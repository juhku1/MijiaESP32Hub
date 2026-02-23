#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "nvs.h"
#include "esp_wifi.h"
#include "esp_event.h"
#include "esp_http_server.h"
#include "esp_http_client.h"
#include "esp_crt_bundle.h"
#include "esp_timer.h"
#include "driver/gpio.h"
#include "driver/uart.h"
#include "lwip/sockets.h"
#include "lwip/inet.h"
#if __has_include("mdns.h")
#include "mdns.h"
#define HAVE_MDNS 1
#else
#define HAVE_MDNS 0
#endif
#include "nimble/nimble_port.h"
#include "nimble/nimble_port_freertos.h"
#include "host/ble_hs.h"
#include "host/ble_gap.h"
#include "services/gap/ble_svc_gap.h"
#include <string.h>
#include "ble_parser.h"
#include "webserver.h"
#include "setup_page.h"
#include <stdint.h>

static const char *TAG = "BLE_SCAN";
static const char *WIFI_TAG = "WiFi";
static const char *AIO_TAG = "AdafruitIO";

#define MAX_DEVICES 50
#define MAX_NAME_LEN 32
#define NVS_NAMESPACE "devices"
#define NVS_WIFI_NAMESPACE "wifi"
#define NVS_AIO_NAMESPACE "aio"

#define BOOT_BUTTON_GPIO 0
#define BOOT_HOLD_TIME_MS 5000
#define AIO_SEND_INTERVAL_MS (5 * 60 * 1000)  // 5 minutes
#define BLE_RATE_INTERVAL_MS 10000
#define DISCOVERY_PORT 19798
#define DISCOVERY_INTERVAL_MS 5000
#define MDNS_HOSTNAME "ble-master"
typedef struct {
    uint8_t addr[6];
    int8_t rssi;
    uint32_t last_seen;
    uint32_t last_sensor_seen; // When the last BLE sensor data was received
    bool visible;  // Is the device visible
    char name[MAX_NAME_LEN];
    char adv_name[MAX_NAME_LEN];  // Advertised name (BLE advertisement)
    bool user_named;  // Has the user set a custom name
    bool show_mac;  // Show MAC address
    bool show_ip;  // Show satellite IP
    uint16_t field_mask;  // Bitmask: which fields to show (temp, hum, bat, batMv, rssi, age)
    bool has_sensor_data;
    float temperature;
    uint8_t humidity;
    uint8_t battery_pct;
    uint16_t battery_mv;
    char firmware_type[16];  // "pvvx", "ATC", "MiBeacon", "BTHome", or "Unknown"
    char source[32];  // "local" or "satellite-192.168.68.129"
} ble_device_t;

// Field mask bits
#define FIELD_TEMP   (1 << 0)
#define FIELD_HUM    (1 << 1)
#define FIELD_BAT    (1 << 2)
#define FIELD_BATMV  (1 << 3)
#define FIELD_RSSI   (1 << 4)
#define FIELD_AGE    (1 << 5)
#define FIELD_ALL    0xFFFF  // All fields by default

static ble_device_t devices[MAX_DEVICES];
static int device_count = 0;
static httpd_handle_t server = NULL;
static bool setup_mode = false;
static char wifi_ssid[64] = {0};
static char wifi_password[64] = {0};
static char ap_password[64] = "temperature";  // Default AP password
static bool wifi_connected = false;
static char master_ip[16] = {0};
#if HAVE_MDNS
static bool mdns_started = false;
#endif
static char aio_username[64] = {0};
static char aio_key[128] = {0};
static bool aio_enabled = false;
static uint8_t aio_feed_types = FIELD_TEMP | FIELD_HUM;  // Default temp + hum
static esp_timer_handle_t aio_timer = NULL;
static char d1_worker_url[256] = {0};
static char d1_token[128] = {0};
static bool d1_enabled = false;
static esp_timer_handle_t ble_rate_timer = NULL;

// BLE packet counters
static uint32_t ble_adv_count = 0;
static uint32_t ble_sensor_count = 0;
static uint32_t sat_adv_count = 0;
static uint32_t sat_sensor_count = 0;

// Scan control
// NOTE: Scanning runs CONTINUOUSLY, but new devices are only added in discovery mode
static bool allow_new_devices = false;  // Allow adding new devices (discovery mode)
static bool master_ble_enabled = true;  // Is local BLE scanning enabled (or satellites only)

// Save device settings to NVS
static void save_device_settings(uint8_t *addr, const char *name, bool show_mac, bool show_ip, uint16_t field_mask, bool user_named) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
        char base_key[20];
        snprintf(base_key, sizeof(base_key), "%02X%02X%02X%02X%02X%02X",
            addr[5], addr[4], addr[3], addr[2], addr[1], addr[0]);
        
        // Save name
        if (name && strlen(name) > 0) {
            char name_key[24];
            snprintf(name_key, sizeof(name_key), "%s_n", base_key);
            nvs_set_str(nvs, name_key, name);
        }

        // Save user_named
        char user_key[24];
        snprintf(user_key, sizeof(user_key), "%s_u", base_key);
        nvs_set_u8(nvs, user_key, user_named ? 1 : 0);
        
        // Save show_mac
        char mac_key[24];
        snprintf(mac_key, sizeof(mac_key), "%s_m", base_key);
        nvs_set_u8(nvs, mac_key, show_mac ? 1 : 0);

        // Save show_ip
        char ip_key[24];
        snprintf(ip_key, sizeof(ip_key), "%s_i", base_key);
        nvs_set_u8(nvs, ip_key, show_ip ? 1 : 0);
        
        // Save field_mask
        char field_key[24];
        snprintf(field_key, sizeof(field_key), "%s_f", base_key);
        nvs_set_u16(nvs, field_key, field_mask);
        
        nvs_commit(nvs);
        nvs_close(nvs);
        ESP_LOGI(TAG, "Saved settings: %s, name=%s, user_named=%d, show_mac=%d, show_ip=%d, fields=0x%04X", 
             base_key, name, user_named ? 1 : 0, show_mac, show_ip, field_mask);
    }
}

// Load device settings from NVS
static void load_device_settings(uint8_t *addr, char *name_out, bool *show_mac_out, bool *show_ip_out, uint16_t *field_mask_out, bool *user_named_out) {
    nvs_handle_t nvs;
    // Defaults
    name_out[0] = '\0';
    *show_mac_out = true;
    *show_ip_out = false;
    *field_mask_out = FIELD_ALL;
    *user_named_out = false;
    
    if (nvs_open(NVS_NAMESPACE, NVS_READONLY, &nvs) == ESP_OK) {
        char base_key[20];
        snprintf(base_key, sizeof(base_key), "%02X%02X%02X%02X%02X%02X",
            addr[5], addr[4], addr[3], addr[2], addr[1], addr[0]);
        
        // Load name
        char name_key[24];
        snprintf(name_key, sizeof(name_key), "%s_n", base_key);
        size_t name_len = MAX_NAME_LEN;
        nvs_get_str(nvs, name_key, name_out, &name_len);

        // Load user_named
        char user_key[24];
        snprintf(user_key, sizeof(user_key), "%s_u", base_key);
        uint8_t user_named_val = 0;
        if (nvs_get_u8(nvs, user_key, &user_named_val) == ESP_OK) {
            *user_named_out = user_named_val ? true : false;
        } else if (name_out[0] != '\0') {
            // Backward compatibility: if a name is stored, assume it's user-provided
            *user_named_out = true;
        }
        
        // Load show_mac
        char mac_key[24];
        snprintf(mac_key, sizeof(mac_key), "%s_m", base_key);
        uint8_t show_mac_val = 1;
        if (nvs_get_u8(nvs, mac_key, &show_mac_val) == ESP_OK) {
            *show_mac_out = show_mac_val ? true : false;
        }

        // Load show_ip
        char ip_key[24];
        snprintf(ip_key, sizeof(ip_key), "%s_i", base_key);
        uint8_t show_ip_val = 0;
        if (nvs_get_u8(nvs, ip_key, &show_ip_val) == ESP_OK) {
            *show_ip_out = show_ip_val ? true : false;
        }
        
        // Load field_mask
        char field_key[24];
        snprintf(field_key, sizeof(field_key), "%s_f", base_key);
        nvs_get_u16(nvs, field_key, field_mask_out);
        
        nvs_close(nvs);
    }
}

// Save device visibility setting to NVS
static void save_visibility(uint8_t *addr, bool visible) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
        char key[20];
        snprintf(key, sizeof(key), "%02X%02X%02X%02X%02X%02X",
            addr[5], addr[4], addr[3], addr[2], addr[1], addr[0]);
        if (visible) {
            uint8_t val = 1;
            ESP_LOGI(TAG, "NVS save visibility: %s -> %d", key, val);
            nvs_set_u8(nvs, key, val);
        } else {
            ESP_LOGI(TAG, "NVS erase visibility: %s", key);
            nvs_erase_key(nvs, key);
        }
        nvs_commit(nvs);
        nvs_close(nvs);
    }
}
static bool load_visibility(uint8_t *addr) {
    nvs_handle_t nvs;
    uint8_t val = 0;  // Default HIDDEN (not yet selected for main view)
    if (nvs_open(NVS_NAMESPACE, NVS_READONLY, &nvs) == ESP_OK) {
        char key[20];
        snprintf(key, sizeof(key), "%02X%02X%02X%02X%02X%02X",
            addr[5], addr[4], addr[3], addr[2], addr[1], addr[0]);
        esp_err_t err = nvs_get_u8(nvs, key, &val);
        if (err == ESP_OK) {
            ESP_LOGI(TAG, "NVS loaded: %s -> visible=%d", key, val);
        } else {
            ESP_LOGI(TAG, "NVS: %s not found (err=%d), default visible=0", key, err);
        }
        nvs_close(nvs);
    }
    return val ? true : false;
}

static int remove_device_by_index(int idx, bool erase_nvs) {
    if (idx < 0 || idx >= device_count) return 0;

    uint8_t *addr = devices[idx].addr;
    char mac_str[13];
    snprintf(mac_str, sizeof(mac_str), "%02X%02X%02X%02X%02X%02X",
             addr[5], addr[4], addr[3], addr[2], addr[1], addr[0]);

    int nvs_removed_count = 0;
    if (erase_nvs) {
        nvs_handle_t nvs;
        if (nvs_open(NVS_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
            if (nvs_erase_key(nvs, mac_str) == ESP_OK) {
                nvs_removed_count++;
            }

            const char* suffixes[] = {"_n", "_m", "_i", "_f", "_u"};
            for (int i = 0; i < 5; i++) {
                char key[24];
                snprintf(key, sizeof(key), "%s%s", mac_str, suffixes[i]);
                if (nvs_erase_key(nvs, key) == ESP_OK) {
                    nvs_removed_count++;
                }
            }

            nvs_commit(nvs);
            nvs_close(nvs);
        }
    }

    for (int i = idx; i < device_count - 1; i++) {
        memcpy(&devices[i], &devices[i + 1], sizeof(ble_device_t));
    }
    device_count--;

    ESP_LOGI(TAG, "🗑️ Removed device from list: %s (nvs_removed=%d)", mac_str, nvs_removed_count);
    return nvs_removed_count;
}

static void prune_hidden_devices(void) {
    for (int i = device_count - 1; i >= 0; i--) {
        if (!devices[i].visible) {
            remove_device_by_index(i, false);
        }
    }
}

// Load all devices stored in NVS at startup
static void load_all_devices_from_nvs(void) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_NAMESPACE, NVS_READONLY, &nvs) != ESP_OK) {
        ESP_LOGI(TAG, "NVS not initialized yet or no devices");
        return;
    }
    
    ESP_LOGI(TAG, "Loading all devices from NVS...");
    
    // Iterate over all NVS keys
    nvs_iterator_t it = NULL;
    esp_err_t res = nvs_entry_find("nvs", NVS_NAMESPACE, NVS_TYPE_ANY, &it);
    
    while (res == ESP_OK && device_count < MAX_DEVICES) {
        nvs_entry_info_t info;
        nvs_entry_info(it, &info);
        
        // Check if this is a visibility key (12 hex chars without _ suffix)
        if (strlen(info.key) == 12) {
            bool is_hex = true;
            for (int i = 0; i < 12; i++) {
                if (!((info.key[i] >= '0' && info.key[i] <= '9') ||
                      (info.key[i] >= 'A' && info.key[i] <= 'F'))) {
                    is_hex = false;
                    break;
                }
            }
            
            if (is_hex) {
                // Parse MAC address
                uint8_t addr[6];
                for (int i = 0; i < 6; i++) {
                    char byte_str[3] = {info.key[i*2], info.key[i*2+1], 0};
                    addr[5-i] = (uint8_t)strtol(byte_str, NULL, 16);
                }

                bool visible = load_visibility(addr);
                if (!visible) {
                    res = nvs_entry_next(&it);
                    continue;
                }
                
                // Add device to list
                memcpy(devices[device_count].addr, addr, 6);
                devices[device_count].visible = visible;
                devices[device_count].rssi = 0;
                devices[device_count].last_seen = 0;
                devices[device_count].last_sensor_seen = 0;
                devices[device_count].has_sensor_data = false;
                devices[device_count].adv_name[0] = '\0';
                
                // Load other settings
                load_device_settings(addr, devices[device_count].name,
                            &devices[device_count].show_mac,
                            &devices[device_count].show_ip,
                            &devices[device_count].field_mask,
                            &devices[device_count].user_named);
                
                ESP_LOGI(TAG, "  Loaded device %d: %02X:%02X:%02X:%02X:%02X:%02X, name=%s",
                        device_count,
                        addr[0], addr[1], addr[2], addr[3], addr[4], addr[5],
                        devices[device_count].name);
                
                device_count++;
            }
        }
        
        res = nvs_entry_next(&it);
    }
    
    nvs_release_iterator(it);
    nvs_close(nvs);
    
    ESP_LOGI(TAG, "Loaded %d devices from NVS", device_count);
}


static int find_or_add_device(uint8_t *addr, bool allow_adding_new) {
    // Check if the device is already in the list
    for (int i = 0; i < device_count; i++) {
        if (memcmp(devices[i].addr, addr, 6) == 0) {
            return i;
        }
    }
    
    // Add a new device only if allowed (discovery mode on)
    if (!allow_adding_new) {
        return -1;  // Do not add new devices in monitoring mode
    }
    
    // Add a new device - default HIDDEN (shown only in discovery popup)
    if (device_count < MAX_DEVICES) {
        memcpy(devices[device_count].addr, addr, 6);
        devices[device_count].visible = false;  // Hidden until user adds to main view
        devices[device_count].rssi = 0;
        devices[device_count].last_seen = 0;
        devices[device_count].last_sensor_seen = 0;
        devices[device_count].has_sensor_data = false;
        devices[device_count].adv_name[0] = '\0';
        strcpy(devices[device_count].source, "local");  // Local device
        
        // Load stored settings (name, show_mac, field_mask)
        load_device_settings(addr, devices[device_count].name, 
               &devices[device_count].show_mac,
               &devices[device_count].show_ip,
               &devices[device_count].field_mask,
               &devices[device_count].user_named);
        
        // Load visibility from NVS (if stored)
        devices[device_count].visible = load_visibility(addr);
        
        ESP_LOGI(TAG, "New device found: %02X:%02X:%02X:%02X:%02X:%02X, name=%s, visible=%d",
                 addr[0], addr[1], addr[2], addr[3], addr[4], addr[5],
                 devices[device_count].name, devices[device_count].visible);
        return device_count++;
    }
    return -1;
}

static int ble_gap_event(struct ble_gap_event *event, void *arg) {
    if (event->type == BLE_GAP_EVENT_DISC) {
        // Check if master BLE is enabled
        if (!master_ble_enabled) {
            return 0;  // Skip local BLE observations
        }
        
        ble_adv_count++;
        // Discovery mode: add new + update all
        // Monitoring mode: update only visible=true devices
        int idx = find_or_add_device(event->disc.addr.val, allow_new_devices);
        
        // LOG: Local BLE observation
        ESP_LOGI(TAG, "📡 LOCAL BLE: %02X:%02X:%02X:%02X:%02X:%02X, RSSI: %d dBm, data_len: %d",
                 event->disc.addr.val[5], event->disc.addr.val[4], event->disc.addr.val[3],
                 event->disc.addr.val[2], event->disc.addr.val[1], event->disc.addr.val[0],
                 event->disc.rssi, event->disc.length_data);
        
        // If the device is not in the list, skip (new devices aren't added in monitoring mode)
        if (idx < 0) {
            return 0;
        }
        
        if (idx >= 0) {
            // Always update RSSI and timestamp
            devices[idx].rssi = event->disc.rssi;
            uint32_t now_ms = xTaskGetTickCount() * portTICK_PERIOD_MS;
            devices[idx].last_seen = now_ms;
            
            // Source = local whenever a local observation arrives
            strcpy(devices[idx].source, "local");
            
            // If the device is hidden and discovery mode is off, don't update adv name/sensor data
            if (!allow_new_devices && !devices[idx].visible) {
                return 0;
            }

            // Parse advertisement data
            struct ble_hs_adv_fields fields;
            if (ble_hs_adv_parse_fields(&fields, event->disc.data, event->disc.length_data) == 0) {
                
                // adv_name updates only if the user hasn't set a custom name
                if (!devices[idx].user_named && fields.name != NULL && fields.name_len > 0) {
                    int copy_len = (fields.name_len < MAX_NAME_LEN - 1) ? fields.name_len : MAX_NAME_LEN - 1;
                    memcpy(devices[idx].adv_name, fields.name, copy_len);
                    devices[idx].adv_name[copy_len] = '\0';
                    // Update name only if empty (user hasn't set a custom one)
                    if (devices[idx].name[0] == '\0') {
                        memcpy(devices[idx].name, fields.name, copy_len);
                        devices[idx].name[copy_len] = '\0';
                        ESP_LOGI(TAG, "BLE name copied: %s", devices[idx].name);
                    }
                } else if (devices[idx].name[0] == '\0') {
                    ESP_LOGI(TAG, "No BLE name in advertisement for this device");
                }
                
                // Sensor data (pvvx/ATC UUID 0x181A or MiBeacon UUID 0xFE95 or BTHome v2 UUID 0xFCD2)
                if (fields.svc_data_uuid16 != NULL && fields.svc_data_uuid16_len >= 13) {
                    uint16_t uuid = fields.svc_data_uuid16[0] | (fields.svc_data_uuid16[1] << 8);
                    
                    if (uuid == 0x181A) {
                        // pvvx or ATC custom firmware
                        ble_sensor_data_t sensor_data;
                        bool parsed = false;
                        
                        if (fields.svc_data_uuid16_len >= 17) {
                            parsed = ble_parse_pvvx_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                        } else if (fields.svc_data_uuid16_len >= 15) {
                            parsed = ble_parse_atc_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                        }
                        
                        if (parsed) {
                            ble_sensor_count++;
                            devices[idx].temperature = sensor_data.temperature;
                            devices[idx].humidity = sensor_data.humidity;
                            devices[idx].battery_pct = sensor_data.battery_pct;
                            devices[idx].battery_mv = sensor_data.battery_mv;
                            strncpy(devices[idx].firmware_type, sensor_data.device_type, sizeof(devices[idx].firmware_type) - 1);
                            devices[idx].firmware_type[sizeof(devices[idx].firmware_type) - 1] = '\0';
                            devices[idx].has_sensor_data = true;
                            devices[idx].last_sensor_seen = now_ms;
                        }
                    } else if (uuid == 0xFE95) {
                        // MiBeacon - Xiaomi original firmware
                        ble_sensor_data_t sensor_data;
                        bool parsed = ble_parse_mibeacon_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                        
                        if (parsed) {
                            ble_sensor_count++;
                            devices[idx].temperature = sensor_data.temperature;
                            devices[idx].humidity = sensor_data.humidity;
                            devices[idx].battery_pct = sensor_data.battery_pct;
                            devices[idx].battery_mv = sensor_data.battery_mv;
                            strncpy(devices[idx].firmware_type, sensor_data.device_type, sizeof(devices[idx].firmware_type) - 1);
                            devices[idx].firmware_type[sizeof(devices[idx].firmware_type) - 1] = '\0';
                            devices[idx].has_sensor_data = true;
                            devices[idx].last_sensor_seen = now_ms;
                        }
                    } else if (uuid == 0xFCD2) {
                        // BTHome v2 - common standard (pvvx supports this)
                        ble_sensor_data_t sensor_data;
                        bool parsed = ble_parse_bthome_v2_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                        
                        if (parsed) {
                            ble_sensor_count++;
                            devices[idx].temperature = sensor_data.temperature;
                            devices[idx].humidity = sensor_data.humidity;
                            devices[idx].battery_pct = sensor_data.battery_pct;
                            devices[idx].battery_mv = sensor_data.battery_mv;
                            strncpy(devices[idx].firmware_type, sensor_data.device_type, sizeof(devices[idx].firmware_type) - 1);
                            devices[idx].firmware_type[sizeof(devices[idx].firmware_type) - 1] = '\0';
                            devices[idx].has_sensor_data = true;
                            devices[idx].last_sensor_seen = now_ms;
                        }
                    }
                }
            }
        }
    }
    return 0;
}

static void ble_rate_timer_callback(void* arg) {
    static uint32_t last_ble_adv = 0;
    static uint32_t last_ble_sensor = 0;
    static uint32_t last_sat_adv = 0;
    static uint32_t last_sat_sensor = 0;

    uint32_t adv = ble_adv_count;
    uint32_t sensor = ble_sensor_count;
    uint32_t sat_adv = sat_adv_count;
    uint32_t sat_sensor = sat_sensor_count;

    uint32_t d_adv = adv - last_ble_adv;
    uint32_t d_sensor = sensor - last_ble_sensor;
    uint32_t d_sat_adv = sat_adv - last_sat_adv;
    uint32_t d_sat_sensor = sat_sensor - last_sat_sensor;

    last_ble_adv = adv;
    last_ble_sensor = sensor;
    last_sat_adv = sat_adv;
    last_sat_sensor = sat_sensor;

    float interval_s = BLE_RATE_INTERVAL_MS / 1000.0f;
    ESP_LOGI(TAG, "BLE rate: adv=%.1f/s sensor=%.1f/s | sat adv=%.1f/s sensor=%.1f/s",
             d_adv / interval_s, d_sensor / interval_s,
             d_sat_adv / interval_s, d_sat_sensor / interval_s);
}

// BLE stack ready, start continuous scan
static void ble_app_on_sync(void) {
    ESP_LOGI(TAG, "BLE stack synchronized and ready");
    ESP_LOGI(TAG, "Starting CONTINUOUS scan to track existing devices");
    
    // Start continuous scan (WiFi-friendly parameters)
    struct ble_gap_disc_params disc_params = {0};
    disc_params.itvl = 0x50;    // 80 * 0.625ms = 50ms interval
    disc_params.window = 0x30;  // 48 * 0.625ms = 30ms window (60% duty cycle)
    disc_params.passive = 0;  // Active scan to get scan response (name)
    
    uint8_t addr_type;
    int rc = ble_hs_id_infer_auto(0, &addr_type);
    if (rc != 0) {
        ESP_LOGE(TAG, "BLE addr_type infer failed: %d", rc);
        return;
    }

    rc = ble_gap_disc(addr_type, BLE_HS_FOREVER, &disc_params, ble_gap_event, NULL);
    
    if (rc != 0) {
        ESP_LOGE(TAG, "Failed to start continuous scan: %d", rc);
    } else {
        ESP_LOGI(TAG, "✓ Continuous scan running (new devices NOT added until /api/scan call)");
    }
}

static void host_task(void *param) {
    nimble_port_run();
}

static void wifi_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_START) {
        ESP_LOGI(WIFI_TAG, "WiFi started, connecting...");
        esp_wifi_connect();
    } else if (event_base == WIFI_EVENT && event_id == WIFI_EVENT_STA_DISCONNECTED) {
        ESP_LOGI(WIFI_TAG, "WiFi disconnected, reconnecting...");
        wifi_connected = false;
        esp_wifi_connect();
    } else if (event_base == IP_EVENT && event_id == IP_EVENT_STA_GOT_IP) {
        ip_event_got_ip_t* event = (ip_event_got_ip_t*) event_data;
        wifi_connected = true;
        snprintf(master_ip, sizeof(master_ip), IPSTR, IP2STR(&event->ip_info.ip));
        ESP_LOGI(WIFI_TAG, "✓ Connected! IP address: " IPSTR, IP2STR(&event->ip_info.ip));
        ESP_LOGI(WIFI_TAG, "Open in browser: http://" IPSTR, IP2STR(&event->ip_info.ip));
        ESP_LOGI(WIFI_TAG, "Discovery broadcast ready (port %d, every 5 s)", DISCOVERY_PORT);
#if HAVE_MDNS
        ESP_LOGI(WIFI_TAG, "mDNS available (HAVE_MDNS=1)");
        if (!mdns_started) {
            esp_err_t err = mdns_init();
            if (err == ESP_OK) {
                mdns_hostname_set(MDNS_HOSTNAME);
                mdns_instance_name_set("BLE Master");
                mdns_txt_item_t txt_data[] = {
                    {"role", "master"},
                    {"path", "/api/satellite-data"},
                };
                mdns_service_add("BLE Master", "_http", "_tcp", 80, txt_data, 2);
                mdns_started = true;
                ESP_LOGI(WIFI_TAG, "✅ mDNS started: http://%s.local", MDNS_HOSTNAME);
                ESP_LOGI(WIFI_TAG, "mDNS service: _http._tcp port 80, txt(role=master, path=/api/satellite-data)");
            } else {
                ESP_LOGW(WIFI_TAG, "❌ mDNS init failed: %s", esp_err_to_name(err));
            }
        }
#else
        ESP_LOGW(WIFI_TAG, "mDNS NOT available (HAVE_MDNS=0), using UDP broadcast only");
#endif
    }
}

static void discovery_broadcast_task(void *param) {
    int sock = socket(AF_INET, SOCK_DGRAM, IPPROTO_IP);
    if (sock < 0) {
        ESP_LOGE(WIFI_TAG, "Discovery socket create failed");
        vTaskDelete(NULL);
        return;
    }

    int broadcast = 1;
    setsockopt(sock, SOL_SOCKET, SO_BROADCAST, &broadcast, sizeof(broadcast));

    struct sockaddr_in dest = {
        .sin_family = AF_INET,
        .sin_port = htons(DISCOVERY_PORT),
        .sin_addr.s_addr = htonl(INADDR_BROADCAST),
    };

    while (1) {
        if (wifi_connected && master_ip[0] != '\0') {
            char msg[64];
            snprintf(msg, sizeof(msg), "SATMASTER %s 80", master_ip);
            int err = sendto(sock, msg, strlen(msg), 0, (struct sockaddr *)&dest, sizeof(dest));
            if (err < 0) {
                ESP_LOGW(WIFI_TAG, "Discovery broadcast failed");
            } else {
                ESP_LOGI(WIFI_TAG, "📡 Discovery broadcast: %s", msg);
            }
        } else {
            ESP_LOGW(WIFI_TAG, "Discovery broadcast skipped (wifi_connected=%d, master_ip='%s')",
                     wifi_connected ? 1 : 0, master_ip);
        }
        vTaskDelay(pdMS_TO_TICKS(DISCOVERY_INTERVAL_MS));
    }
}

// WiFi NVS -funktiot
static bool load_wifi_config(void) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_WIFI_NAMESPACE, NVS_READONLY, &nvs) != ESP_OK) {
        ESP_LOGW(WIFI_TAG, "WiFi settings not found in NVS");
        return false;
    }
    
    size_t ssid_len = sizeof(wifi_ssid);
    size_t pass_len = sizeof(wifi_password);
    
    esp_err_t err_ssid = nvs_get_str(nvs, "ssid", wifi_ssid, &ssid_len);
    esp_err_t err_pass = nvs_get_str(nvs, "password", wifi_password, &pass_len);
    
    nvs_close(nvs);
    
    if (err_ssid == ESP_OK && err_pass == ESP_OK && strlen(wifi_ssid) > 0) {
        ESP_LOGI(WIFI_TAG, "WiFi-asetukset ladattu: %s", wifi_ssid);
        return true;
    }
    
    return false;
}

static void load_ap_password(void) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_WIFI_NAMESPACE, NVS_READONLY, &nvs) != ESP_OK) {
        ESP_LOGI(WIFI_TAG, "AP password not set, using default: temperature");
        strcpy(ap_password, "temperature");
        return;
    }
    
    size_t pass_len = sizeof(ap_password);
    esp_err_t err = nvs_get_str(nvs, "ap_password", ap_password, &pass_len);
    nvs_close(nvs);
    
    if (err != ESP_OK || strlen(ap_password) < 8) {
        ESP_LOGI(WIFI_TAG, "AP password invalid or too short, using default");
        strcpy(ap_password, "temperature");
    } else {
        ESP_LOGI(WIFI_TAG, "AP password loaded from NVS");
    }
}

static void save_ap_password(const char* password) {
    if (strlen(password) < 8 || strlen(password) > 63) {
        ESP_LOGE(WIFI_TAG, "AP password must be 8-63 characters");
        return;
    }
    
    nvs_handle_t nvs;
    if (nvs_open(NVS_WIFI_NAMESPACE, NVS_READWRITE, &nvs) != ESP_OK) {
        ESP_LOGE(WIFI_TAG, "Failed to open NVS for AP password");
        return;
    }
    
    nvs_set_str(nvs, "ap_password", password);
    nvs_commit(nvs);
    nvs_close(nvs);
    
    strcpy(ap_password, password);
    ESP_LOGI(WIFI_TAG, "AP password saved");
}

static void save_wifi_config(const char* ssid, const char* password) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_WIFI_NAMESPACE, NVS_READWRITE, &nvs) != ESP_OK) {
        ESP_LOGE(WIFI_TAG, "Failed to open NVS");
        return;
    }
    
    nvs_set_str(nvs, "ssid", ssid);
    nvs_set_str(nvs, "password", password);
    nvs_commit(nvs);
    nvs_close(nvs);
    
    ESP_LOGI(WIFI_TAG, "WiFi-asetukset tallennettu");
}

static void clear_wifi_config(void) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_WIFI_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
        nvs_erase_all(nvs);
        nvs_commit(nvs);
        nvs_close(nvs);
        ESP_LOGI(WIFI_TAG, "WiFi-asetukset nollattu");
    }
}

static void check_boot_button(void) {
    gpio_config_t io_conf = {
        .pin_bit_mask = (1ULL << BOOT_BUTTON_GPIO),
        .mode = GPIO_MODE_INPUT,
        .pull_up_en = GPIO_PULLUP_ENABLE,
        .pull_down_en = GPIO_PULLDOWN_DISABLE,
        .intr_type = GPIO_INTR_DISABLE
    };
    gpio_config(&io_conf);
    
    if (gpio_get_level(BOOT_BUTTON_GPIO) == 0) {
        ESP_LOGI(WIFI_TAG, "BOOT-nappi pohjassa, tarkistetaan...");
        vTaskDelay(pdMS_TO_TICKS(100));
        
        uint32_t start = esp_timer_get_time() / 1000;
        while (gpio_get_level(BOOT_BUTTON_GPIO) == 0) {
            uint32_t elapsed = (esp_timer_get_time() / 1000) - start;
            if (elapsed >= BOOT_HOLD_TIME_MS) {
                ESP_LOGW(WIFI_TAG, "🔄 BOOT-nappi pidetty 5s - Nollataan WiFi!");
                clear_wifi_config();
                vTaskDelay(pdMS_TO_TICKS(500));
                esp_restart();
            }
            vTaskDelay(pdMS_TO_TICKS(100));
        }
        ESP_LOGI(WIFI_TAG, "BOOT-nappi vapautettu liian aikaisin");
    }
}

// Adafruit IO NVS -funktiot
static bool load_aio_config(void) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_AIO_NAMESPACE, NVS_READONLY, &nvs) != ESP_OK) {
        ESP_LOGW(AIO_TAG, "Adafruit IO settings not found");
        return false;
    }
    
    size_t user_len = sizeof(aio_username);
    size_t key_len = sizeof(aio_key);
    uint8_t enabled = 0;
    
    esp_err_t err_user = nvs_get_str(nvs, "username", aio_username, &user_len);
    esp_err_t err_key = nvs_get_str(nvs, "key", aio_key, &key_len);
    nvs_get_u8(nvs, "enabled", &enabled);
    nvs_get_u8(nvs, "feed_types", &aio_feed_types);
    
    nvs_close(nvs);
    
    if (err_user == ESP_OK && err_key == ESP_OK && strlen(aio_username) > 0 && strlen(aio_key) > 0) {
        aio_enabled = (enabled != 0);
        if (aio_feed_types == 0) aio_feed_types = FIELD_TEMP | FIELD_HUM;  // Oletusarvo
        ESP_LOGI(AIO_TAG, "Asetukset ladattu: %s, enabled=%d, types=0x%02x", aio_username, aio_enabled, aio_feed_types);
        return true;
    }
    
    return false;
}

static void save_aio_config(const char* username, const char* key, bool enabled, uint8_t feed_types) {
    nvs_handle_t nvs;
    if (nvs_open(NVS_AIO_NAMESPACE, NVS_READWRITE, &nvs) != ESP_OK) {
        ESP_LOGE(AIO_TAG, "Failed to open NVS");
        return;
    }
    
    nvs_set_str(nvs, "username", username);
    nvs_set_str(nvs, "key", key);
    nvs_set_u8(nvs, "enabled", enabled ? 1 : 0);
    nvs_set_u8(nvs, "feed_types", feed_types);
    nvs_commit(nvs);
    nvs_close(nvs);
    
    strncpy(aio_username, username, sizeof(aio_username) - 1);
    strncpy(aio_key, key, sizeof(aio_key) - 1);
    aio_enabled = enabled;
    aio_feed_types = feed_types;
    
    ESP_LOGI(AIO_TAG, "Settings saved, types=0x%02x", feed_types);
}

// Load D1 config from NVS
static bool load_d1_config(void) {
    nvs_handle_t nvs;
    if (nvs_open("d1_config", NVS_READONLY, &nvs) != ESP_OK) {
        return false;
    }
    
    size_t url_len = sizeof(d1_worker_url);
    size_t token_len = sizeof(d1_token);
    uint8_t enabled_val = 0;
    
    esp_err_t err1 = nvs_get_str(nvs, "worker_url", d1_worker_url, &url_len);
    esp_err_t err2 = nvs_get_str(nvs, "token", d1_token, &token_len);
    nvs_get_u8(nvs, "enabled", &enabled_val);
    
    nvs_close(nvs);
    
    d1_enabled = (enabled_val == 1);
    
    return (err1 == ESP_OK && err2 == ESP_OK);
}

// Save D1 config to NVS
static void save_d1_config(const char* worker_url, const char* token, bool enabled) {
    nvs_handle_t nvs;
    if (nvs_open("d1_config", NVS_READWRITE, &nvs) != ESP_OK) {
        ESP_LOGE(TAG, "Failed to open NVS for D1");
        return;
    }
    
    nvs_set_str(nvs, "worker_url", worker_url);
    nvs_set_str(nvs, "token", token);
    nvs_set_u8(nvs, "enabled", enabled ? 1 : 0);
    nvs_commit(nvs);
    nvs_close(nvs);
    
    strncpy(d1_worker_url, worker_url, sizeof(d1_worker_url) - 1);
    strncpy(d1_token, token, sizeof(d1_token) - 1);
    d1_enabled = enabled;
    
    ESP_LOGI(TAG, "D1 settings saved: %s, enabled=%d", worker_url, enabled);
}

static void wifi_init(void) {
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));
    
    esp_event_handler_instance_t instance_any_id;
    esp_event_handler_instance_t instance_got_ip;
    ESP_ERROR_CHECK(esp_event_handler_instance_register(WIFI_EVENT, ESP_EVENT_ANY_ID, &wifi_event_handler, NULL, &instance_any_id));
    ESP_ERROR_CHECK(esp_event_handler_instance_register(IP_EVENT, IP_EVENT_STA_GOT_IP, &wifi_event_handler, NULL, &instance_got_ip));
    
    // Always create both STA and AP interfaces
    esp_netif_create_default_wifi_sta();
    esp_netif_create_default_wifi_ap();
    
    // Load AP password from NVS
    load_ap_password();
    
    // AP configuration (always enabled)
    wifi_config_t ap_config = {
        .ap = {
            .ssid = "BLE-Monitor",
            .ssid_len = strlen("BLE-Monitor"),
            .channel = 1,
            .password = "",
            .max_connection = 4,
            .authmode = WIFI_AUTH_WPA2_PSK,
        },
    };
    strncpy((char*)ap_config.ap.password, ap_password, sizeof(ap_config.ap.password));
    
    // Check if WiFi is configured
    if (!load_wifi_config()) {
        // No WiFi settings -> AP only mode
        ESP_LOGI(WIFI_TAG, "🔧 Setup mode: AP only (no WiFi configured)");
        setup_mode = true;
        
        ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_APSTA));
        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &ap_config));
        ESP_ERROR_CHECK(esp_wifi_start());
        
        ESP_LOGI(WIFI_TAG, "✓ AP started: BLE-Monitor");
        ESP_LOGI(WIFI_TAG, "📱 Connect to: BLE-Monitor");
        ESP_LOGI(WIFI_TAG, "🌐 Open browser: http://192.168.4.1");
    } else {
        // WiFi configured -> STA+AP mode (both enabled)
        ESP_LOGI(WIFI_TAG, "🌐 Dual mode: Station + AP");
        ESP_LOGI(WIFI_TAG, "Connecting to network: %s", wifi_ssid);
        setup_mode = false;
        
        // STA configuration
        wifi_config_t sta_config = {0};
        strncpy((char*)sta_config.sta.ssid, wifi_ssid, sizeof(sta_config.sta.ssid));
        strncpy((char*)sta_config.sta.password, wifi_password, sizeof(sta_config.sta.password));
        
        ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_APSTA));
        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_STA, &sta_config));
        ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &ap_config));
        ESP_ERROR_CHECK(esp_wifi_start());
        
        ESP_LOGI(WIFI_TAG, "✓ AP always on: BLE-Monitor");
        ESP_LOGI(WIFI_TAG, "📱 Local access: http://192.168.4.1");
    }
}

// ============================================
// ADAFRUIT IO DATA UPLOAD
// ============================================

// Send device data to Cloudflare D1
static void send_device_to_d1(const ble_device_t *dev) {
    if (!d1_enabled || !dev->has_sensor_data) return;
    
    // Build JSON payload with all device data
    char *payload = malloc(1024);
    if (!payload) {
        ESP_LOGE(TAG, "Failed to allocate memory for D1 payload");
        return;
    }
    
    char mac_str[18];
    snprintf(mac_str, sizeof(mac_str), "%02X:%02X:%02X:%02X:%02X:%02X",
             dev->addr[0], dev->addr[1], dev->addr[2], 
             dev->addr[3], dev->addr[4], dev->addr[5]);
    
    int len = snprintf(payload, 1024, 
        "{\"mac\":\"%s\",\"name\":\"%s\",\"data\":{",
        mac_str,
        dev->name[0] ? dev->name : "Unknown");
    
    bool first = true;
    if (dev->field_mask & FIELD_TEMP) {
        len += snprintf(payload + len, 1024 - len, "%s\"temperature\":%.2f", first ? "" : ",", dev->temperature);
        first = false;
    }
    if (dev->field_mask & FIELD_HUM) {
        len += snprintf(payload + len, 1024 - len, "%s\"humidity\":%d", first ? "" : ",", dev->humidity);
        first = false;
    }
    if (dev->field_mask & FIELD_BAT) {
        len += snprintf(payload + len, 1024 - len, "%s\"battery_mv\":%d", first ? "" : ",", dev->battery_mv);
        first = false;
    }
    if (dev->field_mask & FIELD_RSSI) {
        len += snprintf(payload + len, 1024 - len, "%s\"rssi\":%d", first ? "" : ",", dev->rssi);
    }
    
    snprintf(payload + len, 1024 - len, "}}");
    
    // Send to D1 worker
    char url[300];
    snprintf(url, sizeof(url), "%s/data", d1_worker_url);
    
    esp_http_client_config_t config = {
        .url = url,
        .method = HTTP_METHOD_POST,
        .crt_bundle_attach = esp_crt_bundle_attach,
        .timeout_ms = 10000,
    };
    esp_http_client_handle_t client = esp_http_client_init(&config);
    esp_http_client_set_header(client, "Content-Type", "application/json");
    esp_http_client_set_header(client, "Authorization", d1_token);
    esp_http_client_set_post_field(client, payload, strlen(payload));
    
    esp_err_t err = esp_http_client_perform(client);
    int status = esp_http_client_get_status_code(client);
    
    if (err == ESP_OK && status == 200) {
        ESP_LOGI(TAG, "D1: Sent data for %s", dev->name[0] ? dev->name : mac_str);
    } else {
        ESP_LOGW(TAG, "D1: Failed to send %s (HTTP %d)", dev->name[0] ? dev->name : mac_str, status);
    }
    
    esp_http_client_cleanup(client);
    free(payload);
}

static void send_device_to_aio(const ble_device_t *dev) {
    if (!aio_enabled || !dev->has_sensor_data) return;
    
    char url[256];
    char payload[256];
    
    // Feed key: MAC only (never changes even if device renamed)
    char feed_key[20];
    snprintf(feed_key, sizeof(feed_key), "%02x%02x%02x%02x%02x%02x",
             dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
    
    // Send temperature
        if ((dev->field_mask & FIELD_TEMP) && (aio_feed_types & FIELD_TEMP)) {
        char feed_name[80];
        snprintf(feed_name, sizeof(feed_name), "%s-temp", feed_key);
        ESP_LOGI(AIO_TAG, "📤 Sending to feed: %s (URL: /api/v2/%s/feeds/%s/data)", feed_name, aio_username, feed_name);
        snprintf(url, sizeof(url), "https://io.adafruit.com/api/v2/%s/feeds/%s/data", aio_username, feed_name);
        
        // Add metadata: device name and MAC
        if (strlen(dev->name) > 0) {
            snprintf(payload, sizeof(payload), "{\"value\":\"%.2f\",\"feed_key\":\"%s\",\"metadata\":\"%s (%02X:%02X:%02X:%02X:%02X:%02X)\"}",
                     dev->temperature, feed_name, dev->name,
                     dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
        } else {
            snprintf(payload, sizeof(payload), "{\"value\":\"%.2f\",\"feed_key\":\"%s\",\"metadata\":\"MAC: %02X:%02X:%02X:%02X:%02X:%02X\"}",
                     dev->temperature, feed_name,
                     dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
        }
        
        esp_http_client_config_t config = {
            .url = url,
            .method = HTTP_METHOD_POST,
            .crt_bundle_attach = esp_crt_bundle_attach,
        };
        esp_http_client_handle_t client = esp_http_client_init(&config);
        
        esp_http_client_set_header(client, "Content-Type", "application/json");
        esp_http_client_set_header(client, "X-AIO-Key", aio_key);
        esp_http_client_set_post_field(client, payload, strlen(payload));
        
        esp_err_t err = esp_http_client_perform(client);
        int status = esp_http_client_get_status_code(client);
        if (err == ESP_OK && status == 200) {
            ESP_LOGI(AIO_TAG, "Temp sent: %s = %.2f", feed_key, dev->temperature);
        } else {
            ESP_LOGE(AIO_TAG, "Temp failed: %s, HTTP %d", esp_err_to_name(err), status);
        }
        esp_http_client_cleanup(client);
        vTaskDelay(pdMS_TO_TICKS(100)); // Small delay between requests
    }
    
    // Send humidity
    if ((dev->field_mask & FIELD_HUM) && (aio_feed_types & FIELD_HUM)) {
        snprintf(url, sizeof(url), "https://io.adafruit.com/api/v2/%s/feeds/%s-hum/data", aio_username, feed_key);
        
        if (strlen(dev->name) > 0) {
            snprintf(payload, sizeof(payload), "{\"value\":\"%d\",\"metadata\":\"%s (%02X:%02X:%02X:%02X:%02X:%02X)\"}",
                     dev->humidity, dev->name,
                     dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
        } else {
            snprintf(payload, sizeof(payload), "{\"value\":\"%d\",\"metadata\":\"MAC: %02X:%02X:%02X:%02X:%02X:%02X\"}",
                     dev->humidity,
                     dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
        }
        
        esp_http_client_config_t config = {
            .url = url,
            .method = HTTP_METHOD_POST,
            .crt_bundle_attach = esp_crt_bundle_attach,
        };
        esp_http_client_handle_t client = esp_http_client_init(&config);
        
        esp_http_client_set_header(client, "Content-Type", "application/json");
        esp_http_client_set_header(client, "X-AIO-Key", aio_key);
        esp_http_client_set_post_field(client, payload, strlen(payload));
        
        esp_err_t err = esp_http_client_perform(client);
        int status = esp_http_client_get_status_code(client);
        if (err == ESP_OK && status == 200) {
            ESP_LOGI(AIO_TAG, "Hum sent: %s = %d", feed_key, dev->humidity);
        } else {
            ESP_LOGE(AIO_TAG, "Hum failed: %s, HTTP %d", esp_err_to_name(err), status);
        }
        esp_http_client_cleanup(client);
        vTaskDelay(pdMS_TO_TICKS(100));
    }
    
    // Send battery level
    if ((dev->field_mask & FIELD_BAT) && (aio_feed_types & FIELD_BAT)) {
        snprintf(url, sizeof(url), "https://io.adafruit.com/api/v2/%s/feeds/%s-bat/data", aio_username, feed_key);
        
        if (strlen(dev->name) > 0) {
            snprintf(payload, sizeof(payload), "{\"value\":\"%d\",\"metadata\":\"%s (%02X:%02X:%02X:%02X:%02X:%02X)\"}",
                     dev->battery_pct, dev->name,
                     dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
        } else {
            snprintf(payload, sizeof(payload), "{\"value\":\"%d\",\"metadata\":\"MAC: %02X:%02X:%02X:%02X:%02X:%02X\"}",
                     dev->battery_pct,
                     dev->addr[0], dev->addr[1], dev->addr[2], dev->addr[3], dev->addr[4], dev->addr[5]);
        }
        
        esp_http_client_config_t config = {
            .url = url,
            .method = HTTP_METHOD_POST,
            .crt_bundle_attach = esp_crt_bundle_attach,
        };
        esp_http_client_handle_t client = esp_http_client_init(&config);
        
        esp_http_client_set_header(client, "Content-Type", "application/json");
        esp_http_client_set_header(client, "X-AIO-Key", aio_key);
        esp_http_client_set_post_field(client, payload, strlen(payload));
        
        esp_err_t err = esp_http_client_perform(client);
        if (err == ESP_OK) {
            ESP_LOGI(AIO_TAG, "Bat sent: %s = %d", feed_key, dev->battery_pct);
        }
        esp_http_client_cleanup(client);
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}

static void aio_upload_task(void *arg) {
    ESP_LOGI(AIO_TAG, "Starting data upload... (total devices: %d)", device_count);
    
    int sent_count = 0;
    int visible_count = 0;
    int has_data_count = 0;
    
    for (int i = 0; i < device_count; i++) {
        if (devices[i].visible) visible_count++;
        if (devices[i].has_sensor_data) has_data_count++;
        
        if (devices[i].visible && devices[i].has_sensor_data) {
            ESP_LOGI(AIO_TAG, "Sending device %d: %s", i, devices[i].name);
            if (aio_enabled) {
                send_device_to_aio(&devices[i]);
            }
            if (d1_enabled) {
                send_device_to_d1(&devices[i]);
            }
            sent_count++;
        }
    }
    
    ESP_LOGI(TAG, "Upload complete: sent=%d, visible=%d, has_data=%d (AIO:%s, D1:%s)", 
             sent_count, visible_count, has_data_count,
             aio_enabled ? "✓" : "✗", 
             d1_enabled ? "✓" : "✗");
    vTaskDelete(NULL);
}

static void aio_timer_callback(void* arg) {
    if (!aio_enabled) return;
    
    // Create a task that sends data (doesn't block the timer)
    xTaskCreate(aio_upload_task, "aio_upload", 8192, NULL, 5, NULL);
}

static void sanitize_json_string(const char* src, char* dst, size_t dst_size) {
    if (!src || !dst || dst_size == 0) return;
    size_t j = 0;
    for (size_t i = 0; src[i] != '\0' && j + 1 < dst_size; i++) {
        char c = src[i];
        if (c == '"') {
            c = '\'';
        } else if ((unsigned char)c < 32) {
            continue;
        }
        dst[j++] = c;
    }
    dst[j] = '\0';
}

static bool aio_update_feed_name(const char* feed_key_full, const char* full_name) {
    if (!feed_key_full || !full_name || strlen(aio_username) == 0 || strlen(aio_key) == 0) return false;

    char url[256];
    char payload[256];
    snprintf(url, sizeof(url), "https://io.adafruit.com/api/v2/%s/feeds/%s", aio_username, feed_key_full);
    snprintf(payload, sizeof(payload), "{\"feed\":{\"name\":\"%s\"}}", full_name);

    esp_http_client_config_t config = {
        .url = url,
        .method = HTTP_METHOD_PUT,
        .crt_bundle_attach = esp_crt_bundle_attach,
        .timeout_ms = 10000,
    };
    esp_http_client_handle_t client = esp_http_client_init(&config);
    esp_http_client_set_header(client, "Content-Type", "application/json");
    esp_http_client_set_header(client, "X-AIO-Key", aio_key);
    esp_http_client_set_post_field(client, payload, strlen(payload));

    esp_err_t err = esp_http_client_perform(client);
    int status = esp_http_client_get_status_code(client);
    esp_http_client_cleanup(client);

    if (err == ESP_OK && (status == 200 || status == 201)) {
        ESP_LOGI(AIO_TAG, "↻ Updated feed name: %s", feed_key_full);
        return true;
    }

    ESP_LOGW(AIO_TAG, "✗ Failed to update feed name %s (status: %d)", feed_key_full, status);
    return false;
}

static esp_err_t api_aio_create_feeds_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    if (strlen(aio_username) == 0 || strlen(aio_key) == 0) {
        const char* resp = "{\"ok\":false,\"error\":\"Adafruit IO not configured\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Create feeds synchronously and return results
    int created = 0;
    int existed = 0;
    int failed = 0;
    
    for (int i = 0; i < device_count; i++) {
        if (!devices[i].visible || !devices[i].has_sensor_data) continue;
        
        char feed_key[20];
        snprintf(feed_key, sizeof(feed_key), "%02x%02x%02x%02x%02x%02x",
                 devices[i].addr[0], devices[i].addr[1], devices[i].addr[2], 
                 devices[i].addr[3], devices[i].addr[4], devices[i].addr[5]);
        
        // Try each feed type
        const char* suffixes[3] = {"-temp", "-hum", "-bat"};
        const char* names[3] = {"Temperature", "Humidity", "Battery"};
        uint8_t type_bits[3] = {FIELD_TEMP, FIELD_HUM, FIELD_BAT};
        
        for (int t = 0; t < 3; t++) {
            if (!(devices[i].field_mask & type_bits[t]) || !(aio_feed_types & type_bits[t])) continue;
            
            char url[256];
            char payload[256];
            char display_name[64];
            char full_name[96];
            char feed_key_full[32];
            const char* raw_name = (strlen(devices[i].name) > 0) ? devices[i].name : feed_key;
            sanitize_json_string(raw_name, display_name, sizeof(display_name));
            snprintf(full_name, sizeof(full_name), "%s %s", display_name, names[t]);
            snprintf(feed_key_full, sizeof(feed_key_full), "%s%s", feed_key, suffixes[t]);
            snprintf(url, sizeof(url), "https://io.adafruit.com/api/v2/%s/feeds", aio_username);
            snprintf(payload, sizeof(payload), "{\"key\":\"%s%s\",\"name\":\"%s %s\"}", 
                     feed_key, suffixes[t], display_name, names[t]);
            
            esp_http_client_config_t config = {
                .url = url,
                .method = HTTP_METHOD_POST,
                .crt_bundle_attach = esp_crt_bundle_attach,
                .timeout_ms = 10000,
            };
            esp_http_client_handle_t client = esp_http_client_init(&config);
            esp_http_client_set_header(client, "Content-Type", "application/json");
            esp_http_client_set_header(client, "X-AIO-Key", aio_key);
            esp_http_client_set_post_field(client, payload, strlen(payload));
            
            esp_err_t err = esp_http_client_perform(client);
            int status = esp_http_client_get_status_code(client);
            esp_http_client_cleanup(client);
            
            if (err == ESP_OK) {
                if (status == 200 || status == 201) {
                    created++;
                    ESP_LOGI(AIO_TAG, "✓ Created feed: %s%s", feed_key, suffixes[t]);
                } else if (status == 422 || status == 409 || status == 400) {
                    // 422 = Unprocessable Entity (already exists)
                    // 409 = Conflict (already exists)
                    // 400 = Bad Request (often means already exists in Adafruit IO)
                    existed++;
                    ESP_LOGI(AIO_TAG, "○ Feed already exists: %s%s (status: %d)", feed_key, suffixes[t], status);
                    if (strlen(devices[i].name) > 0) {
                        aio_update_feed_name(feed_key_full, full_name);
                    }
                } else {
                    failed++;
                    ESP_LOGW(AIO_TAG, "✗ Failed to create feed %s%s (status: %d)", feed_key, suffixes[t], status);
                }
            } else {
                failed++;
                ESP_LOGE(AIO_TAG, "✗ HTTP error creating %s%s: %s", feed_key, suffixes[t], esp_err_to_name(err));
            }
            vTaskDelay(pdMS_TO_TICKS(300));
        }
    }
    
    ESP_LOGI(AIO_TAG, "Feed creation completed: %d created, %d existed, %d failed", created, existed, failed);
    
    char response[256];
    snprintf(response, sizeof(response), 
             "{\"ok\":true,\"created\":%d,\"existed\":%d,\"failed\":%d}", 
             created, existed, failed);
    httpd_resp_send(req, response, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Delete feeds by type (temp/hum/bat)
static esp_err_t api_aio_delete_feeds_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    if (strlen(aio_username) == 0 || strlen(aio_key) == 0) {
        const char* resp = "{\"ok\":false,\"error\":\"Adafruit IO not configured\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Get types parameter from query string
    char query[64];
    uint8_t types_to_delete = 0;
    if (httpd_req_get_url_query_str(req, query, sizeof(query)) == ESP_OK) {
        char types_param[8];
        if (httpd_query_key_value(query, "types", types_param, sizeof(types_param)) == ESP_OK) {
            types_to_delete = (uint8_t)atoi(types_param);
        }
    }
    
    if (types_to_delete == 0) {
        const char* resp = "{\"ok\":false,\"error\":\"No types to delete\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    int deleted = 0;
    const char* suffixes[3] = {"-temp", "-hum", "-bat"};
    uint8_t type_bits[3] = {FIELD_TEMP, FIELD_HUM, FIELD_BAT};
    
    // Iterate over each type to delete
    for (int t = 0; t < 3; t++) {
        if (!(types_to_delete & type_bits[t])) continue;
        
        // Iterate over all visible devices
        for (int i = 0; i < device_count; i++) {
            if (!devices[i].visible) continue;
            
            // Generate feed key (MAC only)
            char feed_key[24];
            snprintf(feed_key, sizeof(feed_key), "%02x%02x%02x%02x%02x%02x%s",
                     devices[i].addr[0], devices[i].addr[1], devices[i].addr[2], 
                     devices[i].addr[3], devices[i].addr[4], devices[i].addr[5],
                     suffixes[t]);
            
            // Delete feed
            char url[256];
            snprintf(url, sizeof(url), "https://io.adafruit.com/api/v2/%s/feeds/%s", aio_username, feed_key);
            
            esp_http_client_config_t config = {
                .url = url,
                .method = HTTP_METHOD_DELETE,
                .crt_bundle_attach = esp_crt_bundle_attach,
            };
            esp_http_client_handle_t client = esp_http_client_init(&config);
            esp_http_client_set_header(client, "X-AIO-Key", aio_key);
            
            esp_err_t err = esp_http_client_perform(client);
            int status = esp_http_client_get_status_code(client);
            esp_http_client_cleanup(client);
            
            if (err == ESP_OK && (status == 200 || status == 204)) {
                deleted++;
                ESP_LOGI(AIO_TAG, "Feed deleted: %s", feed_key);
            }
            vTaskDelay(pdMS_TO_TICKS(150));
        }
    }
    
    char response[128];
    snprintf(response, sizeof(response), "{\"ok\":true,\"deleted\":%d}", deleted);
    httpd_resp_send(req, response, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Send data now (test)
static esp_err_t api_aio_send_now_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    if (!aio_enabled || strlen(aio_username) == 0 || strlen(aio_key) == 0) {
        const char* resp = "{\"ok\":false,\"error\":\"Adafruit IO not enabled\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Create a task that sends data
    xTaskCreate(aio_upload_task, "aio_upload", 8192, NULL, 5, NULL);
    
    const char* resp = "{\"ok\":true,\"message\":\"Send started\"}";
    httpd_resp_sendstr(req, resp);
    return ESP_OK;
}

// ============================================
// WEB UI
// ============================================

static esp_err_t root_get_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Cache-Control", "no-store, no-cache, must-revalidate, max-age=0");
    httpd_resp_set_hdr(req, "Pragma", "no-cache");
    httpd_resp_set_hdr(req, "Expires", "0");
    
    // Check if request came from AP interface (192.168.4.x)
    int sockfd = httpd_req_to_sockfd(req);
    struct sockaddr_in6 addr;
    socklen_t addr_size = sizeof(addr);
    
    if (getpeername(sockfd, (struct sockaddr *)&addr, &addr_size) == 0) {
        if (addr.sin6_family == AF_INET6) {
            // Check for IPv4-mapped IPv6 address
            if (IN6_IS_ADDR_V4MAPPED(&addr.sin6_addr)) {
                uint32_t ipv4 = ((uint32_t *)&addr.sin6_addr)[3];
                uint8_t *ip_bytes = (uint8_t *)&ipv4;
                // Check if IP is 192.168.4.x (AP network)
                if (ip_bytes[0] == 192 && ip_bytes[1] == 168 && ip_bytes[2] == 4) {
                    // Request from AP -> show setup page
                    httpd_resp_send(req, SETUP_HTML_PAGE, HTTPD_RESP_USE_STRLEN);
                    return ESP_OK;
                }
            }
        } else if (addr.sin6_family == AF_INET) {
            struct sockaddr_in *addr_in = (struct sockaddr_in *)&addr;
            uint8_t *ip_bytes = (uint8_t *)&addr_in->sin_addr.s_addr;
            // Check if IP is 192.168.4.x (AP network)
            if (ip_bytes[0] == 192 && ip_bytes[1] == 168 && ip_bytes[2] == 4) {
                // Request from AP -> show setup page
                httpd_resp_send(req, SETUP_HTML_PAGE, HTTPD_RESP_USE_STRLEN);
                return ESP_OK;
            }
        }
    }
    
    // Request from STA or unknown -> show full UI
    httpd_resp_send(req, HTML_PAGE, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Setup WiFi-asetukset
static esp_err_t api_setup_handler(httpd_req_t *req) {
    char buf[256];
    int ret = httpd_req_recv(req, buf, sizeof(buf) - 1);
    if (ret <= 0) {
        httpd_resp_send_500(req);
        return ESP_FAIL;
    }
    buf[ret] = '\0';
    
    // Parseroidaan JSON (yksinkertainen toteutus)
    char *ssid_start = strstr(buf, "\"ssid\":\"");
    char *pass_start = strstr(buf, "\"password\":\"");
    
    if (!ssid_start || !pass_start) {
        const char* resp = "{\"ok\":false,\"error\":\"Invalid JSON\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    ssid_start += 8;  // Skip "ssid":"
    pass_start += 12; // Skip "password":"
    
    char ssid[64] = {0};
    char password[64] = {0};
    
    char *ssid_end = strchr(ssid_start, '"');
    char *pass_end = strchr(pass_start, '"');
    
    if (ssid_end && pass_end) {
        int ssid_len = ssid_end - ssid_start;
        int pass_len = pass_end - pass_start;
        
        if (ssid_len > 0 && ssid_len < 64) {
            strncpy(ssid, ssid_start, ssid_len);
        }
        if (pass_len >= 0 && pass_len < 64) {
            strncpy(password, pass_start, pass_len);
        }
        
        // Save WiFi config
        save_wifi_config(ssid, password);
        
        const char* resp = "{\"ok\":true}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        
        // Update WiFi configuration without restart
        ESP_LOGI(WIFI_TAG, "WiFi configured, reconnecting to: %s", ssid);
        
        wifi_config_t sta_config = {0};
        strncpy((char*)sta_config.sta.ssid, ssid, sizeof(sta_config.sta.ssid));
        strncpy((char*)sta_config.sta.password, password, sizeof(sta_config.sta.password));
        
        // Update STA config and reconnect
        esp_wifi_set_config(WIFI_IF_STA, &sta_config);
        esp_wifi_disconnect();
        vTaskDelay(pdMS_TO_TICKS(100));
        esp_wifi_connect();
        
        setup_mode = false;
        
        return ESP_OK;
    }
    
    const char* resp = "{\"ok\":false,\"error\":\"Parse error\"}";
    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Get WiFi status (for setup page)
static esp_err_t api_status_handler(httpd_req_t *req) {
    char resp[128];
    if (wifi_connected && master_ip[0] != '\0') {
        snprintf(resp, sizeof(resp), "{\"connected\":true,\"ip\":\"%s\"}", master_ip);
    } else {
        snprintf(resp, sizeof(resp), "{\"connected\":false,\"ip\":\"\"}");
    }
    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Set AP password
static esp_err_t api_ap_password_handler(httpd_req_t *req) {
    char buf[128];
    int ret = httpd_req_recv(req, buf, sizeof(buf) - 1);
    if (ret <= 0) {
        httpd_resp_send_500(req);
        return ESP_FAIL;
    }
    buf[ret] = '\0';
    
    char *pass_start = strstr(buf, "\"password\":\"");
    if (!pass_start) {
        const char* resp = "{\"ok\":false,\"error\":\"Invalid JSON\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    pass_start += 12;  // Skip "password":"
    char *pass_end = strchr(pass_start, '"');
    if (!pass_end) {
        const char* resp = "{\"ok\":false,\"error\":\"Parse error\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    int pass_len = pass_end - pass_start;
    if (pass_len < 8 || pass_len > 63) {
        const char* resp = "{\"ok\":false,\"error\":\"Password must be 8-63 chars\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    char new_password[64];
    strncpy(new_password, pass_start, pass_len);
    new_password[pass_len] = '\0';
    
    save_ap_password(new_password);
    
    const char* resp = "{\"ok\":true,\"message\":\"AP password updated. Reconnect to BLE-Monitor\"}";
    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
    
    // Update AP config
    wifi_config_t ap_config = {0};
    esp_wifi_get_config(WIFI_IF_AP, &ap_config);
    strncpy((char*)ap_config.ap.password, new_password, sizeof(ap_config.ap.password));
    ap_config.ap.authmode = WIFI_AUTH_WPA2_PSK;
    esp_wifi_set_config(WIFI_IF_AP, &ap_config);
    
    return ESP_OK;
}

// API: Adafruit IO settings
static esp_err_t api_aio_config_handler(httpd_req_t *req) {
    char buf[512];
    int ret = httpd_req_recv(req, buf, sizeof(buf) - 1);
    if (ret <= 0) {
        httpd_resp_send_500(req);
        return ESP_FAIL;
    }
    buf[ret] = '\0';
    
    // Parseroidaan JSON
    char *user_start = strstr(buf, "\"username\":\"");
    char *key_start = strstr(buf, "\"key\":\"");
    char *enabled_start = strstr(buf, "\"enabled\":");
    char *types_start = strstr(buf, "\"feedTypes\":");
    
    if (!user_start || !key_start) {
        const char* resp = "{\"ok\":false,\"error\":\"Invalid JSON\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    user_start += 12;  // Skip "username":"
    key_start += 7;     // Skip "key":"
    
    char username[64] = {0};
    char key[128] = {0};
    bool enabled = true;
    uint8_t feed_types = FIELD_TEMP | FIELD_HUM;  // Oletus
    
    char *user_end = strchr(user_start, '"');
    char *key_end = strchr(key_start, '"');
    
    if (user_end && key_end) {
        int user_len = user_end - user_start;
        int key_len = key_end - key_start;
        
        if (user_len > 0 && user_len < 64) {
            strncpy(username, user_start, user_len);
        }
        if (key_len > 0 && key_len < 128) {
            strncpy(key, key_start, key_len);
        }
        
        if (enabled_start) {
            enabled_start += 10;  // Skip "enabled":
            enabled = (strncmp(enabled_start, "true", 4) == 0);
        }
        
        if (types_start) {
            types_start += 12;  // Skip "feedTypes":
            int types_val = 0;
            sscanf(types_start, "%d", &types_val);
            feed_types = (uint8_t)types_val;
        }
        
        save_aio_config(username, key, enabled, feed_types);
        
        const char* resp = "{\"ok\":true}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        
        return ESP_OK;
    }
    
    const char* resp = "{\"ok\":false,\"error\":\"Parse error\"}";
    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Get Adafruit IO settings
static esp_err_t api_aio_get_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    char response[512];
    snprintf(response, sizeof(response), 
             "{\"ok\":true,\"username\":\"%s\",\"key\":\"%s\",\"enabled\":%s,\"has_key\":%s,\"feedTypes\":%d}",
             aio_username,
             aio_key,
             aio_enabled ? "true" : "false",
             strlen(aio_key) > 0 ? "true" : "false",
             aio_feed_types);
    
    httpd_resp_sendstr(req, response);
    return ESP_OK;
}

// API: Get D1 settings
static esp_err_t api_d1_get_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    char response[512];
    snprintf(response, sizeof(response), 
             "{\"ok\":true,\"workerUrl\":\"%s\",\"enabled\":%s,\"hasToken\":%s}",
             d1_worker_url,
             d1_enabled ? "true" : "false",
             strlen(d1_token) > 0 ? "true" : "false");
    
    httpd_resp_sendstr(req, response);
    return ESP_OK;
}

// API: Save D1 settings
static esp_err_t api_d1_config_handler(httpd_req_t *req) {
    char buf[512];
    int ret = httpd_req_recv(req, buf, sizeof(buf) - 1);
    if (ret <= 0) {
        httpd_resp_send_500(req);
        return ESP_FAIL;
    }
    buf[ret] = '\0';
    
    char *url_start = strstr(buf, "\"workerUrl\":\"");
    char *token_start = strstr(buf, "\"token\":\"");
    char *enabled_start = strstr(buf, "\"enabled\":");
    
    if (!url_start || !token_start) {
        const char* resp = "{\"ok\":false,\"error\":\"Invalid JSON\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    url_start += 13;
    token_start += 10;
    
    char worker_url[256] = {0};
    char token[128] = {0};
    bool enabled = true;
    
    char *url_end = strchr(url_start, '"');
    char *token_end = strchr(token_start, '"');
    
    if (url_end && token_end) {
        int url_len = url_end - url_start;
        int token_len = token_end - token_start;
        
        if (url_len > 0 && url_len < 256) {
            strncpy(worker_url, url_start, url_len);
        }
        if (token_len > 0 && token_len < 128) {
            strncpy(token, token_start, token_len);
        }
        
        if (enabled_start) {
            enabled_start += 10;
            enabled = (strncmp(enabled_start, "true", 4) == 0);
        }
        
        save_d1_config(worker_url, token, enabled);
        
        const char* resp = "{\"ok\":true}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    const char* resp = "{\"ok\":false,\"error\":\"Parse error\"}";
    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// API: Test D1 connection
static esp_err_t api_d1_test_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    if (strlen(d1_worker_url) == 0 || strlen(d1_token) == 0) {
        const char* resp = "{\"ok\":false,\"error\":\"D1 not configured\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Test connection with ping endpoint
    char url[300];
    snprintf(url, sizeof(url), "%s/ping", d1_worker_url);
    
    esp_http_client_config_t config = {
        .url = url,
        .method = HTTP_METHOD_GET,
        .crt_bundle_attach = esp_crt_bundle_attach,
        .timeout_ms = 5000,
    };
    esp_http_client_handle_t client = esp_http_client_init(&config);
    esp_http_client_set_header(client, "Authorization", d1_token);
    
    esp_err_t err = esp_http_client_perform(client);
    int status = esp_http_client_get_status_code(client);
    esp_http_client_cleanup(client);
    
    if (err == ESP_OK && status == 200) {
        const char* resp = "{\"ok\":true,\"message\":\"Connection successful!\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
    } else {
        char resp[128];
        snprintf(resp, sizeof(resp), "{\"ok\":false,\"error\":\"Connection failed (HTTP %d)\"}", status);
        httpd_resp_send(req, resp, strlen(resp));
    }
    
    return ESP_OK;
}

// API: Start discovery mode (search for new devices)
// NOTE: Scanning runs continuously; this only allows adding new devices
static esp_err_t api_start_scan_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Access-Control-Allow-Origin", "*");
    httpd_resp_set_type(req, "application/json");
    
    if (allow_new_devices) {
        ESP_LOGW(TAG, "Discovery mode is already running");
        httpd_resp_sendstr(req, "{\"ok\":true,\"already_running\":true}");
        return ESP_OK;
    }
    
    ESP_LOGI(TAG, "🔍 DISCOVERY MODE started (no timer, stays on until stopped)");
    
    // Allow adding new devices
    allow_new_devices = true;
    
    httpd_resp_sendstr(req, "{\"ok\":true,\"already_running\":false}");
    return ESP_OK;
}

// API: Stop discovery mode (search for new devices)
static esp_err_t api_stop_scan_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Access-Control-Allow-Origin", "*");
    httpd_resp_set_type(req, "application/json");
    
    ESP_LOGI(TAG, "🔍 DISCOVERY MODE stopped");
    allow_new_devices = false;
    prune_hidden_devices();
    
    httpd_resp_sendstr(req, "{\"ok\":true}");
    return ESP_OK;
}

// API: Get or save scan settings (GET or POST)
static esp_err_t api_scan_settings_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Access-Control-Allow-Origin", "*");
    httpd_resp_set_type(req, "application/json");
    
    if (req->method == HTTP_GET) {
        // Return current settings
        char response[128];
        snprintf(response, sizeof(response), "{\"ok\":true,\"masterBleEnabled\":%s}", 
                 master_ble_enabled ? "true" : "false");
        httpd_resp_sendstr(req, response);
    } else if (req->method == HTTP_POST) {
        // Save new settings
        char buf[256];
        int ret = httpd_req_recv(req, buf, sizeof(buf) - 1);
        if (ret <= 0) {
            httpd_resp_sendstr(req, "{\"ok\":false,\"error\":\"Empty request\"}");
            return ESP_OK;
        }
        buf[ret] = '\0';
        
        // Parse JSON (simple string search)
        char *enabled_str = strstr(buf, "\"masterBleEnabled\":");
        if (enabled_str) {
            enabled_str += strlen("\"masterBleEnabled\":");
            while (*enabled_str == ' ') enabled_str++;
            master_ble_enabled = (strncmp(enabled_str, "true", 4) == 0);
            ESP_LOGI(TAG, "⚙️ Master BLE scan: %s", master_ble_enabled ? "ENABLED" : "DISABLED");
            
            // Save to NVS
            nvs_handle_t nvs;
            if (nvs_open(NVS_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
                nvs_set_u8(nvs, "scan_master", master_ble_enabled ? 1 : 0);
                nvs_commit(nvs);
                nvs_close(nvs);
            }
        }
        
        httpd_resp_sendstr(req, "{\"ok\":true}");
    }
    
    return ESP_OK;
}

// API: Diagnostics (crash logs, memory, boot count)
static esp_err_t api_diagnostics_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    // Get diagnostics from NVS
    nvs_handle_t diag_nvs;
    uint32_t boot_count = 0;
    uint32_t last_reset = 0;
    
    if (nvs_open("diagnostics", NVS_READONLY, &diag_nvs) == ESP_OK) {
        nvs_get_u32(diag_nvs, "boot_count", &boot_count);
        nvs_get_u32(diag_nvs, "last_reset", &last_reset);
        nvs_close(diag_nvs);
    }
    
    // Reset reason strings
    const char* reset_reasons[] = {
        "UNKNOWN", "POWERON", "EXT", "SW", "PANIC", "INT_WDT",
        "TASK_WDT", "WDT", "DEEPSLEEP", "BROWNOUT", "SDIO"
    };
    const char* reset_str = (last_reset < 11) ? reset_reasons[last_reset] : "UNKNOWN";
    
    // Memory stats
    uint32_t free_heap = esp_get_free_heap_size();
    uint32_t min_free_heap = esp_get_minimum_free_heap_size();
    uint32_t largest_block = heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);
    
    // Uptime
    uint32_t uptime_sec = (uint32_t)(esp_timer_get_time() / 1000000);
    
    // BLE stats (total advertisements received)
    uint32_t ble_rate = ble_adv_count;
    
    char response[512];
    snprintf(response, sizeof(response),
        "{\"bootCount\":%lu,"
        "\"lastReset\":\"%s\","
        "\"uptimeSec\":%lu,"
        "\"freeHeap\":%lu,"
        "\"minFreeHeap\":%lu,"
        "\"largestBlock\":%lu,"
        "\"bleAdvCount\":%lu,"
        "\"deviceCount\":%d}",
        boot_count, reset_str, uptime_sec,
        free_heap, min_free_heap, largest_block,
        ble_rate, device_count);
    
    httpd_resp_send(req, response, strlen(response));
    return ESP_OK;
}

// API: Return all VISIBLE devices as JSON (or all if ?all=1)
static esp_err_t api_devices_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Access-Control-Allow-Origin", "*");
    httpd_resp_set_type(req, "application/json");
    
    // Check if parameter ?all=1
    bool show_all = false;
    char query[64];
    if (httpd_req_get_url_query_str(req, query, sizeof(query)) == ESP_OK) {
        char all_param[8];
        if (httpd_query_key_value(query, "all", all_param, sizeof(all_param)) == ESP_OK) {
            show_all = (strcmp(all_param, "1") == 0);
        }
    }
    
    ESP_LOGI(TAG, "API /api/devices called, devices total: %d, show_all=%d", device_count, show_all);
    
    char *json = malloc(16384);
    if (!json) {
        httpd_resp_send_500(req);
        return ESP_FAIL;
    }
    
    strcpy(json, "[");
    bool first = true;
    
    uint32_t now_ms = xTaskGetTickCount() * portTICK_PERIOD_MS;

    // Collect visible (or all) indices and sort by MAC address
    int indices[MAX_DEVICES];
    int count = 0;
    for (int i = 0; i < device_count; i++) {
        if (!show_all && !devices[i].visible) {
            continue;
        }
        // Skip master devices if master BLE is disabled
        if (!master_ble_enabled) {
            // If the source is "local" or empty, it's a master device
            if (devices[i].source[0] == '\0' || strcmp(devices[i].source, "local") == 0) {
                continue;
            }
        }
        indices[count++] = i;
    }

    // Simple bubble sort by MAC address (addr)
    for (int i = 0; i < count - 1; i++) {
        for (int j = 0; j < count - i - 1; j++) {
            ble_device_t *a = &devices[indices[j]];
            ble_device_t *b = &devices[indices[j + 1]];
            if (memcmp(a->addr, b->addr, 6) > 0) {
                int tmp = indices[j];
                indices[j] = indices[j + 1];
                indices[j + 1] = tmp;
            }
        }
    }
    for (int k = 0; k < count; k++) {
        int i = indices[k];
        
        char addr_str[18];
        snprintf(addr_str, sizeof(addr_str), "%02X:%02X:%02X:%02X:%02X:%02X",
            devices[i].addr[0], devices[i].addr[1], devices[i].addr[2],
            devices[i].addr[3], devices[i].addr[4], devices[i].addr[5]);
        
        char item[512];
        uint32_t age_sec = 0;
        uint32_t ref_ms = devices[i].has_sensor_data ? devices[i].last_sensor_seen : devices[i].last_seen;
        if (ref_ms > 0 && now_ms >= ref_ms) {
            age_sec = (now_ms - ref_ms) / 1000;
        }

        if (devices[i].has_sensor_data) {
            // Determine which fields the device supports
            uint16_t available = 0;
            if (devices[i].temperature != 0) available |= FIELD_TEMP;
            if (devices[i].humidity != 0) available |= FIELD_HUM;
            if (devices[i].battery_pct != 0) available |= FIELD_BAT;
            if (devices[i].battery_mv != 0) available |= FIELD_BATMV;
            available |= FIELD_RSSI; // RSSI always available
            available |= FIELD_AGE;  // Update age always available
            
            snprintf(item, sizeof(item),
                "%s{\"addr\":\"%s\",\"name\":\"%s\",\"advName\":\"%s\",\"rssi\":%d,"
                "\"hasSensor\":true,\"temp\":%.1f,\"hum\":%d,\"bat\":%d,\"batMv\":%d,"
                "\"firmware\":\"%s\",\"source\":\"%s\","
                "\"saved\":%s,\"showMac\":%s,\"showIp\":%s,\"fieldMask\":%d,\"availableFields\":%d,\"ageSec\":%lu}",
                first ? "" : ",",
                addr_str,
                devices[i].name[0] ? devices[i].name : "Unknown",
                devices[i].adv_name[0] ? devices[i].adv_name : "",
                devices[i].rssi,
                devices[i].temperature,
                devices[i].humidity,
                devices[i].battery_pct,
                devices[i].battery_mv,
                devices[i].firmware_type[0] ? devices[i].firmware_type : "Unknown",
                devices[i].source[0] ? devices[i].source : "local",
                devices[i].visible ? "true" : "false",
                devices[i].show_mac ? "true" : "false",
                devices[i].show_ip ? "true" : "false",
                devices[i].field_mask,
                available,
                (unsigned long)age_sec);
        } else {
            snprintf(item, sizeof(item),
                "%s{\"addr\":\"%s\",\"name\":\"%s\",\"advName\":\"%s\",\"rssi\":%d,"
                "\"hasSensor\":false,\"source\":\"%s\",\"saved\":%s,\"showMac\":%s,\"showIp\":%s,\"fieldMask\":%d,\"availableFields\":%d,\"ageSec\":%lu}",
                first ? "" : ",",
                addr_str,
                devices[i].name[0] ? devices[i].name : "Unknown",
                devices[i].adv_name[0] ? devices[i].adv_name : "",
                devices[i].rssi,
                devices[i].source[0] ? devices[i].source : "local",
                devices[i].visible ? "true" : "false",
                devices[i].show_mac ? "true" : "false",
                devices[i].show_ip ? "true" : "false",
                devices[i].field_mask,
                FIELD_RSSI | FIELD_AGE,
                (unsigned long)age_sec); // Only RSSI available
        }
        strcat(json, item);
        first = false;
    }
    strcat(json, "]");
    
    httpd_resp_sendstr(req, json);
    free(json);
    return ESP_OK;
}

// API: Vastaanota satelliitti-dataa
static esp_err_t api_satellite_data_handler(httpd_req_t *req) {
    char buf[512];
    int ret = httpd_req_recv(req, buf, sizeof(buf)-1);
    if (ret <= 0) {
        httpd_resp_send_err(req, HTTPD_400_BAD_REQUEST, "No data");
        return ESP_FAIL;
    }
    buf[ret] = '\0';
    
    // Get sender IP address
    char client_ip[16] = {0};
    struct sockaddr_in6 client_addr;
    socklen_t addr_len = sizeof(client_addr);
    
    ESP_LOGI(TAG, "🛰️  Getting client IP...");
    if (httpd_req_get_hdr_value_str(req, "X-Forwarded-For", client_ip, sizeof(client_ip)) == ESP_OK) {
        ESP_LOGI(TAG, "  X-Forwarded-For: %s", client_ip);
    } else {
        ESP_LOGI(TAG, "  No X-Forwarded-For header");
        // If X-Forwarded-For is missing, use direct connection
        int sockfd = httpd_req_to_sockfd(req);
        ESP_LOGI(TAG, "  Socket FD: %d", sockfd);
        
        if (getpeername(sockfd, (struct sockaddr *)&client_addr, &addr_len) == 0) {
            ESP_LOGI(TAG, "  getpeername OK, family: %d (AF_INET=%d, AF_INET6=%d)", 
                     client_addr.sin6_family, AF_INET, AF_INET6);
            
            if (client_addr.sin6_family == AF_INET) {
                struct sockaddr_in *addr_in = (struct sockaddr_in *)&client_addr;
                inet_ntoa_r(addr_in->sin_addr, client_ip, sizeof(client_ip));
                ESP_LOGI(TAG, "  IPv4 address: %s", client_ip);
            } else if (client_addr.sin6_family == AF_INET6) {
                // IPv6 address
                char ipv6_str[INET6_ADDRSTRLEN];
                inet_ntop(AF_INET6, &client_addr.sin6_addr, ipv6_str, sizeof(ipv6_str));
                ESP_LOGI(TAG, "  IPv6 address: %s", ipv6_str);
                // Try to map to IPv4 if it's IPv4-mapped
                if (IN6_IS_ADDR_V4MAPPED(&client_addr.sin6_addr)) {
                    struct in_addr ipv4_addr;
                    memcpy(&ipv4_addr, &client_addr.sin6_addr.s6_addr[12], 4);
                    inet_ntoa_r(ipv4_addr, client_ip, sizeof(client_ip));
                    ESP_LOGI(TAG, "  IPv4-mapped: %s", client_ip);
                }
            }
        } else {
            ESP_LOGE(TAG, "  getpeername FAILED");
        }
    }
    
    ESP_LOGI(TAG, "🛰️  Satellite data from %s (%d bytes)", client_ip, ret);
    
    // Parse JSON: {"mac":"AA:BB:CC:DD:EE:FF","rssi":-65,"data":"0201061AFF..."}
    char mac_str[18] = {0};
    int rssi = 0;
    char hex_data[256] = {0};
    char json_name[64] = {0};
    
    char *p = strstr(buf, "\"mac\":\"");
    if (p) {
        p += 7;
        char *end = strchr(p, '"');
        if (end && (end - p) < 18) {
            memcpy(mac_str, p, end - p);
        }
    }
    
    p = strstr(buf, "\"rssi\":");
    if (p) {
        sscanf(p + 7, "%d", &rssi);
    }
    
    p = strstr(buf, "\"data\":\"");
    if (p) {
        p += 8;
        char *end = strchr(p, '"');
        if (end && (end - p) < 256) {
            memcpy(hex_data, p, end - p);
        }
    }

    p = strstr(buf, "\"name\":\"");
    if (p) {
        p += 8;
        char *end = strchr(p, '"');
        if (end && (end - p) < (int)sizeof(json_name)) {
            memcpy(json_name, p, end - p);
            json_name[end - p] = '\0';
            ESP_LOGI(TAG, "  📛 Satellite JSON name: '%s'", json_name);
        }
    } else {
        ESP_LOGI(TAG, "  📛 Satellite JSON name: (none)");
    }
    
    // Parse MAC address (satellite uses normal order)
    uint8_t mac_addr[6];
    if (sscanf(mac_str, "%hhx:%hhx:%hhx:%hhx:%hhx:%hhx",
               &mac_addr[0], &mac_addr[1], &mac_addr[2], &mac_addr[3], &mac_addr[4], &mac_addr[5]) == 6) {
        
        // LOG: Satellite observation
        ESP_LOGI(TAG, "🛰️  SATELLITE: %s, RSSI: %d dBm, hex_len: %d, from: %s",
                 mac_str, rssi, strlen(hex_data), client_ip);
        
        // Find or add device
        int idx = -1;
        for (int i = 0; i < device_count; i++) {
            if (memcmp(devices[i].addr, mac_addr, 6) == 0) {
                idx = i;
                break;
            }
        }
        
        if (idx < 0 && device_count < MAX_DEVICES) {
            // New device from satellite (default HIDDEN, shown only after selection in scan menu)
            idx = device_count++;
            memcpy(devices[idx].addr, mac_addr, 6);
            devices[idx].visible = load_visibility(mac_addr);
            devices[idx].show_mac = true;
            devices[idx].field_mask = FIELD_ALL;
            devices[idx].adv_name[0] = '\0';
            load_device_settings(mac_addr, devices[idx].name,
                               &devices[idx].show_mac,
                               &devices[idx].show_ip,
                               &devices[idx].field_mask,
                               &devices[idx].user_named);
            if (devices[idx].name[0] == '\0') {
                snprintf(devices[idx].name, MAX_NAME_LEN, "Sat-%02X%02X", mac_addr[4], mac_addr[5]);
            }
            devices[idx].has_sensor_data = false;
            devices[idx].last_sensor_seen = 0;
            snprintf(devices[idx].source, sizeof(devices[idx].source), "satellite-%s", client_ip);
            
            ESP_LOGI(TAG, "🛰️  New satellite device: %s from %s", mac_str, client_ip);
        }
        
        if (idx >= 0) {
            sat_adv_count++;
            
            // Source = satellite whenever a satellite observation arrives
            snprintf(devices[idx].source, sizeof(devices[idx].source), "satellite-%s", client_ip);
            
            // Always update RSSI and timestamp
            devices[idx].rssi = rssi;
            uint32_t now_ms = xTaskGetTickCount() * portTICK_PERIOD_MS;
            devices[idx].last_seen = now_ms;
            
            // Convert hex string to bytes and parse BLE advertisement data
            uint8_t raw_data[128];
            int data_len = strlen(hex_data) / 2;
            for (int i = 0; i < data_len && i < 128; i++) {
                char byte_str[3] = {hex_data[i*2], hex_data[i*2+1], 0};
                raw_data[i] = (uint8_t)strtol(byte_str, NULL, 16);
            }
            
            // Parse advertisement fields
            struct ble_hs_adv_fields fields;
            int parse_result = ble_hs_adv_parse_fields(&fields, raw_data, data_len);
            ESP_LOGI(TAG, "  🔍 Parse fields result: %d, data_len: %d", parse_result, data_len);
            
            if (parse_result == 0) {
                // adv_name updates only if the user hasn't set a custom name
                if (json_name[0] != '\0') {
                    int copy_len = (strlen(json_name) < MAX_NAME_LEN - 1) ? (int)strlen(json_name) : MAX_NAME_LEN - 1;
                    if (!devices[idx].user_named) {
                        memcpy(devices[idx].adv_name, json_name, copy_len);
                        devices[idx].adv_name[copy_len] = '\0';
                    }
                    // Update name if empty, starts with "Sat-", or equals MAC address
                    bool should_update_name = false;
                    if (!devices[idx].user_named && devices[idx].name[0] == '\0') {
                        should_update_name = true;
                    } else if (!devices[idx].user_named && strncmp(devices[idx].name, "Sat-", 4) == 0) {
                        should_update_name = true;
                    } else {
                        char mac_as_name[18];
                        snprintf(mac_as_name, sizeof(mac_as_name), "%02X:%02X:%02X:%02X:%02X:%02X",
                                mac_addr[0], mac_addr[1], mac_addr[2], mac_addr[3], mac_addr[4], mac_addr[5]);
                        if (!devices[idx].user_named && strcmp(devices[idx].name, mac_as_name) == 0) {
                            should_update_name = true;
                        }
                    }
                    if (should_update_name) {
                        memcpy(devices[idx].name, json_name, copy_len);
                        devices[idx].name[copy_len] = '\0';
                        ESP_LOGI(TAG, "  ✏️ Updated name from satellite JSON: %s", devices[idx].name);
                    }
                }

                bool has_svc16 = (fields.svc_data_uuid16 != NULL && fields.svc_data_uuid16_len > 0);
                bool has_mfg = (fields.mfg_data != NULL && fields.mfg_data_len > 0);
                ESP_LOGI(TAG, "  📦 Payload: svc16=%s len=%d, mfg=%s len=%d",
                         has_svc16 ? "yes" : "no", fields.svc_data_uuid16_len,
                         has_mfg ? "yes" : "no", fields.mfg_data_len);

                // Copy device name if user hasn't set custom name
                if (fields.name != NULL && fields.name_len > 0) {
                    ESP_LOGI(TAG, "  📛 Device name found: len=%d", fields.name_len);
                    int copy_len = (fields.name_len < MAX_NAME_LEN - 1) ? fields.name_len : MAX_NAME_LEN - 1;
                    if (!devices[idx].user_named) {
                        memcpy(devices[idx].adv_name, fields.name, copy_len);
                        devices[idx].adv_name[copy_len] = '\0';
                    }
                    // Update name if empty, starts with "Sat-", or equals MAC address
                    bool should_update_name = false;
                    if (!devices[idx].user_named && devices[idx].name[0] == '\0') {
                        should_update_name = true;
                    } else if (!devices[idx].user_named && strncmp(devices[idx].name, "Sat-", 4) == 0) {
                        should_update_name = true;
                    } else {
                        // Tarkista onko nimi vain MAC-osoite muodossa XX:XX:XX:XX:XX:XX
                        char mac_as_name[18];
                        snprintf(mac_as_name, sizeof(mac_as_name), "%02X:%02X:%02X:%02X:%02X:%02X",
                                mac_addr[0], mac_addr[1], mac_addr[2], mac_addr[3], mac_addr[4], mac_addr[5]);
                        if (!devices[idx].user_named && strcmp(devices[idx].name, mac_as_name) == 0) {
                            should_update_name = true;
                        }
                    }
                    if (should_update_name) {
                        memcpy(devices[idx].name, fields.name, copy_len);
                        devices[idx].name[copy_len] = '\0';
                        ESP_LOGI(TAG, "  ✏️ Updated name to: %s", devices[idx].name);
                    }
                } else {
                    ESP_LOGI(TAG, "  📛 No device name in adv/scan response");
                }
                
                // Parse sensor data (pvvx/ATC format UUID 0x181A, MiBeacon UUID 0xFE95, or BTHome v2 UUID 0xFCD2)
                if (fields.svc_data_uuid16 != NULL && fields.svc_data_uuid16_len >= 13) {
                    uint16_t uuid = fields.svc_data_uuid16[0] | (fields.svc_data_uuid16[1] << 8);
                    ESP_LOGI(TAG, "  🔬 Service UUID: 0x%04X, len: %d", uuid, fields.svc_data_uuid16_len);
                    
                    if (uuid == 0x181A) {
                        // pvvx or ATC custom firmware
                        ble_sensor_data_t sensor_data;
                        bool parsed = false;
                        
                        if (fields.svc_data_uuid16_len >= 17) {
                            parsed = ble_parse_pvvx_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                            ESP_LOGI(TAG, "  ✅ pvvx parse: %s", parsed ? "SUCCESS" : "FAILED");
                        } else if (fields.svc_data_uuid16_len >= 15) {
                            parsed = ble_parse_atc_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                            ESP_LOGI(TAG, "  ✅ ATC parse: %s", parsed ? "SUCCESS" : "FAILED");
                        }
                        
                        if (parsed) {
                            sat_sensor_count++;
                            ESP_LOGI(TAG, "  🌡️  Satellite sensor: %.1f°C, %d%%, %d%%", 
                                     sensor_data.temperature/100.0, sensor_data.humidity/100, sensor_data.battery_pct);
                            devices[idx].temperature = sensor_data.temperature;
                            devices[idx].humidity = sensor_data.humidity;
                            devices[idx].battery_pct = sensor_data.battery_pct;
                            devices[idx].battery_mv = sensor_data.battery_mv;
                            strncpy(devices[idx].firmware_type, sensor_data.device_type, sizeof(devices[idx].firmware_type) - 1);
                            devices[idx].firmware_type[sizeof(devices[idx].firmware_type) - 1] = '\0';
                            devices[idx].has_sensor_data = true;
                            devices[idx].last_sensor_seen = now_ms;
                        }
                    } else if (uuid == 0xFE95) {
                        // MiBeacon - Xiaomi original firmware
                        ble_sensor_data_t sensor_data;
                        bool parsed = ble_parse_mibeacon_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                        ESP_LOGI(TAG, "  ✅ MiBeacon parse: %s", parsed ? "SUCCESS" : "FAILED");
                        
                        if (parsed) {
                            sat_sensor_count++;
                            devices[idx].temperature = sensor_data.temperature;
                            devices[idx].humidity = sensor_data.humidity;
                            devices[idx].battery_pct = sensor_data.battery_pct;
                            devices[idx].battery_mv = sensor_data.battery_mv;
                            strncpy(devices[idx].firmware_type, sensor_data.device_type, sizeof(devices[idx].firmware_type) - 1);
                            devices[idx].firmware_type[sizeof(devices[idx].firmware_type) - 1] = '\0';
                            devices[idx].has_sensor_data = true;
                            devices[idx].last_sensor_seen = now_ms;
                        }
                    } else if (uuid == 0xFCD2) {
                        // BTHome v2
                        ble_sensor_data_t sensor_data;
                        bool parsed = ble_parse_bthome_v2_format(fields.svc_data_uuid16, fields.svc_data_uuid16_len, &sensor_data);
                        ESP_LOGI(TAG, "  ✅ BTHome parse: %s", parsed ? "SUCCESS" : "FAILED");
                        
                        if (parsed) {
                            sat_sensor_count++;
                            devices[idx].temperature = sensor_data.temperature;
                            devices[idx].humidity = sensor_data.humidity;
                            devices[idx].battery_pct = sensor_data.battery_pct;
                            devices[idx].battery_mv = sensor_data.battery_mv;
                            strncpy(devices[idx].firmware_type, sensor_data.device_type, sizeof(devices[idx].firmware_type) - 1);
                            devices[idx].firmware_type[sizeof(devices[idx].firmware_type) - 1] = '\0';
                            devices[idx].has_sensor_data = true;
                            devices[idx].last_sensor_seen = now_ms;
                        }
                    }
                }
            }
        }
    }
    
    // Send response
    httpd_resp_set_type(req, "application/json");
    httpd_resp_sendstr(req, "{\"status\":\"ok\"}");
    return ESP_OK;
}

// API: Change device visibility
static esp_err_t api_toggle_visibility_handler(httpd_req_t *req) {
    char content[256];
    int ret = httpd_req_recv(req, content, sizeof(content) - 1);
    if (ret <= 0) {
        httpd_resp_send_err(req, HTTPD_400_BAD_REQUEST, "Invalid request");
        return ESP_FAIL;
    }
    content[ret] = '\0';
    
    // Parsitaan addr ja visible parametrit
    char addr_str[64] = {0};  // Tarpeeksi iso URL-enkoodatulle osoitteelle
    int visible = 1;
    
    char *addr_param = strstr(content, "addr=");
    char *visible_param = strstr(content, "visible=");
    
    if (addr_param) {
        sscanf(addr_param, "addr=%60[^&]", addr_str);  // Kasvatettu 18 -> 60
        
        ESP_LOGI(TAG, "URL-enkoodattu osoite: %s", addr_str);
        
        // URL-dekoodaus (muuta %3A tai %3a takaisin :)
        char decoded[20];
        int j = 0;
        for (int i = 0; addr_str[i] && j < sizeof(decoded) - 1; i++) {
            if (addr_str[i] == '%' && addr_str[i+1] && addr_str[i+2]) {
                if ((addr_str[i+1] == '3' || addr_str[i+1] == '3') && 
                    (addr_str[i+2] == 'A' || addr_str[i+2] == 'a')) {
                    decoded[j++] = ':';
                    i += 2;
                } else {
                    decoded[j++] = addr_str[i];
                }
            } else {
                decoded[j++] = addr_str[i];
            }
        }
        decoded[j] = '\0';
        strcpy(addr_str, decoded);
        
        ESP_LOGI(TAG, "Decoded address: %s", addr_str);
    }
    
    if (visible_param) {
        sscanf(visible_param, "visible=%d", &visible);
    }
    
    ESP_LOGI(TAG, "API request to set visibility: %s -> visible=%d", addr_str, visible);
    
    // Find device and update its state
    for (int i = 0; i < device_count; i++) {
        char dev_addr[18];
        snprintf(dev_addr, sizeof(dev_addr), "%02X:%02X:%02X:%02X:%02X:%02X",
            devices[i].addr[0], devices[i].addr[1], devices[i].addr[2],
            devices[i].addr[3], devices[i].addr[4], devices[i].addr[5]);
        
        if (strcmp(dev_addr, addr_str) == 0) {
            ESP_LOGI(TAG, "Device found at index %d, previous visible=%d", i, devices[i].visible);
            if (visible) {
                devices[i].visible = true;
                save_visibility(devices[i].addr, true);
                ESP_LOGI(TAG, "✓ Device %d visibility updated -> 1", i);
            } else {
                remove_device_by_index(i, true);
                ESP_LOGI(TAG, "✓ Device removed from list (visibility off)");
            }
            break;
        }
    }
    
    ESP_LOGI(TAG, "Response sent");
    
    httpd_resp_sendstr(req, "{\"ok\":true}");
    return ESP_OK;
}

// API: Clear visibility selections for all devices (also from NVS)
static esp_err_t api_clear_visibility_handler(httpd_req_t *req) {
    int cleared_nvs = 0;
    int cleared_devices = 0;

    for (int i = device_count - 1; i >= 0; i--) {
        cleared_nvs += remove_device_by_index(i, true);
        cleared_devices++;
    }

    ESP_LOGI(TAG, "🗑️ Visibility reset: %d devices removed, %d NVS keys removed", cleared_devices, cleared_nvs);

    char response[128];
    snprintf(response, sizeof(response), "{\"ok\":true,\"cleared\":%d,\"nvs_cleared\":%d}", cleared_devices, cleared_nvs);
    httpd_resp_set_type(req, "application/json");
    httpd_resp_sendstr(req, response);
    return ESP_OK;
}

// API: Forget a specific device (remove from memory and NVS)
static esp_err_t api_forget_device_handler(httpd_req_t *req) {
    httpd_resp_set_type(req, "application/json");
    
    // Get MAC address from query string
    char query[64];
    char mac_str[16];
    if (httpd_req_get_url_query_str(req, query, sizeof(query)) != ESP_OK) {
        const char* resp = "{\"ok\":false,\"error\":\"Missing query string\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    if (httpd_query_key_value(query, "mac", mac_str, sizeof(mac_str)) != ESP_OK) {
        const char* resp = "{\"ok\":false,\"error\":\"Missing MAC parameter\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Validate MAC format (12 hex chars)
    if (strlen(mac_str) != 12) {
        const char* resp = "{\"ok\":false,\"error\":\"Invalid MAC format (need 12 hex chars)\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Convert to uppercase for consistency
    for (int i = 0; i < 12; i++) {
        mac_str[i] = toupper(mac_str[i]);
        if (!((mac_str[i] >= '0' && mac_str[i] <= '9') || 
              (mac_str[i] >= 'A' && mac_str[i] <= 'F'))) {
            const char* resp = "{\"ok\":false,\"error\":\"Invalid MAC format (not hex)\"}";
            httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
            return ESP_OK;
        }
    }
    
    // Parse MAC address
    uint8_t target_mac[6];
    for (int i = 0; i < 6; i++) {
        char byte_str[3] = {mac_str[i*2], mac_str[i*2+1], '\0'};
        target_mac[i] = (uint8_t)strtol(byte_str, NULL, 16);
    }
    
    // Generate NVS key in reversed order (same as load_visibility)
    char nvs_key[13];
    snprintf(nvs_key, sizeof(nvs_key), "%02X%02X%02X%02X%02X%02X",
             target_mac[5], target_mac[4], target_mac[3],
             target_mac[2], target_mac[1], target_mac[0]);
    
    // Find device in list
    int found_idx = -1;
    for (int i = 0; i < device_count; i++) {
        if (memcmp(devices[i].addr, target_mac, 6) == 0) {
            found_idx = i;
            break;
        }
    }
    
    if (found_idx == -1) {
        const char* resp = "{\"ok\":false,\"error\":\"Device not found\"}";
        httpd_resp_send(req, resp, HTTPD_RESP_USE_STRLEN);
        return ESP_OK;
    }
    
    // Remove ALL keys from NVS related to this device
    int nvs_removed_count = 0;
    nvs_handle_t nvs;
    if (nvs_open(NVS_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
        // Remove visibility key (use reversed order like load_visibility)
        if (nvs_erase_key(nvs, nvs_key) == ESP_OK) {
            nvs_removed_count++;
        }
        
        // Remove settings keys (FFEEDDCCBBAA_n, _m, _i, _f, _u)
        const char* suffixes[] = {"_n", "_m", "_i", "_f", "_u"};
        for (int i = 0; i < 5; i++) {
            char key[24];
            snprintf(key, sizeof(key), "%s%s", nvs_key, suffixes[i]);
            if (nvs_erase_key(nvs, key) == ESP_OK) {
                nvs_removed_count++;
            }
        }
        
        nvs_commit(nvs);
        nvs_close(nvs);
    }
    
    // Remove from device list (shift remaining devices down)
    char device_name[32];
    strncpy(device_name, devices[found_idx].name, sizeof(device_name) - 1);
    device_name[sizeof(device_name) - 1] = '\0';
    
    for (int i = found_idx; i < device_count - 1; i++) {
        memcpy(&devices[i], &devices[i + 1], sizeof(ble_device_t));
    }
    device_count--;
    
    ESP_LOGI(TAG, "🗑️ Forgot device: %s (%s), NVS key: %s, removed: %d", 
             mac_str, device_name, nvs_key, nvs_removed_count);
    
    char response[128];
    snprintf(response, sizeof(response), 
             "{\"ok\":true,\"mac\":\"%s\",\"name\":\"%s\",\"nvs_removed\":%d}", 
             mac_str, device_name, nvs_removed_count);
    httpd_resp_send(req, response, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// Identify device "signature" (which fields it has)
static uint16_t get_device_signature(const ble_device_t *dev) {
    uint16_t sig = 0;
    if (dev->has_sensor_data) {
        sig |= (1 << 0); // Is a sensor device
        if (dev->temperature != 0) sig |= (1 << 1);
        if (dev->humidity != 0) sig |= (1 << 2);
        if (dev->battery_pct != 0) sig |= (1 << 3);
        if (dev->battery_mv != 0) sig |= (1 << 4);
    }
    return sig;
}

static esp_err_t api_update_settings_handler(httpd_req_t *req) {
    char buf[512];
    int ret, remaining = req->content_len;
    
    if (remaining >= sizeof(buf)) {
        httpd_resp_send_err(req, HTTPD_500_INTERNAL_SERVER_ERROR, "Content too long");
        return ESP_FAIL;
    }
    
    ret = httpd_req_recv(req, buf, remaining);
    if (ret <= 0) {
        if (ret == HTTPD_SOCK_ERR_TIMEOUT) {
            httpd_resp_send_408(req);
        }
        return ESP_FAIL;
    }
    buf[ret] = '\0';
    
    ESP_LOGI(TAG, "Update settings request: %s", buf);
    
    // Parse parameters: addr, name, show_mac, show_ip, field_mask, apply_to_similar
    char addr_str[64] = {0};
    char name[MAX_NAME_LEN] = {0};
    int show_mac = 1;
    int show_ip = 0;
    int field_mask = FIELD_ALL;
    int apply_to_similar = 0;
    
    char *addr_param = strstr(buf, "addr=");
    char *name_param = strstr(buf, "&name=");
    char *show_mac_param = strstr(buf, "&show_mac=");
    char *show_ip_param = strstr(buf, "&show_ip=");
    char *field_mask_param = strstr(buf, "&field_mask=");
    char *apply_param = strstr(buf, "&apply_to_similar=");
    
    if (addr_param) {
        sscanf(addr_param, "addr=%60[^&]", addr_str);
        
        // URL decode
        char decoded[64];
        int j = 0;
        for (int i = 0; addr_str[i] && j < 63; i++) {
            if (addr_str[i] == '%' && addr_str[i+1] && addr_str[i+2]) {
                char hex[3] = {addr_str[i+1], addr_str[i+2], 0};
                // Support both uppercase and lowercase (%3A and %3a)
                char c;
                if (hex[0] >= 'a') hex[0] -= 32;
                if (hex[1] >= 'a') hex[1] -= 32;
                sscanf(hex, "%hhX", &c);
                decoded[j++] = c;
                i += 2;
            } else if (addr_str[i] == '+') {
                decoded[j++] = ' ';
            } else {
                decoded[j++] = addr_str[i];
            }
        }
        decoded[j] = '\0';
        strcpy(addr_str, decoded);
    }
    
    if (name_param) {
        sscanf(name_param, "&name=%60[^&]", name);
        // URL decode for name
        char decoded[MAX_NAME_LEN];
        int j = 0;
        for (int i = 0; name[i] && j < MAX_NAME_LEN-1; i++) {
            if (name[i] == '%' && name[i+1] && name[i+2]) {
                char hex[3] = {name[i+1], name[i+2], 0};
                char c;
                if (hex[0] >= 'a') hex[0] -= 32;
                if (hex[1] >= 'a') hex[1] -= 32;
                sscanf(hex, "%hhX", &c);
                decoded[j++] = c;
                i += 2;
            } else if (name[i] == '+') {
                decoded[j++] = ' ';
            } else {
                decoded[j++] = name[i];
            }
        }
        decoded[j] = '\0';
        strcpy(name, decoded);
    }
    
    if (show_mac_param) {
        sscanf(show_mac_param, "&show_mac=%d", &show_mac);
    }

    if (show_ip_param) {
        sscanf(show_ip_param, "&show_ip=%d", &show_ip);
    }
    
    if (field_mask_param) {
        sscanf(field_mask_param, "&field_mask=%d", &field_mask);
    }
    
    if (apply_param) {
        sscanf(apply_param, "&apply_to_similar=%d", &apply_to_similar);
    }
    
    ESP_LOGI(TAG, "Updating device: %s, name='%s', show_mac=%d, show_ip=%d, fields=0x%04X, apply=%d",
             addr_str, name, show_mac, show_ip, field_mask, apply_to_similar);
    
    // Find device
    int target_idx = -1;
    for (int i = 0; i < device_count; i++) {
        char dev_addr[18];
        snprintf(dev_addr, sizeof(dev_addr), "%02X:%02X:%02X:%02X:%02X:%02X",
            devices[i].addr[0], devices[i].addr[1], devices[i].addr[2],
            devices[i].addr[3], devices[i].addr[4], devices[i].addr[5]);
        
        if (strcmp(dev_addr, addr_str) == 0) {
            target_idx = i;
            break;
        }
    }
    
    if (target_idx == -1) {
        ESP_LOGW(TAG, "Device not found: %s", addr_str);
        httpd_resp_send_err(req, HTTPD_404_NOT_FOUND, "Device not found");
        return ESP_FAIL;
    }
    
    // Update device settings
    strncpy(devices[target_idx].name, name, MAX_NAME_LEN - 1);
    devices[target_idx].show_mac = (show_mac != 0);
    devices[target_idx].show_ip = (show_ip != 0);
    devices[target_idx].field_mask = field_mask;
    devices[target_idx].user_named = (name[0] != '\0');
    
    // Save settings
    save_device_settings(devices[target_idx].addr, name, devices[target_idx].show_mac, devices[target_idx].show_ip, field_mask, devices[target_idx].user_named);
    
    // If apply_to_similar is set, find similar devices
    int updated_count = 1;
    if (apply_to_similar) {
        uint16_t target_sig = get_device_signature(&devices[target_idx]);
        ESP_LOGI(TAG, "Apply settings to similar devices (signature: 0x%04X)", target_sig);
        
        for (int i = 0; i < device_count; i++) {
            if (i == target_idx) continue;
            
            uint16_t sig = get_device_signature(&devices[i]);
            if (sig == target_sig) {
                // Apply only show_mac, show_ip, and field_mask, not the name!
                devices[i].show_mac = devices[target_idx].show_mac;
                devices[i].show_ip = devices[target_idx].show_ip;
                devices[i].field_mask = devices[target_idx].field_mask;
                save_device_settings(devices[i].addr, devices[i].name, devices[i].show_mac, devices[i].show_ip, field_mask, devices[i].user_named);
                updated_count++;
                ESP_LOGI(TAG, "  Updated: %02X:%02X:...", devices[i].addr[0], devices[i].addr[1]);
            }
        }
    }
    
    ESP_LOGI(TAG, "Updated %d devices", updated_count);
    
    char response[128];
    snprintf(response, sizeof(response), "{\"ok\":true,\"updated\":%d}", updated_count);
    httpd_resp_sendstr(req, response);
    return ESP_OK;
}

// PWA: manifest
static esp_err_t manifest_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Cache-Control", "no-store");
    httpd_resp_set_type(req, "application/manifest+json");
    const char *manifest =
        "{"
        "\"name\":\"BLE Devices\","
        "\"short_name\":\"BLE Hub\","
        "\"start_url\":\"/\","
        "\"display\":\"standalone\","
        "\"background_color\":\"#0f172a\","
        "\"theme_color\":\"#0f172a\","
        "\"icons\":["
        "{\"src\":\"/icon-192.png\",\"sizes\":\"192x192\",\"type\":\"image/png\"},"
        "{\"src\":\"/icon-512.png\",\"sizes\":\"512x512\",\"type\":\"image/png\"},"
        "{\"src\":\"/icon.svg\",\"sizes\":\"any\",\"type\":\"image/svg+xml\"}"
        "]"
        "}";
    httpd_resp_sendstr(req, manifest);
    return ESP_OK;
}

// PWA: service worker (network-only, no caching)
static esp_err_t sw_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Cache-Control", "no-store");
    httpd_resp_set_type(req, "application/javascript");
    const char *sw =
        "self.addEventListener('install',e=>{self.skipWaiting();});"
        "self.addEventListener('activate',e=>{e.waitUntil(self.clients.claim());});"
        "self.addEventListener('fetch',e=>{"
        "e.respondWith(fetch(e.request,{cache:'no-store'}));"
        "});";
    httpd_resp_sendstr(req, sw);
    return ESP_OK;
}

// PWA: simple SVG icon
static esp_err_t icon_svg_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Cache-Control", "no-store");
    httpd_resp_set_type(req, "image/svg+xml");
    const char *svg =
        "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 128 128'>"
        "<rect width='128' height='128' rx='24' fill='#0f172a'/>"
        "<path d='M64 20c-16.6 0-30 13.4-30 30v8h12v-8c0-9.9 8.1-18 18-18s18 8.1 18 18v8h12v-8c0-16.6-13.4-30-30-30z' fill='#3b82f6'/>"
        "<circle cx='64' cy='74' r='26' fill='#1e293b' stroke='#3b82f6' stroke-width='6'/>"
        "<circle cx='64' cy='74' r='6' fill='#60a5fa'/>"
        "</svg>";
    httpd_resp_sendstr(req, svg);
    return ESP_OK;
}

// PWA: PNG icon (1x1 transparent, scaled by OS)
static esp_err_t icon_png_handler(httpd_req_t *req) {
    httpd_resp_set_hdr(req, "Cache-Control", "no-store");
    httpd_resp_set_type(req, "image/png");
    static const uint8_t icon_png[] = {
        0x89,0x50,0x4E,0x47,0x0D,0x0A,0x1A,0x0A,
        0x00,0x00,0x00,0x0D,0x49,0x48,0x44,0x52,
        0x00,0x00,0x00,0x01,0x00,0x00,0x00,0x01,
        0x08,0x04,0x00,0x00,0x00,0xB5,0x1C,0x0C,
        0x02,0x00,0x00,0x00,0x0B,0x49,0x44,0x41,
        0x54,0x78,0x9C,0x63,0x60,0x00,0x00,0x00,
        0x02,0x00,0x01,0x4C,0x49,0x8C,0x02,0x00,
        0x00,0x00,0x00,0x49,0x45,0x4E,0x44,0xAE,
        0x42,0x60,0x82
    };
    httpd_resp_send(req, (const char *)icon_png, sizeof(icon_png));
    return ESP_OK;
}

static void start_webserver(void) {
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    config.max_uri_handlers = 31;
    config.stack_size = 8192;
    
    if (httpd_start(&server, &config) == ESP_OK) {
        httpd_uri_t root = {
            .uri = "/",
            .method = HTTP_GET,
            .handler = root_get_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &root);

        httpd_uri_t manifest = {
            .uri = "/manifest.json",
            .method = HTTP_GET,
            .handler = manifest_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &manifest);

        httpd_uri_t sw = {
            .uri = "/sw.js",
            .method = HTTP_GET,
            .handler = sw_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &sw);

        httpd_uri_t icon_svg = {
            .uri = "/icon.svg",
            .method = HTTP_GET,
            .handler = icon_svg_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &icon_svg);

        httpd_uri_t icon_192 = {
            .uri = "/icon-192.png",
            .method = HTTP_GET,
            .handler = icon_png_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &icon_192);

        httpd_uri_t icon_512 = {
            .uri = "/icon-512.png",
            .method = HTTP_GET,
            .handler = icon_png_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &icon_512);
        
        httpd_uri_t api_devices = {
            .uri = "/api/devices",
            .method = HTTP_GET,
            .handler = api_devices_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_devices);
        
        httpd_uri_t api_diagnostics = {
            .uri = "/api/diagnostics",
            .method = HTTP_GET,
            .handler = api_diagnostics_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_diagnostics);
        
        httpd_uri_t api_satellite_data = {
            .uri = "/api/satellite-data",
            .method = HTTP_POST,
            .handler = api_satellite_data_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_satellite_data);
        
        httpd_uri_t api_toggle_visibility = {
            .uri = "/api/toggle-visibility",
            .method = HTTP_POST,
            .handler = api_toggle_visibility_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_toggle_visibility);

        httpd_uri_t api_clear_visibility = {
            .uri = "/api/clear-visibility",
            .method = HTTP_POST,
            .handler = api_clear_visibility_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_clear_visibility);
        
        httpd_uri_t api_forget_device = {
            .uri = "/api/forget-device",
            .method = HTTP_POST,
            .handler = api_forget_device_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_forget_device);
        
        httpd_uri_t api_update_settings = {
            .uri = "/api/update-settings",
            .method = HTTP_POST,
            .handler = api_update_settings_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_update_settings);
        
        httpd_uri_t api_start_scan = {
            .uri = "/api/start-scan",
            .method = HTTP_POST,
            .handler = api_start_scan_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_start_scan);
        
        httpd_uri_t api_stop_scan = {
            .uri = "/api/stop-scan",
            .method = HTTP_POST,
            .handler = api_stop_scan_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_stop_scan);
        
        httpd_uri_t api_scan_settings_get = {
            .uri = "/api/scan-settings",
            .method = HTTP_GET,
            .handler = api_scan_settings_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_scan_settings_get);
        
        httpd_uri_t api_scan_settings_post = {
            .uri = "/api/scan-settings",
            .method = HTTP_POST,
            .handler = api_scan_settings_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_scan_settings_post);
        
        httpd_uri_t api_setup = {
            .uri = "/api/setup",
            .method = HTTP_POST,
            .handler = api_setup_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_setup);
        
        httpd_uri_t api_status = {
            .uri = "/api/status",
            .method = HTTP_GET,
            .handler = api_status_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_status);
        
        httpd_uri_t api_ap_password = {
            .uri = "/api/ap-password",
            .method = HTTP_POST,
            .handler = api_ap_password_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_ap_password);
        
        httpd_uri_t api_aio_config = {
            .uri = "/api/aio/config",
            .method = HTTP_POST,
            .handler = api_aio_config_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_aio_config);
        
    
        httpd_uri_t api_aio_get = {
            .uri = "/api/aio/config",
            .method = HTTP_GET,
            .handler = api_aio_get_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_aio_get);
        
        httpd_uri_t api_aio_send = {
            .uri = "/api/aio/send_now",
            .method = HTTP_POST,
            .handler = api_aio_send_now_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_aio_send);
        
        httpd_uri_t api_aio_create = {
            .uri = "/api/aio/create_feeds",
            .method = HTTP_POST,
            .handler = api_aio_create_feeds_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_aio_create);
        
        httpd_uri_t api_aio_delete = {
            .uri = "/api/aio/delete_feeds",
            .method = HTTP_DELETE,
            .handler = api_aio_delete_feeds_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_aio_delete);
        
        httpd_uri_t api_d1_get = {
            .uri = "/api/d1/config",
            .method = HTTP_GET,
            .handler = api_d1_get_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_d1_get);
        
        httpd_uri_t api_d1_config = {
            .uri = "/api/d1/config",
            .method = HTTP_POST,
            .handler = api_d1_config_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_d1_config);
        
        httpd_uri_t api_d1_test = {
            .uri = "/api/d1/test",
            .method = HTTP_POST,
            .handler = api_d1_test_handler,
            .user_ctx = NULL
        };
        httpd_register_uri_handler(server, &api_d1_test);
        
        ESP_LOGI(TAG, "HTTP server started");
    }
}

// UART console task for factory reset
static void uart_console_task(void *pvParameters) {
    uart_config_t uart_config = {
        .baud_rate = 115200,
        .data_bits = UART_DATA_8_BITS,
        .parity = UART_PARITY_DISABLE,
        .stop_bits = UART_STOP_BITS_1,
        .flow_ctrl = UART_HW_FLOWCTRL_DISABLE,
    };
    uart_param_config(UART_NUM_0, &uart_config);
    uart_driver_install(UART_NUM_0, 256, 0, 0, NULL, 0);

    char rx_buffer[128];
    ESP_LOGI(TAG, "UART console ready. Type 'factory_reset' to erase all settings.");

    while (1) {
        int len = uart_read_bytes(UART_NUM_0, (uint8_t*)rx_buffer, sizeof(rx_buffer) - 1, pdMS_TO_TICKS(100));
        if (len > 0) {
            rx_buffer[len] = '\0';
            
            // Remove newlines/carriage returns
            for (int i = 0; i < len; i++) {
                if (rx_buffer[i] == '\r' || rx_buffer[i] == '\n') {
                    rx_buffer[i] = '\0';
                    break;
                }
            }
            
            if (strlen(rx_buffer) > 0) {
                ESP_LOGI(TAG, "Command received: %s", rx_buffer);
                
                if (strcmp(rx_buffer, "factory_reset") == 0) {
                    ESP_LOGW(TAG, "🔥 FACTORY RESET initiated!");
                    ESP_LOGW(TAG, "Erasing all NVS data (WiFi, Adafruit IO, Cloudflare D1, devices)...");
                    
                    // Erase all NVS partitions
                    esp_err_t err = nvs_flash_erase();
                    if (err == ESP_OK) {
                        ESP_LOGI(TAG, "✅ Factory reset complete. Rebooting...");
                        vTaskDelay(pdMS_TO_TICKS(1000));
                        esp_restart();
                    } else {
                        ESP_LOGE(TAG, "❌ Factory reset failed: %s", esp_err_to_name(err));
                    }
                } else if (strcmp(rx_buffer, "help") == 0) {
                    ESP_LOGI(TAG, "Available commands:");
                    ESP_LOGI(TAG, "  factory_reset - Erase all settings and reboot");
                    ESP_LOGI(TAG, "  help          - Show this help");
                } else {
                    ESP_LOGW(TAG, "Unknown command: %s (type 'help' for commands)", rx_buffer);
                }
            }
        }
        vTaskDelay(pdMS_TO_TICKS(100));
    }
}

void app_main() {
    ESP_LOGI(TAG, "BLE Scanner + Web UI starting");
    
    // Log reset reason for crash diagnostics
    esp_reset_reason_t reset_reason = esp_reset_reason();
    const char* reset_reason_str[] = {
        "UNKNOWN", "POWERON", "EXT", "SW", "PANIC", "INT_WDT", 
        "TASK_WDT", "WDT", "DEEPSLEEP", "BROWNOUT", "SDIO"
    };
    ESP_LOGW(TAG, "🔄 Reset reason: %s", reset_reason_str[reset_reason]);
    
    // NVS alustus
    esp_err_t ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK(ret);
    
    // Boot counter and crash tracking
    nvs_handle_t diag_nvs;
    uint32_t boot_count = 0;
    if (nvs_open("diagnostics", NVS_READWRITE, &diag_nvs) == ESP_OK) {
        nvs_get_u32(diag_nvs, "boot_count", &boot_count);
        boot_count++;
        nvs_set_u32(diag_nvs, "boot_count", boot_count);
        nvs_set_u32(diag_nvs, "last_reset", (uint32_t)reset_reason);
        nvs_commit(diag_nvs);
        nvs_close(diag_nvs);
        ESP_LOGI(TAG, "📊 Boot count: %lu (Reason: %s)", boot_count, reset_reason_str[reset_reason]);
        
        // Warn if crashed
        if (reset_reason == ESP_RST_PANIC || reset_reason == ESP_RST_INT_WDT || 
            reset_reason == ESP_RST_TASK_WDT || reset_reason == ESP_RST_WDT) {
            ESP_LOGE(TAG, "⚠️ CRASH DETECTED! Last boot was abnormal. Check serial logs.");
        }
    }
    
    // Log free memory
    ESP_LOGI(TAG, "💾 Free heap: %lu bytes (largest block: %lu bytes)", 
             esp_get_free_heap_size(), heap_caps_get_largest_free_block(MALLOC_CAP_8BIT));
    
    nvs_handle_t nvs;
    if (nvs_open(NVS_NAMESPACE, NVS_READWRITE, &nvs) == ESP_OK) {
        // Load master BLE scan setting
        uint8_t master_ble_val = 1; // Enabled by default
        if (nvs_get_u8(nvs, "scan_master", &master_ble_val) == ESP_OK) {
            master_ble_enabled = (master_ble_val != 0);
            ESP_LOGI(TAG, "📂 Loaded setting: Master BLE scan = %s", master_ble_enabled ? "ENABLED" : "DISABLED");
        }
        nvs_close(nvs);
    }
    
    // Check BOOT button for WiFi reset
    check_boot_button();
    
    // Load saved devices from NVS
    load_all_devices_from_nvs();
    ESP_LOGI(TAG, "Loaded %d saved devices from NVS", device_count);
    
    wifi_init();
    start_webserver();

    // Start satellite discovery broadcast
    xTaskCreate(discovery_broadcast_task, "discovery_broadcast", 4096, NULL, 4, NULL);
    
    // Load Adafruit IO settings
    load_aio_config();
    
    // Load Cloudflare D1 settings
    load_d1_config();
    
    // Start Adafruit IO timer if settings are configured
    if (aio_enabled && strlen(aio_username) > 0 && strlen(aio_key) > 0) {
        esp_timer_create_args_t aio_timer_args = {
            .callback = aio_timer_callback,
            .name = "aio_timer"
        };
        esp_timer_create(&aio_timer_args, &aio_timer);
        esp_timer_start_periodic(aio_timer, AIO_SEND_INTERVAL_MS * 1000);  // Microsekunteja
        ESP_LOGI(AIO_TAG, "Timer started, send every %d min", AIO_SEND_INTERVAL_MS / 60000);
    }

    // BLE packet rate logging
    if (ble_rate_timer == NULL) {
        esp_timer_create_args_t rate_timer_args = {
            .callback = ble_rate_timer_callback,
            .name = "ble_rate_timer"
        };
        esp_timer_create(&rate_timer_args, &ble_rate_timer);
        esp_timer_start_periodic(ble_rate_timer, BLE_RATE_INTERVAL_MS * 1000);
    }
    
    // BLE only in normal mode, not setup mode
    if (!setup_mode) {
        // Start BLE stack, but do NOT start scanning automatically
        nimble_port_init();
        ble_hs_cfg.sync_cb = ble_app_on_sync;
        nimble_port_freertos_init(host_task);
        
        ESP_LOGI(TAG, "System ready. Scanning awaits user command.");
    } else {
        ESP_LOGI(TAG, "Setup mode active. BLE disabled.");
    }
    
    // Start UART console for factory reset command
    xTaskCreate(uart_console_task, "uart_console", 4096, NULL, 5, NULL);
}
