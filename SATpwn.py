import logging
import pwnagotchi.plugins as plugins
import pwnagotchi.ui.components as components
import pwnagotchi.ui.view as view
from flask import Response
import random
import json
import os
import time
from concurrent.futures import ThreadPoolExecutor

# TOML import with fallback for different Python versions
try:
    import tomllib  # Python 3.11+
except ImportError:
    try:
        import tomli as tomllib  # Fallback for older Python
    except ImportError:
        import toml as tomllib  # Alternative fallback

class SATpwn(plugins.Plugin):
    __author__ = 'Renmeii x Mr-Cass-Ette and discoJack too '
    __version__ = 'x88.0.7'
    __license__ = 'GPL3'
    __description__ = 'SATpwn intelligent targeting without GPS dependencies'
    
    # --- Constants for configuration ---
    AP_EXPIRY_SECONDS = 3600 * 48  # 48 hours
    CLIENT_EXPIRY_SECONDS = 3600 * 24  # 24 hours
    ATTACK_SCORE_THRESHOLD = 50
    ATTACK_COOLDOWN_SECONDS = 300  # 5 minutes
    SUCCESS_BONUS_DURATION_SECONDS = 1800  # 30 minutes
    SCORE_DECAY_PENALTY_PER_HOUR = 5  # Score penalty per hour
    PMKID_FRIENDLY_APS_THRESHOLD = 3
    PMKID_FRIENDLY_BOOST_FACTOR = 1.5
    HANDSHAKE_WEIGHT = 10
    CLIENT_WEIGHT = 1
    SCORE_RECALCULATION_INTERVAL_SECONDS = 30  # 30 seconds
    EXPLORATION_PROBABILITY = 0.1  # 10% chance to explore a random channel in loose mode
    DRIVE_BY_AP_EXPIRY_SECONDS = 1800  # 30 minutes
    DRIVE_BY_CLIENT_EXPIRY_SECONDS = 900  # 15 minutes
    DRIVE_BY_ATTACK_SCORE_THRESHOLD = 20 # Lower score threshold
    DRIVE_BY_ATTACK_COOLDOWN_SECONDS = 60  # 1 minute
    
    # AUTO Mode constants (time-based since no GPS)
    STATIONARY_SECONDS = 3600      # 1 hour to trigger "recon" mode
    ACTIVITY_THRESHOLD = 5         # Number of new APs to consider "moving"
    ACTIVITY_WINDOW_SECONDS = 300  # 5 minutes window for activity detection
    
    def __init__(self):
        self.ready = False
        self.agent = None
        self.memory = {}
        self.modes = ['strict', 'loose', 'drive-by', 'recon', 'auto']
        self.memory_path = '/etc/pwnagotchi/SATpwn_memory.json'
        self.executor = ThreadPoolExecutor(max_workers=5)
        self.mode = self.modes[0]  # Default mode, will be overridden by _load_memory()
        self.channel_stats = {}
        self.memory_is_dirty = True
        self.recon_channel_iterator = None
        self.recon_channels_tested = []
        
        # AUTO mode state (time-based without GPS)
        self._last_activity_check = 0
        self._activity_history = []  # Track AP discoveries over time
        self.home_whitelist = set()
        self._current_auto_submode = None  # Track what AUTO is currently running
        self._stationary_start = None  # When we first detected stationary state
        
        logging.info("[SATpwn] Plugin initializing without GPS dependencies...")
        self._load_home_whitelist()
    
    def _load_home_whitelist(self):
        """Load home SSID/BSSID whitelist with robust TOML parsing and format detection."""
        try:
            config_path = "/etc/pwnagotchi/config.toml"
            logging.debug(f"[SATpwn] Attempting to load config from: {config_path}")
            
            if not os.path.exists(config_path):
                logging.warning(f"[SATpwn] config.toml not found at {config_path}")
                self.home_whitelist = set()
                return
            
            # Detect TOML library and use appropriate mode
            try:
                # Check if this is the built-in tomllib (Python 3.11+) which requires binary mode
                if hasattr(tomllib, '__name__') and getattr(tomllib, '__name__', '') == 'tomllib':
                    open_mode = "rb"
                    logging.debug("[SATpwn] Using tomllib (Python 3.11+) with binary mode")
                else:
                    # This is tomli or toml - requires text mode
                    open_mode = "r"
                    logging.debug("[SATpwn] Using tomli/toml with text mode")
                
                with open(config_path, open_mode) as f:
                    conf = tomllib.load(f)
                
                logging.debug(f"[SATpwn] Config loaded successfully. Top-level keys: {list(conf.keys())}")
                
                # Try multiple ways to get the home whitelist
                home_whitelist = None
                
                # Method 1: Flat key format (jayofelony style)
                if 'main.home_whitelist' in conf:
                    home_whitelist = conf['main.home_whitelist']
                    logging.debug("[SATpwn] Found whitelist using flat key 'main.home_whitelist'")
                
                # Method 2: Nested table format
                elif 'main' in conf and isinstance(conf['main'], dict):
                    main_section = conf['main']
                    if 'home_whitelist' in main_section:
                        home_whitelist = main_section['home_whitelist']
                        logging.debug("[SATpwn] Found whitelist in [main] table under 'home_whitelist'")
                    elif 'whitelist' in main_section:
                        home_whitelist = main_section['whitelist']
                        logging.debug("[SATpwn] Found whitelist in [main] table under 'whitelist'")
                
                # Method 3: Direct top-level key
                elif 'home_whitelist' in conf:
                    home_whitelist = conf['home_whitelist']
                    logging.debug("[SATpwn] Found whitelist as top-level 'home_whitelist'")
                
                # Process the whitelist data
                if home_whitelist is not None:
                    # Handle different data types
                    if isinstance(home_whitelist, str):
                        # Split comma-separated string
                        home_list = [x.strip() for x in home_whitelist.split(',') if x.strip()]
                        logging.debug(f"[SATpwn] Parsed CSV string into list: {home_list}")
                    elif isinstance(home_whitelist, list):
                        home_list = [str(x).strip() for x in home_whitelist if str(x).strip()]
                        logging.debug(f"[SATpwn] Using list directly: {home_list}")
                    else:
                        logging.warning(f"[SATpwn] Unexpected whitelist format: {type(home_whitelist)}")
                        home_list = []
                    
                    if home_list:
                        self.home_whitelist = set(home_list)
                        logging.info(f"[SATpwn] Loaded home whitelist: {len(self.home_whitelist)} entries: {self.home_whitelist}")
                    else:
                        self.home_whitelist = set()
                        logging.warning("[SATpwn] Home whitelist was empty after processing")
                else:
                    self.home_whitelist = set()
                    logging.warning("[SATpwn] No home whitelist found in config file")
                
            except Exception as parse_error:
                logging.error(f"[SATpwn] Error parsing TOML config: {parse_error}")
                self.home_whitelist = set()
                
        except Exception as e:
            logging.error(f"[SATpwn] Could not load home whitelist from config: {e}")
            self.home_whitelist = set()
    
    def _update_activity_history(self, new_ap_count):
        """Track AP discovery activity over time for movement detection."""
        now = time.time()
        self._activity_history.append((now, new_ap_count))
        
        # Clean old entries outside the activity window
        cutoff = now - self.ACTIVITY_WINDOW_SECONDS
        self._activity_history = [(t, count) for t, count in self._activity_history if t > cutoff]
    
    def _is_stationary(self):
        """Check if device appears stationary based on AP discovery patterns."""
        now = time.time()
        
        # Calculate recent AP discovery rate
        recent_activity = sum(count for t, count in self._activity_history 
                             if now - t <= self.ACTIVITY_WINDOW_SECONDS)
        
        # Low activity suggests stationary behavior
        low_activity = recent_activity < self.ACTIVITY_THRESHOLD
        
        if low_activity:
            if self._stationary_start is None:
                self._stationary_start = now
                logging.debug("[SATpwn] Stationary state detected - starting timer")
            
            elapsed = now - self._stationary_start
            stationary = elapsed >= self.STATIONARY_SECONDS
            logging.debug(f"[SATpwn] Stationary check - elapsed: {elapsed:.0f}s, stationary: {stationary}")
            return stationary
        else:
            # Reset stationary timer if we see activity
            if self._stationary_start is not None:
                logging.debug("[SATpwn] Activity detected - resetting stationary timer")
                self._stationary_start = None
            return False
    
    def _is_moving(self):
        """Detect movement based on high AP discovery rate."""
        now = time.time()
        
        # Calculate recent AP discovery rate
        recent_activity = sum(count for t, count in self._activity_history 
                             if now - t <= self.ACTIVITY_WINDOW_SECONDS)
        
        moving = recent_activity >= self.ACTIVITY_THRESHOLD
        logging.debug(f"[SATpwn] Movement check - recent_activity: {recent_activity}, moving: {moving}")
        return moving
    
    def _home_ssid_visible(self):
        """Check if any home SSID/BSSID is currently visible with debug logging."""
        logging.debug(f"[SATpwn] Checking home whitelist: {self.home_whitelist}")
        logging.debug(f"[SATpwn] Current memory has {len(self.memory)} APs")
        
        if not self.home_whitelist:
            logging.debug("[SATpwn] Home whitelist is empty")
            return False
        
        visible_ssids = []
        for ap_mac, ap in self.memory.items():
            ssid = ap.get("ssid", "")
            visible_ssids.append(ssid)
            if ssid in self.home_whitelist or ap_mac in self.home_whitelist:
                logging.info(f"[SATpwn] Home SSID detected: '{ssid}' (MAC: {ap_mac})")
                return True
        
        logging.debug(f"[SATpwn] Visible SSIDs: {visible_ssids}")
        logging.debug("[SATpwn] No home SSID found in current scan")
        return False
    
    def _auto_mode_logic(self):
        """Decide sub-mode based on activity patterns and SSID visibility."""
        home_ssid_visible = self._home_ssid_visible()
        is_stationary = self._is_stationary()
        is_moving = self._is_moving()
        
        logging.debug(f"[SATpwn] AUTO logic - home_visible: {home_ssid_visible}, stationary: {is_stationary}, moving: {is_moving}")
        
        # Priority: Home > Stationary > Moving > Default
        if home_ssid_visible or is_stationary:
            return 'recon'  # Passive behavior when at home or stationary
        if is_moving:
            return 'drive-by'  # Aggressive mobile targeting
        
        # Default based on AP count
        return 'loose' if len(self.memory) < 10 else 'strict'
        
    def _save_memory(self):
        """Saves the current AP/client memory and current mode to a JSON file."""
        try:
            # Create a complete memory structure that includes metadata
            memory_data = {
                "plugin_metadata": {
                    "current_mode": self.mode,
                    "last_saved": time.time(),
                    "version": self.__version__,
                    "stationary_start": self._stationary_start
                },
                "ap_data": self.memory
            }
            
            with open(self.memory_path, 'w') as f:
                json.dump(memory_data, f, indent=4)
            logging.debug(f"[SATpwn] Memory and mode '{self.mode}' saved to {self.memory_path}")
        except Exception as e:
            logging.error(f"[SATpwn] Error saving memory: {e}")
    
    def _load_memory(self):
        """Loads the AP/client memory and restores the last saved mode from a JSON file."""
        if os.path.exists(self.memory_path):
            try:
                with open(self.memory_path, 'r') as f:
                    data = json.load(f)
                
                # Handle both old format (direct AP data) and new format (with metadata)
                if "plugin_metadata" in data:
                    # New format with metadata
                    metadata = data["plugin_metadata"]
                    self.memory = data.get("ap_data", {})
                    
                    # Restore the last saved mode
                    saved_mode = metadata.get("current_mode", self.modes[0])
                    if saved_mode in self.modes:
                        self.mode = saved_mode
                        logging.info(f"[SATpwn] Restored mode: {self.mode}")
                    else:
                        logging.warning(f"[SATpwn] Invalid saved mode '{saved_mode}', using default: {self.modes[0]}")
                        self.mode = self.modes[0]
                    
                    # Restore stationary timer if available
                    self._stationary_start = metadata.get("stationary_start", None)
                    if self._stationary_start:
                        logging.info(f"[SATpwn] Restored stationary timer")
                    
                    last_saved = metadata.get("last_saved", 0)
                    time_diff = time.time() - last_saved
                    logging.info(f"[SATpwn] Memory loaded from {self.memory_path} (last saved {time_diff:.0f}s ago)")
                else:
                    # Old format - just AP data
                    self.memory = data
                    self.mode = self.modes[0]  # Default to strict mode
                    logging.info(f"[SATpwn] Legacy memory format loaded, defaulting to mode: {self.mode}")
                    
            except Exception as e:
                logging.error(f"[SATpwn] Error loading memory: {e}")
                self.memory = {}
                self.mode = self.modes[0]
        else:
            logging.info("[SATpwn] No existing memory file found, starting fresh")
    
    def _cleanup_memory(self):
        """Removes old APs and clients from memory to keep it relevant."""
        self.memory_is_dirty = True
        now = time.time()
        ap_expiry = self.DRIVE_BY_AP_EXPIRY_SECONDS if self.mode == 'drive-by' else self.AP_EXPIRY_SECONDS
        client_expiry = self.DRIVE_BY_CLIENT_EXPIRY_SECONDS if self.mode == 'drive-by' else self.CLIENT_EXPIRY_SECONDS
        
        expired_aps = [ap_mac for ap_mac, data in self.memory.items()
                       if now - data.get("last_seen", 0) > ap_expiry]
        for ap_mac in expired_aps:
            if ap_mac in self.memory:
                del self.memory[ap_mac]
        
        for ap_mac in list(self.memory.keys()):
            if ap_mac not in self.memory:
                continue
                
            ap = self.memory[ap_mac]
            expired_clients = [client_mac for client_mac, client_data in ap.get("clients", {}).items()
                              if now - client_data.get("last_seen", 0) > client_expiry]
            for client_mac in expired_clients:
                if client_mac in ap["clients"]:
                    del ap["clients"][client_mac]
                    logging.debug(f"[SATpwn] Removed expired client {client_mac} from AP {ap_mac}")
        
        if expired_aps:
            logging.info(f"[SATpwn] Cleaned up {len(expired_aps)} expired APs from memory")
    
    def on_loaded(self):
        """Called when the plugin is loaded."""
        self._load_memory()
        logging.info(f"[SATpwn] Plugin loaded successfully. Current mode: {self.mode}")
    
    def on_ready(self, agent):
        """Called when the agent is ready."""
        self.agent = agent
        self.ready = True
        logging.info(f"[SATpwn] Plugin ready. Starting in {self.mode} mode.")
    
    def on_unfiltered_ap_list(self, agent, data):
        """Process WiFi AP scan results and update memory."""
        if not self.ready:
            return
        
        now = time.time()
        new_ap_count = 0
        
        # Check if we should update our activity check
        if now - self._last_activity_check > 30:  # Update every 30 seconds
            self._last_activity_check = now
            
        try:
            aps = data.get('wifi', {}).get('aps', [])
            for ap_data in aps:
                ap_mac = ap_data.get('mac', '').lower()
                if not ap_mac:
                    continue
                
                ssid = ap_data.get('hostname', '')
                rssi = ap_data.get('rssi', 0)
                channel = ap_data.get('channel', 0)
                encryption = ap_data.get('encryption', '')
                
                # Check if this is a new AP
                is_new_ap = ap_mac not in self.memory
                if is_new_ap:
                    new_ap_count += 1
                    logging.debug(f"[SATpwn] New AP discovered: {ssid} ({ap_mac})")
                
                # Update or create AP entry
                if ap_mac not in self.memory:
                    self.memory[ap_mac] = {
                        "ssid": ssid,
                        "first_seen": now,
                        "last_seen": now,
                        "rssi": rssi,
                        "channel": channel,
                        "encryption": encryption,
                        "clients": {},
                        "attack_history": [],
                        "handshakes": 0,
                        "pmkid_attempts": 0,
                        "score": 0
                    }
                    self.memory_is_dirty = True
                else:
                    # Update existing AP
                    ap_entry = self.memory[ap_mac]
                    ap_entry["last_seen"] = now
                    ap_entry["rssi"] = rssi
                    if ssid:  # Only update SSID if we have one
                        ap_entry["ssid"] = ssid
                
                # Process clients for this AP
                clients = ap_data.get('clients', [])
                for client_data in clients:
                    client_mac = client_data.get('mac', '').lower()
                    if not client_mac:
                        continue
                    
                    if client_mac not in self.memory[ap_mac]["clients"]:
                        self.memory[ap_mac]["clients"][client_mac] = {
                            "first_seen": now,
                            "last_seen": now,
                            "packets": 0
                        }
                        self.memory_is_dirty = True
                        logging.debug(f"[SATpwn] New client discovered: {client_mac} -> {ap_mac}")
                    else:
                        self.memory[ap_mac]["clients"][client_mac]["last_seen"] = now
            
            # Update activity history
            self._update_activity_history(new_ap_count)
            
            # Handle AUTO mode logic
            if self.mode == 'auto':
                new_submode = self._auto_mode_logic()
                if new_submode != self._current_auto_submode:
                    logging.info(f"[SATpwn] AUTO mode switching: {self._current_auto_submode} -> {new_submode}")
                    self._current_auto_submode = new_submode
            
        except Exception as e:
            logging.error(f"[SATpwn] Error processing AP list: {e}")
    
    def on_ui_update(self, ui):
        """Update the UI with current mode and stats."""
        if not self.ready:
            return
        
        try:
            # Display current mode and stats
            mode_display = self.mode
            if self.mode == 'auto' and self._current_auto_submode:
                mode_display = f"auto({self._current_auto_submode})"
            
            ap_count = len(self.memory)
            total_clients = sum(len(ap.get("clients", {})) for ap in self.memory.values())
            
            # Show activity indicator
            activity_indicator = ""
            if self._is_moving():
                activity_indicator = "📱"  # Moving
            elif self._is_stationary():
                activity_indicator = "🏠"  # Stationary
            elif self._home_ssid_visible():
                activity_indicator = "🏡"  # Home
            
            status_text = f"SATpwn:{mode_display} APs:{ap_count} Clients:{total_clients} {activity_indicator}"
            
            ui.set('SATpwn', status_text)
            
        except Exception as e:
            logging.error(f"[SATpwn] Error updating UI: {e}")
    
    def on_epoch(self, agent, epoch, epoch_data):
        """Called at the end of each epoch."""
        if not self.ready:
            return
        
        # Cleanup old entries periodically
        if epoch % 10 == 0:  # Every 10 epochs
            self._cleanup_memory()
        
        # Save memory if dirty
        if self.memory_is_dirty and epoch % 5 == 0:  # Every 5 epochs
            self._save_memory()
            self.memory_is_dirty = False
    
    def on_unload(self, ui):
        """Called when the plugin is being unloaded."""
        logging.info("[SATpwn] Plugin unloading...")
        if self.memory_is_dirty:
            self._save_memory()
        if hasattr(self, 'executor'):
            self.executor.shutdown(wait=True)
        logging.info("[SATpwn] Plugin unloaded successfully")
