import sys
import ctypes
import os
import json
import pygame
import cv2
from PIL import Image as PILImage
import math
from PyQt5.QtCore import Qt, QTimer, QPropertyAnimation, QEasingCurve, QPoint, QMimeData
from PyQt5.QtGui import QPixmap, QIcon, QFont, QImage, QDrag, QPainter, QColor
from PyQt5.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QFrame, QScrollArea, QTextEdit, QLineEdit, QSlider, QGridLayout,
    QShortcut, QSpinBox, QMessageBox, QListWidget, QListWidgetItem,
    QAbstractItemView, QSizePolicy, QDialog, QColorDialog
)

# --- Настройки ---
DATA_DIR = "data"
ICONS_DIR = "icons"
VIDEO_FOLDER = "background"
MUSIC_FOLDER = "music"  # ← ЕДИНСТВЕННАЯ ПАПКА МУЗЫКИ!
LOCALES_DIR = "locales"

# Создаем необходимые директории
os.makedirs(DATA_DIR, exist_ok=True)
for folder in [ICONS_DIR, VIDEO_FOLDER, MUSIC_FOLDER, "sounds", LOCALES_DIR]:
    os.makedirs(folder, exist_ok=True)

TASKS_FILE = os.path.join(DATA_DIR, "tasks.json")
NOTES_FILE = os.path.join(DATA_DIR, "notes.json")
NOISES_FILE = os.path.join(DATA_DIR, "noises.json")
PLAYLIST_FILE = os.path.join(DATA_DIR, "playlist.json")
PLAYER_STATE_FILE = os.path.join(DATA_DIR, "player_state.json")
KANBAN_FILE = os.path.join(DATA_DIR, "kanban.json")
LANGUAGE_FILE = os.path.join(DATA_DIR, "language.json")
BACKGROUND_FILE = os.path.join(DATA_DIR, "background.json")
KANBAN_COLUMNS_FILE = os.path.join(DATA_DIR, "kanban_columns.json")

# Создаем файлы, если их нет
for file_path in [TASKS_FILE, NOTES_FILE, NOISES_FILE, PLAYLIST_FILE, PLAYER_STATE_FILE, KANBAN_FILE]:
    if not os.path.exists(file_path):
        with open(file_path, "w", encoding="utf-8") as f:
            if "notes" in file_path or "tasks" in file_path:
                json.dump([], f)
            elif "kanban" in file_path:
                json.dump({"todo": [], "progress": [], "done": []}, f)
            else:
                json.dump({}, f)

# Создаем файл настроек колонок, если его нет
default_columns = [
    {"key": "todo", "title": "To Do", "color": [70, 130, 180]},
    {"key": "progress", "title": "In Progress", "color": [255, 165, 0]},
    {"key": "done", "title": "Done", "color": [50, 205, 50]}
]
if not os.path.exists(KANBAN_COLUMNS_FILE):
    with open(KANBAN_COLUMNS_FILE, "w", encoding="utf-8") as f:
        json.dump(default_columns, f, indent=2)

# --- Звук ---
pygame.mixer.init()
pygame.init()
SOUND_PATHS = {
    "tv": "sounds/tv.ogg",
    "fire": "sounds/fire.ogg",
    "wind": "sounds/wind.ogg",
    "rain": "sounds/rain.ogg",
    "timer_end": "sounds/timer_end.ogg"
}
sounds = {}
channels = {}
for name, path in SOUND_PATHS.items():
    if os.path.exists(path):
        try:
            sounds[name] = pygame.mixer.Sound(path)
            channels[name] = pygame.mixer.Channel(list(SOUND_PATHS.keys()).index(name))
            print(f"✅ Sound loaded: {name}")
        except Exception as e:
            print(f"❌ Failed to load sound {name}: {e}")

# --- Видео ---
VIDEO_PATH = None
for ext in [".mov", ".mp4", ".avi", ".mkv"]:
    candidate = os.path.join(VIDEO_FOLDER, f"bg{ext}")
    if os.path.exists(candidate):
        VIDEO_PATH = candidate
        print(f"✅ Found video: {candidate}")
        break

# === ОСНОВНОЕ ОКНО ===
class FloatingFocusApp(QWidget):
    def __init__(self):
        super().__init__()
        set_app_icon()
        self.setAcceptDrops(True)
        self.drag_pos = None
        self.notes_data = []
        self.track_list = []
        self.current_index = 0
        self.is_playing = False
        self.noises_volumes = {"tv": 0, "fire": 0, "wind": 0, "rain": 0}
        self.work_time = 25 * 60
        self.break_time = 5 * 60
        self.current_time = self.work_time
        self.timer_running = False
        self.timer = QTimer()
        self.timer.timeout.connect(self.update_timer)
        self.background_files = []
        self.background_index = 0
        self.current_track_position = 0.0
        # --- Загрузка данных ---
        self.load_data()
        # --- UI ---
        self.ICONS = {}
        self.translations = {}
        self.current_language = "ru"
        self.load_translations()
        self.load_data()
        self.load_icons()
        self.init_ui()
        # --- Инициализация таймера для видеофона ---
        self.video_timer = QTimer()
        self.video_timer.timeout.connect(self.update_video)
        self.load_backgrounds()
        self.load_video()
        # --- Запуск шумов ---
        self.start_permanent_noises()
        # --- Воспроизведение последнего трека ---
        if hasattr(self, 'last_played_track') and self.last_played_track:
            if self.last_played_track in self.track_list:
                self.current_index = self.track_list.index(self.last_played_track)
                self.update_track_label()
            else:
                self.current_index = 0
        else:
            self.current_index = 0
        self.update_timer_display()
        self.radial_menu_open = False
        self.radial_buttons = []
        self.setup_radial_menu()
        self.setup_todo_panel()
        self.setup_kanban_panel()
        self.setup_noises_panel()
        self.refresh_kanban_board()
        # --- ИНИЦИАЛИЗАЦИЯ РАДИАЛЬНОГО МЕНЮ НАСТРОЕК ---
        self.setup_settings_radial_menu()
        self.set_language(self.current_language)
        # --- Глобальный хоткей для паузы/воспроизведения на пробел ---
        self.shortcut_play_pause = QShortcut(" ", self)
        self.shortcut_play_pause.activated.connect(self.play_pause)
        self.pygame_timer = QTimer()
        self.pygame_timer.timeout.connect(self.check_pygame_events)
        self.pygame_timer.start(100)

    def check_pygame_events(self):
        """Проверяет события pygame (например, окончание трека) и обрабатывает их."""
        for event in pygame.event.get():
            if event.type == pygame.USEREVENT + 1:  # Событие окончания музыки
                self.handle_music_end()

    def load_translations(self):
        """Загружает все файлы локализации из папки `locales`."""
        supported_languages = ["ru", "en", "cn", "jp", "es"]
        for lang in supported_languages:
            file_path = os.path.join(LOCALES_DIR, f"{lang}.json")
            if os.path.exists(file_path):
                try:
                    with open(file_path, "r", encoding="utf-8") as f:
                        self.translations[lang] = json.load(f)
                except Exception as e:
                    print(f"❌ Ошибка загрузки перевода {lang}: {e}")
            else:
                print(f"⚠️ Файл перевода не найден: {file_path}")

    def start_permanent_noises(self):
        """Запускает шумы, если громкость > 0"""
        for name in self.noises_volumes:
            if self.noises_volumes[name] > 0 and name in sounds:
                vol = self.noises_volumes[name] / 100
                channels[name].play(sounds[name], loops=-1)
                sounds[name].set_volume(vol)

    def load_icons(self):
        icon_map = {
            "play": (24, 24),
            "pause": (24, 24),
            "arrow_up": (20, 20),
            "arrow_down": (20, 20),
            "reset": (24, 24),
            "settings": (24, 24),
            "notes": (32, 32),
            "playlist": (32, 32),
            "noises": (32, 32),
            "close": (24, 24),
            "add": (24, 24),
            "delete": (20, 20),
            "prev": (24, 24),
            "next": (24, 24),
            "todo": (32, 32),
            "kanban": (32, 32),
            "add_task": (32, 32),
            "delete_task": (24, 24),
            "checkbox_unchecked": (20, 20),
            "checkbox_checked": (20, 20),
            "close_panel": (24, 24),
            "help": (24, 24),
            "noise_tv": (40, 40),
            "noise_fire": (40, 40),
            "volume": (20, 20),
            "noise_wind": (40, 40),
            "noise_rain": (40, 40),
            "radial_menu": (32, 32),
            "menu": (32, 32),
            "settings_background": (32, 32),
            "settings_language": (32, 32),
            "settings_exit": (32, 32),
        }
        for name, size in icon_map.items():
            path = os.path.join(ICONS_DIR, f"{name}.png")
            if os.path.exists(path):
                try:
                    pil_img = PILImage.open(path).convert("RGBA")
                    pil_img = pil_img.resize(size, PILImage.Resampling.LANCZOS)
                    data = pil_img.tobytes("raw", "RGBA")
                    qimage = QImage(data, pil_img.size[0], pil_img.size[1], QImage.Format_RGBA8888)
                    self.ICONS[name] = QPixmap.fromImage(qimage)
                except Exception as e:
                    print(f"❌ Failed to load icon {name}: {e}")
            else:
                self.ICONS[name] = None

    def init_ui(self):
        self.setWindowFlags(Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground, True)
        self.setWindowTitle("Project focus")
        self.setWindowIcon(QIcon(os.path.join(ICONS_DIR, "app_icon.png")))
        screen = QApplication.primaryScreen()
        geometry = screen.geometry()
        self.resize(geometry.width(), geometry.height())
        self.shortcut_fullscreen = QShortcut("F11", self)
        self.shortcut_fullscreen.activated.connect(self.toggle_fullscreen)
        self.background_label = QLabel(self)
        self.background_label.setGeometry(0, 0, self.width(), self.height())
        self.background_label.setStyleSheet("background-color: transparent;")
        self.setup_timer_panel()
        self.setup_player()
        self.setup_noises_button()
        self.setup_notes_button()
        self.setup_notes_panel()
        self.setup_playlist_panel()
        self.setup_library_panel()
        self.update_timer_display()

    def toggle_fullscreen(self):
        if self.isFullScreen():
            self.showNormal()
            screen = QApplication.primaryScreen()
            geometry = screen.geometry()
            self.resize(geometry.width(), geometry.height())
        else:
            self.showFullScreen()

    def setup_timer_panel(self):
        self.timer_frame = QFrame(self)
        self.timer_frame.setFixedWidth(300)
        self.timer_frame.setStyleSheet("background-color: transparent; border: none;")
        self.timer_frame.hide()
        layout = QGridLayout(self.timer_frame)
        layout.setContentsMargins(40, 40, 40, 40)
        layout.setSpacing(2)
        self.timer_label = QLabel("25:00")
        self.timer_label.setFont(QFont("Digital-7", 32))
        self.timer_label.setStyleSheet("color: white;")
        self.timer_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(self.timer_label, 0, 0, 1, 3)
        self.play_btn = self.create_icon_button(self.ICONS.get("play"), self.toggle_timer)
        self.reset_btn = self.create_icon_button(self.ICONS.get("reset"), self.reset_timer)
        self.settings_btn = self.create_icon_button(self.ICONS.get("settings"), self.toggle_settings)
        for btn in [self.play_btn, self.reset_btn, self.settings_btn]:
            btn.setFixedSize(36, 36)
            btn.setStyleSheet("""
                QPushButton {
                    background: transparent;
                    border: none;
                    padding: 0;
                    margin: 0;
                }
                QPushButton:hover {
                    background: rgba(100, 100, 150, 0);
                    border-radius: 12px;
                }
            """)
        layout.addWidget(self.play_btn, 1, 0, Qt.AlignCenter)
        layout.addWidget(self.reset_btn, 1, 1, Qt.AlignCenter)
        layout.addWidget(self.settings_btn, 1, 2, Qt.AlignCenter)
        # --- ИНИЦИАЛИЗАЦИЯ settings_layout ---
        self.settings_panel = QFrame()
        settings_layout = QVBoxLayout(self.settings_panel)
        # --- КОНЕЦ ИНИЦИАЛИЗАЦИИ ---
        # --- ЗАМЕНА СТАНДАРТНЫХ КНОПОК SPINBOX НА КАСТОМНЫЕ ---
        work_layout = QHBoxLayout()
        work_label = QLabel("work")
        work_label.setStyleSheet("""
            color: white;
            font-size: 18px;
            font-weight: bold;
            padding: 1px 0;
        """)
        self.work_label = work_label
        work_layout.addWidget(work_label)
        work_container = QWidget()
        work_container_layout = QHBoxLayout(work_container)
        work_container_layout.setContentsMargins(0, 0, 0, 0)
        work_container_layout.setSpacing(2)
        self.work_spin = QSpinBox()
        self.work_spin.setFixedWidth(80)
        self.work_spin.setFixedHeight(40)
        self.work_spin.setStyleSheet("""
            QSpinBox {
                font-size: 18px;
                min-height: 40px;
                padding: 1px;
                border: 1px solid rgba(255,255,255,0);
                border-radius: 8px;
                background: rgba(255, 255, 255, 0);
                color: white;
            }
            QSpinBox::up-button, QSpinBox::down-button {
                width: 0px;
                background: none;
                border: none;
                margin: 0px;
            }
        """)
        self.work_spin.setRange(1, 120)
        self.work_spin.setValue(self.work_time // 60)
        self.work_spin.valueChanged.connect(self.update_work_time)
        work_container_layout.addWidget(self.work_spin)
        work_up_btn = self.create_icon_button(self.ICONS.get("arrow_up"), lambda: self.work_spin.setValue(self.work_spin.value() + 1))
        work_up_btn.setFixedSize(20, 20)
        work_up_btn.setStyleSheet("QPushButton { background: transparent; border: none; }")
        work_down_btn = self.create_icon_button(self.ICONS.get("arrow_down"), lambda: self.work_spin.setValue(self.work_spin.value() - 1))
        work_down_btn.setFixedSize(20, 20)
        work_down_btn.setStyleSheet("QPushButton { background: transparent; border: none; }")
        work_container_layout.addWidget(work_up_btn)
        work_container_layout.addWidget(work_down_btn)
        work_layout.addWidget(work_container)
        settings_layout.addLayout(work_layout)
        # BREAK SPINBOX
        break_layout = QHBoxLayout()
        break_label = QLabel("break")
        break_label.setStyleSheet("""
            color: white;
            font-size: 18px;
            font-weight: bold;
            padding: 2px 0;
        """)
        self.break_label = break_label
        break_layout.addWidget(break_label)
        break_container = QWidget()
        break_container_layout = QHBoxLayout(break_container)
        break_container_layout.setContentsMargins(0, 0, 0, 0)
        break_container_layout.setSpacing(2)
        self.break_spin = QSpinBox()
        self.break_spin.setFixedWidth(80)
        self.break_spin.setFixedHeight(40)
        self.break_spin.setStyleSheet("""
            QSpinBox {
                font-size: 18px;
                min-height: 40px;
                padding: 1px;
                border: 1px solid rgba(255,255,255,0);
                border-radius: 8px;
                background: rgba(255, 255, 255, 0);
                color: white;
            }
            QSpinBox::up-button, QSpinBox::down-button {
                width: 0px;
                background: none;
                border: none;
                margin: 0px;
            }
        """)
        self.break_spin.setRange(1, 60)
        self.break_spin.setValue(self.break_time // 60)
        self.break_spin.valueChanged.connect(self.update_break_time)
        break_container_layout.addWidget(self.break_spin)
        break_up_btn = self.create_icon_button(self.ICONS.get("arrow_up"), lambda: self.break_spin.setValue(self.break_spin.value() + 1))
        break_up_btn.setFixedSize(20, 20)
        break_up_btn.setStyleSheet("QPushButton { background: transparent; border: none; }")
        break_down_btn = self.create_icon_button(self.ICONS.get("arrow_down"), lambda: self.break_spin.setValue(self.break_spin.value() - 1))
        break_down_btn.setFixedSize(20, 20)
        break_down_btn.setStyleSheet("QPushButton { background: transparent; border: none; }")
        break_container_layout.addWidget(break_up_btn)
        break_container_layout.addWidget(break_down_btn)
        break_layout.addWidget(break_container)
        settings_layout.addLayout(break_layout)
        self.settings_panel.hide()
        layout.addWidget(self.settings_panel, 2, 0, 1, 3)

    def update_work_time(self, value):
        self.work_time = value * 60
        if not self.timer_running:
            self.current_time = self.work_time
            self.update_timer_display()

    def update_break_time(self, value):
        self.break_time = value * 60

    def toggle_settings(self):
        if self.settings_panel.isVisible():
            self.settings_panel.hide()
        else:
            self.settings_panel.show()
        self.timer_frame.layout().activate()
        self.timer_frame.adjustSize()

    def update_timer_display(self):
        m, s = divmod(self.current_time, 60)
        self.timer_label.setText(f"{m:02}:{s:02}")

    def update_timer(self):
        if self.current_time > 0:
            self.current_time -= 1
            self.update_timer_display()
        else:
            self.timer.stop()
            self.timer_running = False
            self.play_btn.setIcon(QIcon(self.ICONS["play"]))
            if "timer_end" in sounds:
                channels["timer_end"].play(sounds["timer_end"])
            self.current_time = self.break_time
            self.update_timer_display()

    def toggle_timer(self):
        if self.timer_running:
            self.timer.stop()
            self.timer_running = False
            self.play_btn.setIcon(QIcon(self.ICONS["play"]))
        else:
            self.timer.start(1000)
            self.timer_running = True
            self.play_btn.setIcon(QIcon(self.ICONS["pause"]))

    def reset_timer(self):
        self.timer.stop()
        self.timer_running = False
        self.current_time = self.work_time
        self.update_timer_display()
        self.play_btn.setIcon(QIcon(self.ICONS["play"]))

    def setup_player(self):
        self.player_frame = QFrame(self)
        self.player_frame.setFixedHeight(60)
        self.player_frame.setStyleSheet("""
            background-color: transparent;
            border: 0px solid rgba(255, 255, 255, 30);
            border-radius: 12px;
        """)
        self.player_frame.resize(600, 60)
        self.player_frame.hide()
        layout = QHBoxLayout(self.player_frame)
        layout.setContentsMargins(10, 10, 10, 10)
        btn_layout = QHBoxLayout()
        playlist_btn = self.create_icon_button(self.ICONS.get("playlist"), self.toggle_playlist_panel)
        self.play_btn_player = self.create_icon_button(self.ICONS.get("play"), self.play_pause)
        prev_btn = self.create_icon_button(self.ICONS.get("prev"), self.prev_track)
        next_btn = self.create_icon_button(self.ICONS.get("next"), self.next_track)
        for btn in [playlist_btn, prev_btn, self.play_btn_player, next_btn]:
            btn.setFixedSize(40, 40)
            btn_layout.addWidget(btn)
        layout.addLayout(btn_layout)
        self.track_label = QLabel("🎵 Player")
        self.track_label.setStyleSheet("color: white;")
        layout.addWidget(self.track_label)
        vol_label = QLabel()
        pixmap = self.ICONS.get("volume")
        if pixmap:
            vol_label.setPixmap(pixmap.scaled(20, 20, Qt.KeepAspectRatio, Qt.SmoothTransformation))
        else:
            vol_label.setText("🔊")
            vol_label.setStyleSheet("color: white;")
        vol_label.setFixedWidth(20)
        vol_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(vol_label)
        self.music_volume = QSlider(Qt.Horizontal)
        self.music_volume.setRange(0, 100)
        self.music_volume.setValue(50)
        self.music_volume.setFixedWidth(100)
        self.music_volume.valueChanged.connect(lambda v: pygame.mixer.music.set_volume(v / 100))
        pygame.mixer.music.set_volume(0.7)
        self.music_volume.setStyleSheet("""
            QSlider {
                height: 30px;
            }
            QSlider::groove:horizontal {
                border: 1px solid #999999;
                height: 8px;
                background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #B1B1B1, stop:1 #c4c4c4);
                margin: 2px 0;
                border-radius: 4px;
            }
            QSlider::handle:horizontal {
                background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 #14e2c3, stop:1 #149ae2);
                border: 1px solid #5c5c5c;
                width: 18px;
                margin: -2px 0;
                border-radius: 3px;
            }
        """)
        layout.addWidget(self.music_volume)
        pygame.mixer.music.set_endevent(pygame.USEREVENT + 1)

    def play_pause(self):
        if not self.track_list:
            return
        path = self.track_list[self.current_index]
        if not os.path.exists(path):
            return
        if self.is_playing:
            self.current_track_position = pygame.mixer.music.get_pos() / 1000.0
            pygame.mixer.music.pause()
            self.is_playing = False
            self.play_btn_player.setIcon(QIcon(self.ICONS["play"]))
        else:
            if pygame.mixer.music.get_busy():
                pygame.mixer.music.play(start=self.current_track_position)
            else:
                try:
                    pygame.mixer.music.load(path)
                    pygame.mixer.music.play(start=self.current_track_position)
                except Exception as e:
                    print(f"Ошибка воспроизведения: {e}")
                    return
            self.is_playing = True
            self.play_btn_player.setIcon(QIcon(self.ICONS["pause"]))
        self.update_track_label()

    def update_track_label(self):
        if self.track_list:
            name = os.path.basename(self.track_list[self.current_index])
            name = os.path.splitext(name)[0].replace('_', ' ')
            self.track_label.setText(name[:30] + "..." if len(name) > 30 else name)

    def prev_track(self):
        if not self.track_list:
            return
        self.current_index = (self.current_index - 1) % len(self.track_list)
        try:
            pygame.mixer.music.load(self.track_list[self.current_index])
            pygame.mixer.music.play()
            self.is_playing = True
            self.play_btn_player.setIcon(QIcon(self.ICONS["pause"]))
            self.update_track_label()
            self.current_track_position = 0.0
        except Exception as e:
            print(e)

    def next_track(self):
        if not self.track_list:
            return
        self.current_index = (self.current_index + 1) % len(self.track_list)
        try:
            pygame.mixer.music.load(self.track_list[self.current_index])
            pygame.mixer.music.play()
            self.is_playing = True
            self.play_btn_player.setIcon(QIcon(self.ICONS["pause"]))
            self.update_track_label()
        except Exception as e:
            print(e)

    def handle_music_end(self):
        if self.is_playing and self.track_list:
            self.next_track()

    def setup_noises_button(self):
        self.noises_btn = self.create_icon_button(self.ICONS.get("noises"), self.toggle_noises_panel)
        self.noises_btn.setFixedSize(50, 50)
        self.noises_btn.setStyleSheet("""
            QPushButton {
                background: rgba(50, 50, 70, 0);
                border: none;
                border-radius: 25px;
            }
            QPushButton:hover {
                background: rgba(80, 80, 120, 0);
            }
        """)
        self.noises_btn.hide()

    def setup_notes_button(self):
        if self.ICONS.get("notes") is None:
            self.notes_btn = QPushButton("📝", self)
            self.notes_btn.setStyleSheet("color: white;")
        else:
            self.notes_btn = self.create_icon_button(self.ICONS.get("notes"), self.toggle_notes_panel)
        self.notes_btn.setFixedSize(40, 40)
        self.notes_btn.hide()

    def setup_notes_panel(self):
        self.notes_panel = QFrame(self)
        self.notes_panel.setFixedWidth(300)
        self.notes_panel.setStyleSheet("""
            background-color: rgba(30, 30, 40, 0);
            border: 1px solid rgba(255, 255, 255, 30);
            border-radius: 12px;
        """)
        self.notes_panel.hide()
        layout = QVBoxLayout(self.notes_panel)
        layout.setContentsMargins(10, 10, 10, 10)
        title = QLabel(" Заметки")
        title.setFont(QFont("Segoe UI", 14, QFont.Bold))
        title.setStyleSheet("color: white;")
        layout.addWidget(title)
        self.close_notes_btn = QPushButton("✕", self)
        self.close_notes_btn.setFixedSize(24, 24)
        self.close_notes_btn.setParent(self.notes_panel)
        self.close_notes_btn.move(266, 10)
        self.close_notes_btn.setStyleSheet("""
            QPushButton {
                background: transparent;
                color: white;
                border: none;
                font: bold;
                font-size: 14px;
            }
            QPushButton:hover {
                background: rgba(255, 0, 0, 0);
                border-radius: 12px;
            }
        """)
        self.close_notes_btn.clicked.connect(self.toggle_notes_panel)
        self.notes_text = QTextEdit()
        self.notes_text.setStyleSheet("""
            background: rgba(0, 0, 0, 50);
            color: white;
            border-radius: 8px;
            padding: 8px;
            font-size: 20px;
        """)
        self.notes_text.setFont(QFont("Segoe UI", 12))
        self.notes_text.setPlainText("".join([n.get("content", "") for n in self.notes_data]) or "...")
        self.notes_text.textChanged.connect(self.save_notes)
        layout.addWidget(self.notes_text)

    def save_notes(self):
        text = self.notes_text.toPlainText()
        self.notes_data = [{"content": line} for line in text.split('\n') if line.strip()]
        self.save_data()

    def toggle_notes_panel(self):
        if self.notes_panel.isVisible():
            self.notes_panel.hide()
        else:
            btn_rect = self.notes_btn.geometry()
            x = btn_rect.left() + btn_rect.width() + 10
            y = btn_rect.top()
            if x + 300 > self.width():
                x = self.width() - 310
            self.notes_panel.move(1550, 425)
            self.notes_panel.show()
            self.close_notes_btn.raise_()

    def setup_playlist_panel(self):
        self.playlist_panel = QFrame(self)
        self.playlist_panel.setFixedWidth(515)
        self.playlist_panel.setStyleSheet("""
            background-color: rgba(30, 30, 40, 0);
            border: 1px solid rgba(100, 100, 150, 0);
            border-radius: 1px;
        """)
        self.playlist_panel.hide()
        layout = QVBoxLayout(self.playlist_panel)
        layout.setContentsMargins(10, 10, 10, 10)
        title = QLabel("         Текущий плейлист")
        title.setStyleSheet("color: white; font-weight: bold;")
        layout.addWidget(title)
        # === НОВЫЙ: QListWidget вместо вертикального лейаута ===
        self.playlist_list = QListWidget()
        self.playlist_list.setStyleSheet("""
            QListWidget {
                background: rgba(0, 0, 0, 50);
                color: white;
                border-radius: 8px;
                border: 1px solid rgba(100, 100, 150, 100);
                padding: 5px;
            }
            QListWidget::item {
                padding: 8px 10px;
                margin: 2px 0;
                border-radius: 6px;
                background: rgba(255, 255, 255, 5);
            }
            QListWidget::item:selected {
                background: rgba(20, 200, 195, 30);
                border: 1px solid rgba(20, 200, 195, 80);
            }
            QListWidget::item:hover {
                background: rgba(255, 255, 255, 10);
            }
        """)
        self.playlist_list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.playlist_list.setDragDropMode(QAbstractItemView.InternalMove)
        self.playlist_list.setDefaultDropAction(Qt.MoveAction)
        self.playlist_list.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
        self.playlist_list.setMaximumHeight(320)
        self.playlist_list.setMinimumHeight(180)
        self.playlist_list.model().rowsMoved.connect(self.on_playlist_reordered)
        layout.addWidget(self.playlist_list)
        tr = self.translations.get(self.current_language, {})
        open_lib_btn = QPushButton(f" {tr.get('library_open_button', 'Открыть библиотеку')}")
        open_lib_btn.setStyleSheet("""
            QPushButton {
                background: rgba(255, 0, 0, 0);
                color: white;
                padding: 10px;
                border-radius: 8px;
                font-size: 14px;
            }
            QPushButton:hover {
                background: rgba(20, 20, 20, 20);
            }
        """)
        open_lib_btn.clicked.connect(self.toggle_library_panel)
        layout.addWidget(open_lib_btn)
        self.refresh_playlist()

    def toggle_playlist_panel(self):
        if self.playlist_panel.isVisible():
            self.playlist_panel.hide()
        else:
            player_height = self.player_frame.height()
            panel_height = 450
            y = self.height() - player_height - panel_height - 20
            if y < 20:
                y = 20
            x = 30
            self.playlist_panel.move(x-12, y-35)
            self.playlist_panel.show()

    def setup_library_panel(self):
        self.library_panel = QFrame(self)
        self.library_panel.setFixedWidth(505)
        self.library_panel.setStyleSheet("background: rgba(30, 30, 40, 0); border-radius: 12px;")
        self.library_panel.hide()
        layout = QVBoxLayout(self.library_panel)
        layout.setContentsMargins(10, 10, 10, 10)
        title = QLabel("Библиотека треков")
        title.setStyleSheet("color: white; font-weight: bold;")
        layout.addWidget(title)
        scroll = QScrollArea()
        scroll.verticalScrollBar().setStyleSheet("""
            QScrollBar:vertical {
                background: rgba(30, 30, 40, 0);
                width: 16px;
                margin: 16px 0 16px 0;
                border-radius: 8px;
            }
            QScrollBar::handle:vertical {
                background: qlineargradient(
                    x1:0, y1:0, x2:1, y2:0,
                    stop:0 #14e2c3, stop:1 #149ae2
                );
                min-height: 40px;
                border-radius: 8px;
                margin: 0 2px;
            }
            QScrollBar::handle:vertical:hover {
                background: qlineargradient(
                    x1:0, y1:0, x2:1, y2:0,
                    stop:0 #14ffc3, stop:1 #14aee2
                );
                border-radius: 8px;
            }
            QScrollBar::add-line:vertical, 
            QScrollBar::sub-line:vertical {
                height: 0px;
                background: none;
                border: none;
            }
            QScrollBar::add-page:vertical, 
            QScrollBar::sub-page:vertical {
                background: none;
            }
        """)
        self.library_content = QFrame()
        self.library_layout = QVBoxLayout(self.library_content)
        scroll.setWidget(self.library_content)
        scroll.setWidgetResizable(True)
        layout.addWidget(scroll)
        self.refresh_library()

    def toggle_library_panel(self):
        if self.library_panel.isVisible():
            self.library_panel.hide()
        else:
            playlist_rect = self.playlist_panel.geometry()
            x = playlist_rect.right() + 10
            y = playlist_rect.top()
            if x + 500 > self.width():
                x = self.width() - 510
            self.library_panel.move(x, y-10)
            self.library_panel.show()

    def refresh_library(self):
        for i in reversed(range(self.library_layout.count())):
            item = self.library_layout.itemAt(i)
            if item:
                widget = item.widget()
                if widget:
                    widget.setParent(None)
        if not os.path.exists(MUSIC_FOLDER):
            os.makedirs(MUSIC_FOLDER)
        files = []
        for file in os.listdir(MUSIC_FOLDER):
            if file.lower().endswith(('.ogg', '.mp3', '.wav')):
                path = os.path.join(MUSIC_FOLDER, file)
                files.append(path)
        for path in files:
            filename = os.path.basename(path)
            display_name = os.path.splitext(filename)[0].replace('_', ' ')
            row = QHBoxLayout()
            lbl = QLabel(display_name)
            lbl.setStyleSheet("color: white; padding: 2px;")
            row.addWidget(lbl)
            row.addStretch()
            if path not in self.track_list:
                btn = QPushButton("+")
                btn.setFixedSize(28, 28)
                btn.setStyleSheet("background: rgba(255,255,255,0); color: white; border-radius: 12px;")
                btn.clicked.connect(lambda _, p=path: self.add_to_playlist(p))
            else:
                btn = QPushButton("−")
                btn.setFixedSize(28, 28)
                btn.setStyleSheet("background: rgba(255,255,255,0); color: white; border-radius: 12px;")
                btn.clicked.connect(lambda _, p=path: self.remove_from_playlist(p))
            row.addWidget(btn)
            frame = QFrame()
            frame.setLayout(row)
            self.library_layout.addWidget(frame)

    def add_to_playlist(self, path):
        if path not in self.track_list:
            self.track_list.append(path)
            self.refresh_library()
            self.refresh_playlist()
            self.save_data()

    def remove_from_playlist(self, path):
        if path in self.track_list:
            self.track_list.remove(path)
            self.refresh_library()
            self.refresh_playlist()
            self.save_data()

    def refresh_playlist(self):
        self.playlist_list.clear()
        # Берём последние 7 треков (новые — в конце списка), но отображаем их в обратном порядке → новые сверху
        recent_tracks = self.track_list[-7:] if len(self.track_list) > 7 else self.track_list
        for path in reversed(recent_tracks):  # ← Важно! Отображаем в обратном порядке
            filename = os.path.basename(path)
            display_name = os.path.splitext(filename)[0].replace('_', ' ')
            item = QListWidgetItem(display_name)
            item.setData(Qt.UserRole, path)
            self.playlist_list.addItem(item)
        # Выделяем текущий трек
        if self.track_list and self.current_index < len(self.track_list):
            current_path = self.track_list[self.current_index]
            for i in range(self.playlist_list.count()):
                item = self.playlist_list.item(i)
                if item.data(Qt.UserRole) == current_path:
                    self.playlist_list.setCurrentRow(i)
                    break

    def on_playlist_reordered(self, parent, start, end, destination, row):
        new_order = []
        for i in range(self.playlist_list.count()):
            item = self.playlist_list.item(i)
            path = item.data(Qt.UserRole)
            if path:
                new_order.append(path)
        filtered_track_list = [p for p in self.track_list if p in new_order]
        final_order = []
        for path in new_order:
            if path not in final_order:
                final_order.append(path)
        self.track_list = final_order
        if hasattr(self, 'current_index') and self.current_index < len(self.track_list):
            current_path = self.track_list[self.current_index]
            self.current_index = self.track_list.index(current_path)
        self.save_data()

    def setup_noises_panel(self):
        self.noises_panel = DraggableFrame(self)
        self.noises_panel.setFixedSize(360, 300)
        self._panel_color = QColor(30, 30, 40, 0)
        self.update_noises_panel_style()
        main_layout = QVBoxLayout(self.noises_panel)
        main_layout.setContentsMargins(20, 20, 20, 20)
        main_layout.setSpacing(15)
        header = QHBoxLayout()
        tr = self.translations.get(self.current_language, {})
        title = QLabel(tr.get("noises_panel_title", "Ambient noises"))
        title.setFont(QFont("Segoe UI", 14, QFont.Bold))
        title.setStyleSheet("color: rgba(220, 220, 255, 240);")
        header.addWidget(title)
        close_btn = QPushButton("✕")
        close_btn.setFixedSize(28, 28)
        close_btn.setStyleSheet("""
            QPushButton {
                background: rgba(210, 60, 60, 0);
                color: white;
                border-radius: 14px;
                font-weight: bold;
                font-size: 16px;
                border: 1px solid rgba(170, 40, 40, 0);
            }
            QPushButton:hover {
                background: rgba(255, 70, 70, 0);
                border: 1px solid rgba(220, 50, 50, 0);
            }
        """)
        close_btn.clicked.connect(self.hide_noises_panel)
        header.addWidget(close_btn)
        main_layout.addLayout(header)
        noises_layout = QVBoxLayout()
        noises_layout.setSpacing(25)
        noises_config = [
            ("tv", "📺", "noise_tv"),
            ("fire", "🔥", "noise_fire"),
            ("wind", "🌬️", "noise_wind"),
            ("rain", "🌧️", "noise_rain")
        ]
        self.noise_sliders = {}
        for name, emoji, icon_key in noises_config:
            row_layout = QHBoxLayout()
            row_layout.setSpacing(15)
            row_layout.setAlignment(Qt.AlignVCenter)
            icon_label = QLabel()
            pixmap = self.ICONS.get(icon_key)
            if pixmap:
                icon_label.setPixmap(pixmap.scaled(40, 40, Qt.KeepAspectRatio, Qt.SmoothTransformation))
            else:
                icon_label.setText(emoji)
                icon_label.setStyleSheet("font-size: 22px; color: white;")
            icon_label.setAlignment(Qt.AlignCenter)
            icon_label.setFixedSize(44, 44)
            row_layout.addWidget(icon_label, alignment=Qt.AlignVCenter)
            slider = QSlider(Qt.Horizontal)
            slider.setRange(0, 100)
            slider.setValue(int(self.noises_volumes.get(name, 0)))
            slider.valueChanged.connect(lambda v, n=name: self.set_noise_volume(n, v))
            slider.setStyleSheet("""
                QSlider {
                    height: 30px;
                }
                QSlider::groove:horizontal {
                    border: 1px solid #999999;
                    height: 8px;
                    background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 #B1B1B1, stop:1 #c4c4c4);
                    margin: 2px 0;
                    border-radius: 4px;
                }
                QSlider::handle:horizontal {
                    background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 #14e2c3, stop:1 #149ae2);
                    border: 1px solid #5c5c5c;
                    width: 18px;
                    margin: -2px 0;
                    border-radius: 3px;
                }
            """)
            row_layout.addWidget(slider, 1)
            value_label = QLabel(f"{slider.value()}%")
            value_label.setAlignment(Qt.AlignCenter)
            value_label.setStyleSheet("color: rgba(200, 200, 200, 220); font-size: 12px; min-width: 40px;")
            row_layout.addWidget(value_label, alignment=Qt.AlignVCenter)
            slider.value_label = value_label
            slider.valueChanged.connect(lambda v, lbl=value_label: lbl.setText(f"{v}%"))
            self.noise_sliders[name] = slider
            noises_layout.addLayout(row_layout)
        main_layout.addLayout(noises_layout)
        self.noises_panel.hide()

    def update_noises_panel_style(self):
        self.noises_panel.setStyleSheet(f"""
            DraggableFrame {{
                background: rgba({self._panel_color.red()}, {self._panel_color.green()}, {self._panel_color.blue()}, {self._panel_color.alpha()});
                border: 1px solid rgba(100, 100, 150, 100);
                border-radius: 20px;
            }}
        """)

    def move_noises_panel(self, x, y):
        if hasattr(self, 'noises_panel'):
            self.noises_panel.move(x, y)

    def argb(self, a, r, g, b):
        self._panel_color = QColor(r, g, b, a)
        self.update_noises_panel_style()

    def toggle_noises_panel(self):
        if self.noises_panel.isVisible():
            self.hide_noises_panel()
        else:
            self.show_noises_panel()

    def show_noises_panel(self):
        if hasattr(self, 'noises_btn'):
            btn_rect = self.noises_btn.geometry()
            x = btn_rect.left() - self.noises_panel.width() - 20
            y = btn_rect.top() + (btn_rect.height() - self.noises_panel.height()) // 2
            if x < 20:
                x = 20
            if y < 20:
                y = 20
            self.noises_panel.move(x, y-125)
        else:
            self.noises_panel.move(self.width() - 400, self.height() - 350)
        self.noises_panel.show()
        self.noises_panel.raise_()

    def hide_noises_panel(self):
        self.noises_panel.hide()

    def set_noise_volume(self, name, value):
        vol = value / 100.0
        self.noises_volumes[name] = int(value)
        if name in sounds:
            sounds[name].set_volume(vol)
            if vol > 0:
                if not channels[name].get_busy():
                    channels[name].play(sounds[name], loops=-1)
            else:
                channels[name].stop()
        self.save_data()

    def create_icon_button(self, pixmap, callback):
        btn = QPushButton(self)
        if pixmap:
            btn.setIcon(QIcon(pixmap))
            btn.setIconSize(pixmap.size())
        btn.clicked.connect(callback)
        btn.setStyleSheet("""
            QPushButton {
                background: transparent;
                border: none;
            }
            QPushButton:hover {
                background: rgba(100, 100, 150, 0);
                border-radius: 12px;
            }
        """)
        return btn

    # ============ TO-DO LIST С ИКОНКАМИ ============
    def setup_todo_panel(self):
        self.todo_panel = DraggableFrame(self)
        self.todo_panel.setFixedSize(360, 480)
        self.todo_panel.setStyleSheet("""
            DraggableFrame {
                background: qlineargradient(
                    x1: 0, y1: 0, x2: 0, y2: 1,
                    stop: 0 rgba(45, 45, 60, 00),
                    stop: 1 rgba(25, 25, 40, 50)
                );
                border: 1px solid rgba(100, 100, 100, 255);
                border-radius: 20px;
            }
        """)
        layout = QVBoxLayout(self.todo_panel)
        layout.setContentsMargins(20, 20, 20, 20)
        header = QHBoxLayout()
        title = QLabel(" To-Do List")
        title.setFont(QFont("Segoe UI", 16, QFont.Bold))
        title.setStyleSheet("color: rgba(230, 230, 255, 250);")
        header.addWidget(title)
        close_icon = self.ICONS.get("close_panel")
        if close_icon:
            close_btn = self.create_icon_button(close_icon, self.hide_todo_panel)
            close_btn.setFixedSize(30, 30)
            close_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(210, 60, 60, 0);
                    border-radius: 15px;
                    border: 1px solid rgba(170, 40, 40, 0);
                }
                QPushButton:hover {
                    background: rgba(255, 70, 70, 0);
                    border: 1px solid rgba(220, 50, 50, 0);
                }
            """)
        else:
            close_btn = QPushButton("✕")
            close_btn.setFixedSize(30, 30)
            close_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(210, 60, 60, 190);
                    color: white;
                    border-radius: 15px;
                    font-weight: bold;
                    font-size: 16px;
                    border: 1px solid rgba(170, 40, 40, 160);
                }
                QPushButton:hover {
                    background: rgba(255, 70, 70, 230);
                    border: 1px solid rgba(220, 50, 50, 200);
                }
            """)
            close_btn.clicked.connect(self.hide_todo_panel)
        header.addWidget(close_btn)
        layout.addLayout(header)
        input_layout = QHBoxLayout()
        self.todo_input = QLineEdit()
        tr = self.translations.get(self.current_language, {})
        self.todo_input.setPlaceholderText(f"✍️ {tr.get('todo_input_placeholder', 'Введите задачу...')}")
        self.todo_input.setStyleSheet("""
            QLineEdit {
                background: rgba(255, 255, 255, 25);
                border: 2px solid rgba(120, 150, 255, 100);
                border-radius: 12px;
                color: white;
                padding: 12px;
                font-size: 14px;
                selection-background-color: rgba(100, 150, 255, 180);
            }
            QLineEdit:focus {
                border: 2px solid rgba(140, 180, 255, 180);
                background: rgba(255, 255, 255, 35);
            }
        """)
        input_layout.addWidget(self.todo_input)
        add_icon = self.ICONS.get("add_task")
        if add_icon:
            add_btn = self.create_icon_button(add_icon, self.add_todo_task)
            add_btn.setFixedSize(40, 40)
            add_btn.setStyleSheet("""
                QPushButton {
                    background: qlineargradient(
                        x1: 0, y1: 0, x2: 0, y2: 1,
                        stop: 0 rgba(60, 160, 80, 0),
                        stop: 1 rgba(40, 130, 60, 0)
                    );
                    border-radius: 20px;
                    border: 2px solid rgba(50, 140, 70, 0);
                }
                QPushButton:hover {
                    background: qlineargradient(
                        x1: 0, y1: 0, x2: 0, y2: 1,
                        stop: 0 rgba(70, 190, 90, 0),
                        stop: 1 rgba(50, 160, 70, 0)
                    );
                    border: 2px solid rgba(70, 180, 90, 0);
                }
            """)
        else:
            tr = self.translations.get(self.current_language, {})
            add_btn.setToolTip(tr.get('todo_add_button_tooltip', 'Add Task'))
            add_btn.setFixedSize(40, 40)
            add_btn.setStyleSheet("""
                QPushButton {
                    background: qlineargradient(
                        x1: 0, y1: 0, x2: 0, y2: 1,
                        stop: 0 rgba(60, 160, 80, 230),
                        stop: 1 rgba(40, 130, 60, 230)
                    );
                    color: white;
                    border-radius: 20px;
                    font-weight: bold;
                    font-size: 20px;
                    border: 2px solid rgba(50, 140, 70, 180);
                }
                QPushButton:hover {
                    background: qlineargradient(
                        x1: 0, y1: 0, x2: 0, y2: 1,
                        stop: 0 rgba(70, 190, 90, 250),
                        stop: 1 rgba(50, 160, 70, 250)
                    );
                    border: 2px solid rgba(70, 180, 90, 220);
                }
                QPushButton:pressed {
                    background: rgba(60, 160, 80, 210);
                }
            """)
            add_btn.clicked.connect(self.add_todo_task)
        input_layout.addWidget(add_btn)
        layout.addLayout(input_layout)
        self.todo_list = QWidget()
        self.todo_layout = QVBoxLayout(self.todo_list)
        self.todo_layout.setAlignment(Qt.AlignTop)
        self.todo_layout.setSpacing(12)
        scroll = QScrollArea()
        scroll.setWidget(self.todo_list)
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("QScrollArea { border: none; background: transparent; }")
        scroll.viewport().setStyleSheet("background: transparent;")
        scroll.verticalScrollBar().setStyleSheet("""
            QScrollBar:vertical {
                background: rgba(255, 255, 255, 25);
                width: 12px;
                border-radius: 6px;
                margin: 2px;
            }
            QScrollBar::handle:vertical {
                background: rgba(255, 255, 255, 120);
                min-height: 30px;
                border-radius: 6px;
            }
            QScrollBar::handle:vertical:hover {
                background: rgba(255, 255, 255, 180);
            }
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
                height: 0px;
            }
        """)
        layout.addWidget(scroll)
        self.refresh_todo_list()
        self.todo_panel.hide()

    def add_todo_task(self):
        text = self.todo_input.text().strip()
        if not text:
            return
        for col in self.kanban_columns.keys():
            if text in self.kanban_data.get(col, []):
                self.kanban_data[col].remove(text)
        self.tasks_data.append({"text": text, "completed": False})
        self.kanban_data["progress"].append(text)
        self.todo_input.clear()
        self.refresh_todo_list()
        self.refresh_kanban_board()
        self.save_data()

    def remove_todo_task(self, index):
        if 0 <= index < len(self.tasks_data):
            del self.tasks_data[index]
            self.refresh_todo_list()
            self.save_data()

    def toggle_todo_task(self, index, state):
        if not (0 <= index < len(self.tasks_data)):
            return
        task = self.tasks_data[index]
        task_text = task["text"]
        task["completed"] = state
        for col in self.kanban_columns.keys():
            if task_text in self.kanban_data.get(col, []):
                self.kanban_data[col].remove(task_text)
        if state:
            self.kanban_data["done"].append(task_text)
        else:
            self.kanban_data["progress"].append(task_text)
        self.refresh_todo_list()
        self.refresh_kanban_board()
        self.save_data()

    def refresh_todo_list(self):
        while self.todo_layout.count():
            item = self.todo_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        for i, task in enumerate(self.tasks_data):
            task_widget = QFrame()
            task_widget.setObjectName("taskFrame")
            task_widget.setStyleSheet("""
                QFrame#taskFrame {
                    background: rgba(255, 255, 255, 10);
                    border: 1px solid rgba(255, 255, 255, 30);
                    border-radius: 12px;
                    padding: 8px;
                    margin: 4px 0;
                }
                QFrame#taskFrame:hover {
                    background: rgba(255, 255, 255, 20);
                    border: 1px solid rgba(200, 220, 255, 80);
                }
            """)
            task_layout = QHBoxLayout(task_widget)
            task_layout.setContentsMargins(10, 8, 10, 8)
            checkbox_container = QPushButton()
            checkbox_container.setFixedSize(24, 24)
            if task["completed"]:
                icon = self.ICONS.get("checkbox_checked")
            else:
                icon = self.ICONS.get("checkbox_unchecked")
            if icon:
                checkbox_container.setIcon(QIcon(icon))
                checkbox_container.setIconSize(icon.size())
            else:
                checkbox_container.setText("✓" if task["completed"] else "□")
                checkbox_container.setStyleSheet("font-size: 16px;")
            checkbox_container.setStyleSheet("""
                QPushButton {
                    background: transparent;
                    border: none;
                }
                QPushButton:hover {
                    background: rgba(255, 255, 255, 20);
                    border-radius: 6px;
                }
            """)
            checkbox_container.clicked.connect(lambda _, idx=i: self.toggle_todo_task(idx, not self.tasks_data[idx]["completed"]))
            text_label = QLabel(task["text"])
            text_label.setWordWrap(True)
            text_label.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Minimum)
            text_label.setMinimumWidth(100)
            text_label.setMaximumWidth(16777215)
            text_label.setWordWrap(True)
            text_label.setAlignment(Qt.AlignLeft | Qt.AlignTop)
            text_label.setStyleSheet(f"""
                color: {'rgba(180, 180, 180, 200)' if task['completed'] else 'white'};
                text-decoration: {'line-through' if task['completed'] else 'none'};
                font-size: 14px;
            """)
            delete_icon = self.ICONS.get("delete_task")
            if delete_icon:
                delete_btn = self.create_icon_button(delete_icon, lambda _, idx=i: self.remove_todo_task(idx))
                delete_btn.setFixedSize(28, 28)
                delete_btn.setStyleSheet("""
                    QPushButton {
                        background: transparent;
                        border: none;
                    }
                    QPushButton:hover {
                        background: rgba(255, 120, 120, 40);
                        border-radius: 8px;
                    }
                """)
            else:
                delete_btn = QPushButton("🗑")
                delete_btn.setFixedSize(28, 28)
                delete_btn.setStyleSheet("""
                    QPushButton {
                        background: transparent;
                        color: rgba(255, 120, 120, 0);
                        border: none;
                        font-size: 14px;
                    }
                    QPushButton:hover {
                        background: rgba(255, 120, 120, 40);
                        color: rgba(255, 100, 100, 255);
                        border-radius: 8px;
                    }
                """)
                delete_btn.clicked.connect(lambda _, idx=i: self.remove_todo_task(idx))
            task_layout.addWidget(checkbox_container)
            task_layout.addWidget(text_label, 1)
            task_layout.addWidget(delete_btn)
            self.todo_layout.addWidget(task_widget)

    def show_todo_panel(self):
        if self.todo_panel.isVisible():
            self.hide_todo_panel()
        else:
            self.todo_panel.move(20, 160)
            self.todo_panel.show()
            self.todo_panel.raise_()

    def hide_todo_panel(self):
        self.todo_panel.hide()

    # ============ KANBAN BOARD ============
    def setup_kanban_panel(self):
        self.kanban_panel = DraggableFrame(self)
        self.kanban_panel.resize(740, 540)
        self.kanban_panel.setStyleSheet("""
            DraggableFrame {
                background: qlineargradient(
                    x1: 0, y1: 0, x2: 1, y2: 1,
                    stop: 0 rgba(35, 35, 50, 40),
                    stop: 1 rgba(20, 20, 35, 40)
                );
                border: 1px solid rgba(255, 255, 255, 50);
                border-radius: 22px;
            }
        """)
        main_layout = QVBoxLayout(self.kanban_panel)
        main_layout.setContentsMargins(20, 20, 20, 20)
        header = QHBoxLayout()
        title = QLabel("Kanban Board")
        title.setFont(QFont("Segoe UI", 16, QFont.Bold))
        title.setStyleSheet("color: rgba(230, 230, 255, 250);")
        header.addWidget(title)
        help_icon = self.ICONS.get("help")
        if help_icon:
            help_btn = self.create_icon_button(help_icon, self.show_kanban_help)
            help_btn.setFixedSize(30, 30)
            help_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(80, 120, 200, 0);
                    border-radius: 15px;
                    border: 1px solid rgba(60, 100, 180, 0);
                }
                QPushButton:hover {
                    background: rgba(100, 140, 255, 0);
                    border: 1px solid rgba(80, 120, 220, 220);
                }
            """)
        else:
            tr = self.translations.get(self.current_language, {})
            help_btn.setToolTip(tr.get('kanban_help_button_tooltip', 'Help'))
            help_btn.setFixedSize(30, 30)
            help_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(80, 120, 200, 0);
                    color: white;
                    border-radius: 15px;
                    font-weight: bold;
                    font-size: 14px;
                    border: 1px solid rgba(60, 100, 180, 0);
                }
                QPushButton:hover {
                    background: rgba(100, 140, 255, 0);
                    border: 1px solid rgba(80, 120, 220, 0);
                }
            """)
            help_btn.clicked.connect(self.show_kanban_help)
        header.addWidget(help_btn)
        settings_icon = self.ICONS.get("settings")
        if settings_icon:
            settings_btn = self.create_icon_button(settings_icon, self.open_kanban_settings)
            settings_btn.setFixedSize(30, 30)
            settings_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(80, 120, 200, 0);
                    border-radius: 15px;
                    border: 1px solid rgba(60, 100, 180, 0);
                }
                QPushButton:hover {
                    background: rgba(100, 140, 255, 0);
                    border: 1px solid rgba(80, 120, 220, 220);
                }
            """)
        else:
            settings_btn = QPushButton("⚙️")
            settings_btn.setFixedSize(30, 30)
            settings_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(80, 120, 200, 0);
                    color: white;
                    border-radius: 15px;
                    font-weight: bold;
                    font-size: 14px;
                    border: 1px solid rgba(60, 100, 180, 0);
                }
                QPushButton:hover {
                    background: rgba(100, 140, 255, 0);
                    border: 1px solid rgba(80, 120, 220, 0);
                }
            """)
            settings_btn.clicked.connect(self.open_kanban_settings)
        header.addWidget(settings_btn)
        close_icon = self.ICONS.get("close_panel")
        if close_icon:
            close_btn = self.create_icon_button(close_icon, self.hide_kanban_panel)
            close_btn.setFixedSize(30, 30)
            close_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(210, 60, 60, 0);
                    border-radius: 15px;
                    border: 1px solid rgba(170, 40, 40, 0);
                }
                QPushButton:hover {
                    background: rgba(255, 70, 70, 0);
                    border: 1px solid rgba(220, 50, 50, 0);
                }
            """)
        else:
            close_btn = QPushButton("✕")
            close_btn.setFixedSize(30, 30)
            close_btn.setStyleSheet("""
                QPushButton {
                    background: rgba(210, 60, 60, 0);
                    color: white;
                    border-radius: 15px;
                    font-weight: bold;
                    font-size: 16px;
                    border: 1px solid rgba(170, 40, 40, 0);
                }
                QPushButton:hover {
                    background: rgba(255, 70, 70, 0);
                    border: 1px solid rgba(220, 50, 50, 0);
                }
            """)
            close_btn.clicked.connect(self.hide_kanban_panel)
        header.addWidget(close_btn)
        main_layout.addLayout(header)
        self.columns_layout = QHBoxLayout()
        self.columns_layout.setSpacing(15)
        self.columns_layout.setAlignment(Qt.AlignLeft)
        main_layout.addLayout(self.columns_layout)
        self.kanban_columns = {}
        self.create_kanban_columns_from_settings()
        self.kanban_panel.hide()

    def create_kanban_column(self, title, color, key="custom"):
        frame = QFrame()
        frame.setStyleSheet(f"""
            background-color: rgba({color.red()}, {color.green()}, {color.blue()}, 50);
            border: 1px solid rgba({color.red()}, {color.green()}, {color.blue()}, 150);
            border-radius: 2px;
        """)
        layout = QVBoxLayout(frame)
        layout.setContentsMargins(10, 10, 10, 10)
        tr = self.translations.get(self.current_language, {})
        column_key_map = {
            "To Do": "kanban_column_todo",
            "In Progress": "kanban_column_progress",
            "Done": "kanban_column_done"
        }
        if key in ["todo", "progress", "done"]:
            translated_title = tr.get(column_key_map.get(title, ""), title)
        else:
            translated_title = title
        label = QLabel(translated_title)
        label.setFont(QFont("Segoe UI", 12, QFont.Bold))
        label.setStyleSheet(f"color: rgba({color.red()}, {color.green()}, {color.blue()}, 255);")
        label.setAlignment(Qt.AlignCenter)
        layout.addWidget(label)
        container = KanbanDropContainer(self, key)
        container_layout = QVBoxLayout(container)
        container_layout.setAlignment(Qt.AlignTop)
        container_layout.setSpacing(8)
        container.setLayout(container_layout)
        scroll = QScrollArea()
        scroll.setWidget(container)
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("QScrollArea { border: none; background: transparent; }")
        scroll.viewport().setStyleSheet("background: transparent;")
        frame.list_layout = container_layout
        frame.column_name = key
        frame.container = container
        layout.addWidget(scroll)
        add_task_layout = QHBoxLayout()
        add_task_layout.addStretch()
        add_task_btn = QPushButton("+")
        add_task_btn.setFixedSize(30, 30)
        add_task_btn.setStyleSheet(f"""
            QPushButton {{
                background: rgba({color.red()}, {color.green()}, {color.blue()}, 100);
                color: white;
                border: none;
                border-radius: 15px;
                font-size: 18px;
                font-weight: bold;
            }}
            QPushButton:hover {{
                background: rgba({color.red()}, {color.green()}, {color.blue()}, 180);
            }}
        """)
        add_task_btn.clicked.connect(lambda _, col_key=key: self.show_add_task_input(col_key))
        add_task_layout.addWidget(add_task_btn)
        add_task_layout.addStretch()
        layout.addLayout(add_task_layout)
        return frame

    def create_kanban_columns_from_settings(self):
        try:
            with open(KANBAN_COLUMNS_FILE, "r", encoding="utf-8") as f:
                columns_config = json.load(f)
        except Exception as e:
            print(f"Ошибка загрузки настроек колонок: {e}")
            columns_config = [
                {"key": "todo", "title": "To Do", "color": [70, 130, 180]},
                {"key": "progress", "title": "In Progress", "color": [255, 165, 0]},
                {"key": "done", "title": "Done", "color": [50, 205, 50]}
            ]
        while self.columns_layout.count():
            item = self.columns_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        self.kanban_columns = {}
        for col_config in columns_config:
            key = col_config.get("key", "unknown")
            title = col_config.get("title", key.capitalize())
            color_rgb = col_config.get("color", [100, 100, 100])
            color = QColor(*color_rgb)
            column_frame = self.create_kanban_column(title, color, key=key)
            column_frame.column_key = key
            column_frame.column_title = title
            column_frame.column_color = color
            self.kanban_columns[key] = column_frame
            self.columns_layout.addWidget(column_frame)
        self.adjust_kanban_panel_width()

    def adjust_kanban_panel_width(self):
        if not hasattr(self, 'columns_layout') or not self.kanban_columns:
            return
        base_width = 40
        column_width = 240
        spacing = 15
        num_columns = len(self.kanban_columns)
        total_width = base_width + (column_width * num_columns) + (spacing * (num_columns - 1))
        max_width = self.width() - 40
        final_width = min(total_width, max_width)
        for frame in self.kanban_columns.values():
            frame.setFixedWidth(column_width)
        self.kanban_panel.setFixedWidth(final_width)

    def refresh_kanban_board(self):
        for key in self.kanban_columns.keys():
            frame = self.kanban_columns[key]
            layout = frame.list_layout
            while layout.count():
                item = layout.takeAt(0)
                if item.widget():
                    item.widget().deleteLater()
        for key in self.kanban_columns.keys():
            frame = self.kanban_columns[key]
            layout = frame.list_layout
            seen = set()
            for task_text in self.kanban_data.get(key, []):
                if task_text in seen:
                    continue
                seen.add(task_text)
                task_widget = QFrame()
                task_widget.setStyleSheet("""
                    QFrame {
                        background: rgba(255, 255, 255, 10);
                        border: 1px solid rgba(255, 255, 255, 30);
                        border-radius: 10px;
                        padding: 8px;
                        margin: 4px 0;
                    }
                    QFrame:hover {
                        background: rgba(255, 255, 255, 20);
                        border: 1px solid rgba(200, 220, 255, 80);
                    }
                """)
                task_layout = QHBoxLayout(task_widget)
                task_layout.setContentsMargins(10, 8, 10, 8)
                if hasattr(self, 'file_paths') and task_text in self.file_paths:
                    file_path = self.file_paths[task_text]
                    if file_path.lower().endswith(('.png', '.jpg', '.jpeg', '.bmp', '.gif', '.webp')):
                        pixmap = QPixmap(file_path)
                        if not pixmap.isNull():
                            pixmap = pixmap.scaled(40, 40, Qt.KeepAspectRatio, Qt.SmoothTransformation)
                            image_label = QLabel()
                            image_label.setPixmap(pixmap)
                            image_label.setFixedSize(40, 40)
                            image_label.setStyleSheet("border: 1px solid rgba(255,255,255,50); border-radius: 4px;")
                            task_layout.addWidget(image_label)
                    text_label = QLabel(task_text)
                    text_label.setWordWrap(True)
                    text_label.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Minimum)
                    text_label.setMinimumWidth(100)
                    text_label.setMaximumWidth(16777215)
                    text_label.setWordWrap(True)
                    text_label.setAlignment(Qt.AlignLeft | Qt.AlignTop)
                    if key == "done":
                        text_label.setStyleSheet("color: rgba(180, 180, 180, 220); text-decoration: line-through;")
                    else:
                        text_label.setStyleSheet("color: white;")
                    task_layout.addWidget(text_label, 1)
                else:
                    text_label = QLabel(task_text)
                    text_label.setWordWrap(True)
                    text_label.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Minimum)
                    text_label.setMinimumWidth(100)
                    text_label.setMaximumWidth(16777215)
                    text_label.setWordWrap(True)
                    text_label.setAlignment(Qt.AlignLeft | Qt.AlignTop)
                    if key == "done":
                        text_label.setStyleSheet("color: rgba(180, 180, 180, 220); text-decoration: line-through;")
                    else:
                        text_label.setStyleSheet("color: white;")
                    task_layout.addWidget(text_label, 1)
                delete_btn = QPushButton()
                delete_icon = self.ICONS.get("delete_task")
                if delete_icon:
                    delete_btn.setIcon(QIcon(delete_icon))
                    delete_btn.setIconSize(delete_icon.size())
                else:
                    delete_btn.setText("🗑️")
                    delete_btn.setStyleSheet("font-size: 14px;")
                delete_btn.setFixedSize(28, 28)
                delete_btn.setStyleSheet("""
                    QPushButton {
                        background: transparent;
                        border: none;
                    }
                    QPushButton:hover {
                        background: rgba(255, 100, 100, 40);
                        border-radius: 8px;
                    }
                """)
                delete_btn.clicked.connect(lambda _, t=task_text: self.remove_kanban_task(t))
                task_widget.task_text = task_text
                task_widget.startPos = None
                def make_mouse_events(widget, col_name):
                    def mousePressEvent(event):
                        if event.button() == Qt.LeftButton:
                            widget.startPos = event.pos()
                        event.accept()
                    def mouseMoveEvent(event):
                        if event.buttons() == Qt.LeftButton and widget.startPos:
                            if (event.pos() - widget.startPos).manhattanLength() > 20:
                                drag = QDrag(widget)
                                mime_data = QMimeData()
                                mime_data.setText(f"{widget.task_text}|{col_name}")
                                drag.setMimeData(mime_data)
                                pixmap = QPixmap(widget.size())
                                widget.render(pixmap)
                                drag.setPixmap(pixmap)
                                drag.setHotSpot(event.pos() - widget.rect().topLeft())
                                drag.exec_(Qt.MoveAction)
                    widget.mousePressEvent = mousePressEvent
                    widget.mouseMoveEvent = mouseMoveEvent
                make_mouse_events(task_widget, key)
                task_layout.addWidget(delete_btn)
                layout.addWidget(task_widget)

    def show_kanban_help(self):
        tr = self.translations.get(self.current_language, self.translations.get("ru", {}))
        help_text = tr.get("kanban_help_text", """
📌 <b>Как пользоваться Kanban Board</b>
1. <b>Добавление задачи</b>
   — Пока задачи можно добавлять только через To-Do List.
   — Откройте To-Do List через радиальное меню (кнопка в левом верхнем углу).
   — Добавьте задачу — она появится в колонке "To Do".
2. <b>Перемещение задач</b>
   — Нажмите на задачу в любой колонке.
   — Перетащите её в другую колонку: 
        • "To Do" → ещё не начата
        • "In Progress" → в работе
        • "Done" → завершена
3. <b>Настройка доски</b>
   — Нажмите ⚙️ для добавления, удаления, переименования колонок и выбора их цвета.
4. <b>Сохранение</b>
   — Все изменения сохраняются автоматически.
        """)
        title = tr.get("kanban_help_title", "Помощь по Kanban")
        QMessageBox.information(self, title, help_text)

    def show_kanban_panel(self):
        if self.kanban_panel.isVisible():
            self.hide_kanban_panel()
        else:
            self.kanban_panel.move(160, 20)
            self.kanban_panel.show()
            self.kanban_panel.raise_()

    def hide_kanban_panel(self):
        self.kanban_panel.hide()

    def remove_kanban_task(self, task_text):
        for col in self.kanban_columns.keys():
            if task_text in self.kanban_data.get(col, []):
                self.kanban_data[col].remove(task_text)
        self.tasks_data = [task for task in self.tasks_data if task["text"] != task_text]
        if hasattr(self, 'file_paths') and task_text in self.file_paths:
            del self.file_paths[task_text]
        self.refresh_todo_list()
        self.refresh_kanban_board()
        self.save_data()

    # ============ РАДИАЛЬНОЕ МЕНЮ НАСТРОЕК ============
    def setup_settings_radial_menu(self):
        settings_icon = self.ICONS.get("settings")
        self.settings_radial_trigger_btn = self.create_icon_button(settings_icon, self.toggle_settings_radial_menu)
        self.settings_radial_trigger_btn.setFixedSize(50, 50)
        self.settings_radial_trigger_btn.setStyleSheet("""
            QPushButton {
                background: transparent;
                border: none;
            }
            QPushButton:hover {
                background: rgba(70, 70, 100, 180);
                border: 1px solid rgba(120, 120, 180, 180);
                border-radius: 25px;
            }
        """)
        if not settings_icon:
            self.settings_radial_trigger_btn.setText("⚙️")
        self.settings_radial_buttons = []
        bg_btn = self.create_radial_button("settings_background", " Фон", self.handle_background_setting)
        self.settings_radial_buttons.append(bg_btn)
        lang_btn = self.create_radial_button("settings_language", " Язык", self.handle_language_setting)
        self.settings_radial_buttons.append(lang_btn)
        exit_btn = self.create_radial_button("settings_exit", " Выход", self.handle_exit_setting)
        self.settings_radial_buttons.append(exit_btn)
        for btn in self.settings_radial_buttons:
            btn.hide()
            btn.setParent(self)
        self.settings_radial_trigger_btn.setParent(self)
        self.settings_radial_trigger_btn.move(self.width() // 2 - 25, 20)
        self.settings_radial_trigger_btn.raise_()
        self.settings_radial_trigger_btn.show()
        self.settings_radial_menu_open = False

    def toggle_settings_radial_menu(self):
        if self.settings_radial_menu_open:
            self.hide_settings_radial_menu()
        else:
            self.show_settings_radial_menu()

    def show_settings_radial_menu(self):
        if self.settings_radial_menu_open:
            self.hide_settings_radial_menu()
            return
        center_x = self.settings_radial_trigger_btn.x() + self.settings_radial_trigger_btn.width() // 2
        center_y = self.settings_radial_trigger_btn.y() + self.settings_radial_trigger_btn.height() // 2
        radius = 80
        angles = [220, 270, 320]
        for i, btn in enumerate(self.settings_radial_buttons):
            angle_rad = math.radians(angles[i])
            x = center_x + radius * math.cos(angle_rad) - btn.width() // 2
            y = center_y - radius * math.sin(angle_rad) - btn.height() // 2
            btn.move(int(x), int(y))
            btn.show()
            btn.raise_()
        self.settings_radial_menu_open = True
        self.settings_overlay = QWidget(self)
        self.settings_overlay.setGeometry(0, 0, self.width(), self.height())
        self.settings_overlay.setStyleSheet("background: transparent;")
        self.settings_overlay.mousePressEvent = lambda e: self.hide_settings_radial_menu()
        self.settings_overlay.show()
        self.settings_overlay.raise_()
        self.settings_radial_trigger_btn.raise_()
        for btn in self.settings_radial_buttons:
            btn.raise_()

    def hide_settings_radial_menu(self):
        if not self.settings_radial_menu_open:
            return
        for btn in self.settings_radial_buttons:
            btn.hide()
        self.settings_radial_menu_open = False
        if hasattr(self, 'settings_overlay'):
            self.settings_overlay.close()
            self.settings_overlay.deleteLater()
            del self.settings_overlay

    def handle_background_setting(self):
        self.next_background()

    def handle_language_setting(self):
        dialog = QDialog(self)
        tr = self.translations.get(self.current_language, self.translations.get("ru", {}))
        dialog.setWindowTitle(tr.get("language_dialog_title", "Choose Language"))
        dialog.setFixedSize(400, 200)
        layout = QGridLayout(dialog)
        languages = [
            ("🇷🇺", "ru", "Русский"),
            ("🇺🇸", "en", "English"),
            ("🇨🇳", "cn", "中文"),
            ("🇯🇵", "jp", "日本語"),
            ("🇪🇸", "es", "Español")
        ]
        row, col = 0, 0
        for flag, code, name in languages:
            btn = QPushButton(f"{flag} {name}")
            btn.setFixedSize(120, 40)
            btn.setStyleSheet("""
                QPushButton {
                    background: rgba(50, 50, 70, 180);
                    color: white;
                    border: 1px solid rgba(100, 100, 150, 180);
                    border-radius: 8px;
                    font-size: 14px;
                }
                QPushButton:hover {
                    background: rgba(70, 70, 100, 220);
                    border: 1px solid rgba(120, 120, 180, 220);
                }
            """)
            btn.clicked.connect(lambda _, c=code: self._set_language_and_close_dialog(c, dialog))
            layout.addWidget(btn, row, col)
            col += 1
            if col > 1:
                col = 0
                row += 1
        dialog.exec_()

    def _set_language_and_close_dialog(self, lang_code, dialog):
        self.set_language(lang_code)
        dialog.accept()

    def handle_exit_setting(self):
        self.close()

    # ============ РАДИАЛЬНОЕ МЕНЮ ============
    def setup_radial_menu(self):
        radial_icon = self.ICONS.get("radial_menu") or self.ICONS.get("menu") or self.ICONS.get("settings")
        self.radial_trigger_btn = self.create_icon_button(radial_icon, self.toggle_radial_menu)
        self.radial_trigger_btn.setFixedSize(50, 50)
        self.radial_trigger_btn.setStyleSheet("""
            QPushButton {
                background: rgba(50, 50, 70, 0);
                border: 1px solid rgba(100, 100, 150, 0);
                border-radius: 25px;
            }
            QPushButton:hover {
                background: rgba(70, 70, 100, 0);
                border: 1px solid rgba(120, 120, 180, 0);
            }
        """)
        if not radial_icon:
            self.radial_trigger_btn.setText("●")
        todo_btn = self.create_radial_button("todo", " To-Do", self.show_todo_panel)
        kanban_btn = self.create_radial_button("kanban", " Kanban", self.show_kanban_panel)
        self.radial_buttons = [todo_btn, kanban_btn]
        for btn in self.radial_buttons:
            btn.hide()
            btn.setParent(self)
        self.radial_trigger_btn.setParent(self)
        self.radial_trigger_btn.move(20, 20)
        self.radial_trigger_btn.raise_()
        self.radial_trigger_btn.show()

    def create_radial_button(self, icon_name, tooltip_text, callback):
        if self.ICONS.get(icon_name):
            btn = self.create_icon_button(self.ICONS.get(icon_name), callback)
        else:
            btn = QPushButton(tooltip_text.split()[0], self)
            btn.clicked.connect(callback)
        btn.setFixedSize(50, 50)
        btn.setToolTip(tooltip_text)
        btn.setStyleSheet("""
            QPushButton {
                background: rgba(50, 50, 70, 0);
                border: 2px solid rgba(80, 80, 120, 0);
                border-radius: 25px;
                color: white;
                font-weight: bold;
            }
            QPushButton:hover {
                background: rgba(80, 80, 120, 0);
                border: 2px solid rgba(100, 140, 255, 0);
            }
        """)
        btn.hide()
        return btn

    def toggle_radial_menu(self):
        if self.radial_menu_open:
            self.hide_radial_menu()
        else:
            self.show_radial_menu()

    def show_radial_menu(self):
        if self.radial_menu_open:
            self.hide_radial_menu()
            return
        center_x = self.radial_trigger_btn.x() + self.radial_trigger_btn.width() // 2
        center_y = self.radial_trigger_btn.y() + self.radial_trigger_btn.height() // 2
        radius = 80
        angles = [270, 360]
        for i, btn in enumerate(self.radial_buttons):
            angle_rad = math.radians(angles[i])
            x = center_x + radius * math.cos(angle_rad) - btn.width() // 2
            y = center_y - radius * math.sin(angle_rad) - btn.height() // 2
            btn.move(int(x), int(y))
            btn.show()
            btn.raise_()
        self.radial_menu_open = True
        self.overlay = QWidget(self)
        self.overlay.setGeometry(0, 0, self.width(), self.height())
        self.overlay.setStyleSheet("background: transparent;")
        self.overlay.mousePressEvent = lambda e: self.hide_radial_menu()
        self.overlay.show()
        self.overlay.raise_()
        self.radial_trigger_btn.raise_()
        for btn in self.radial_buttons:
            btn.raise_()

    def hide_radial_menu(self):
        if not self.radial_menu_open:
            return
        for btn in self.radial_buttons:
            btn.hide()
        self.radial_menu_open = False
        if hasattr(self, 'overlay'):
            self.overlay.close()
            self.overlay.deleteLater()
            del self.overlay

    # ============ ЛОГИКА СМЕНЫ ЯЗЫКА ============
    def set_language(self, lang_code):
        if lang_code not in self.translations:
            return
        self.current_language = lang_code
        tr = self.translations[lang_code]
        self.setWindowTitle(tr.get("app_title", "Focus"))
        if hasattr(self, 'work_label'):
            self.work_label.setText(tr.get("timer_work", "work"))
        if hasattr(self, 'break_label'):
            self.break_label.setText(tr.get("timer_break", "break"))
        if hasattr(self, 'notes_panel') and self.notes_panel.layout() is not None:
            title_label = self.notes_panel.layout().itemAt(0).widget()
            if isinstance(title_label, QLabel):
                title_label.setText(f" {tr.get('notes_title', 'Notes')}")
        if hasattr(self, 'playlist_panel') and self.playlist_panel.layout() is not None:
            title_label = self.playlist_panel.layout().itemAt(0).widget()
            if isinstance(title_label, QLabel):
                title_label.setText(tr.get("playlist_title", "Current Playlist"))
        if hasattr(self, 'library_panel') and self.library_panel.layout() is not None:
            title_label = self.library_panel.layout().itemAt(0).widget()
            if isinstance(title_label, QLabel):
                title_label.setText(tr.get("library_title", "Music Library"))
        if hasattr(self, 'noises_panel') and self.noises_panel.layout() is not None:
            header_layout = self.noises_panel.layout().itemAt(0)
            if header_layout and header_layout.layout():
                title_label = header_layout.layout().itemAt(0).widget()
                if isinstance(title_label, QLabel):
                    title_label.setText(tr.get("noises_panel_title", "Ambient noises"))
        if hasattr(self, 'todo_panel') and self.todo_panel.layout() is not None:
            header_layout = self.todo_panel.layout().itemAt(0)
            if header_layout and header_layout.layout():
                title_label = header_layout.layout().itemAt(0).widget()
                if isinstance(title_label, QLabel):
                    title_label.setText(f" {tr.get('todo_title', 'To-Do List')}")
        if hasattr(self, 'kanban_panel') and self.kanban_panel.layout() is not None:
            header_layout = self.kanban_panel.layout().itemAt(0)
            if header_layout and header_layout.layout():
                title_label = header_layout.layout().itemAt(0).widget()
                if isinstance(title_label, QLabel):
                    title_label.setText(tr.get("kanban_title", "Kanban Board"))
        if hasattr(self, 'settings_radial_buttons'):
            button_keys = ["background_setting", "language_setting", "exit_setting"]
            for i, btn in enumerate(self.settings_radial_buttons):
                if i < len(button_keys):
                    text = tr.get(button_keys[i], button_keys[i])
                    btn.setToolTip(text)
                    if isinstance(btn, QPushButton) and btn.icon().isNull():
                        btn.setText(text.split()[0])
        if hasattr(self, 'notes_panel') and self.notes_panel.layout() is not None:
            for i in range(self.notes_panel.layout().count()):
                item = self.notes_panel.layout().itemAt(i)
                if item and item.widget() and isinstance(item.widget(), QPushButton):
                    current_text = item.widget().text().strip()
                    if current_text in ["Сохранить", "Save", "保存", "保存", "Guardar"]:
                        item.widget().setText(tr.get("notes_save_button", "Сохранить"))
                        break
        if hasattr(self, 'playlist_panel') and self.playlist_panel.layout() is not None:
            for i in range(self.playlist_panel.layout().count()):
                item = self.playlist_panel.layout().itemAt(i)
                if item and item.widget() and isinstance(item.widget(), QPushButton):
                    current_text = item.widget().text().strip()
                    if current_text in ["Открыть библиотеку", "Open Library", "打开库", "ライブラリを開く", "Abrir Biblioteca"]:
                        item.widget().setText(tr.get("library_open_button", "Открыть библиотеку"))
                        break
        if hasattr(self, 'todo_input'):
            tr = self.translations.get(self.current_language, {})
            self.todo_input.setPlaceholderText(f"✍️ {tr.get('todo_input_placeholder', 'Введите задачу...')}")
        self.update_kanban_column_titles()
        self.save_language_preference()

    def save_language_preference(self):
        try:
            with open(LANGUAGE_FILE, "w", encoding="utf-8") as f:
                json.dump({"language": self.current_language}, f)
        except Exception as e:
            print(f"Ошибка сохранения языка: {e}")

    def load_language_preference(self):
        try:
            if os.path.exists(LANGUAGE_FILE):
                with open(LANGUAGE_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    lang = data.get("language", "ru")
                    if lang in self.translations:
                        self.current_language = lang
        except Exception as e:
            print(f"Ошибка загрузки языка: {e}")

    def update_kanban_column_titles(self):
        if not hasattr(self, 'kanban_columns') or not self.kanban_columns:
            return
        tr = self.translations.get(self.current_language, {})
        column_key_map = {
            "todo": "kanban_column_todo",
            "progress": "kanban_column_progress",
            "done": "kanban_column_done"
        }
        for internal_key, frame in self.kanban_columns.items():
            layout = frame.layout()
            if layout and layout.count() > 0:
                title_widget = layout.itemAt(0).widget()
                if isinstance(title_widget, QLabel):
                    translation_key = column_key_map.get(internal_key, internal_key)
                    new_title = tr.get(translation_key, internal_key.capitalize())
                    title_widget.setText(new_title)

    # ============ ЛОГИКА СМЕНЫ ФОНА ============
    def load_backgrounds(self):
        self.background_files = []
        if not os.path.exists(VIDEO_FOLDER):
            return
        valid_extensions = ('.mov', '.mp4', '.avi', '.mkv', '.jpg', '.jpeg', '.png', '.bmp', '.gif', '.webp')
        for file in os.listdir(VIDEO_FOLDER):
            if file.lower().endswith(valid_extensions):
                self.background_files.append(os.path.join(VIDEO_FOLDER, file))
        self.background_index = 0
        self.load_background_preference()

    def load_background_preference(self):
        try:
            if os.path.exists(BACKGROUND_FILE):
                with open(BACKGROUND_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    index = data.get("index", 0)
                    if 0 <= index < len(self.background_files):
                        self.background_index = index
        except Exception as e:
            print(f"Ошибка загрузки фона: {e}")

    def save_background_preference(self):
        try:
            with open(BACKGROUND_FILE, "w", encoding="utf-8") as f:
                json.dump({"index": self.background_index}, f)
        except Exception as e:
            print(f"Ошибка сохранения фона: {e}")

    def next_background(self):
        if not hasattr(self, 'background_files') or len(self.background_files) == 0:
            self.load_backgrounds()
        if len(self.background_files) == 0:
            return
        self.background_index = (self.background_index + 1) % len(self.background_files)
        self.apply_background(self.background_files[self.background_index])
        self.save_background_preference()

    def apply_background(self, file_path):
        if hasattr(self, 'cap') and self.cap.isOpened():
            self.cap.release()
            self.video_timer.stop()
        if file_path.lower().endswith(('.mov', '.mp4', '.avi', '.mkv')):
            self.cap = cv2.VideoCapture(file_path)
            self.video_timer.start(33)
        else:
            pixmap = QPixmap(file_path)
            if not pixmap.isNull():
                pixmap = pixmap.scaled(self.size(), Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
                self.background_label.setPixmap(pixmap)
                self.background_label.setGeometry(0, 0, self.width(), self.height())

    # ============ ЗАГРУЗКА/СОХРАНЕНИЕ ============
    def load_data(self):
        try:
            if os.path.exists(NOTES_FILE):
                with open(NOTES_FILE, "r", encoding="utf-8") as f:
                    self.notes_data = json.load(f)
            if os.path.exists(TASKS_FILE):
                with open(TASKS_FILE, "r", encoding="utf-8") as f:
                    self.tasks_data = json.load(f)
            else:
                self.tasks_data = []
            if os.path.exists(KANBAN_FILE):
                with open(KANBAN_FILE, "r", encoding="utf-8") as f:
                    self.kanban_data = json.load(f)
            else:
                try:
                    with open(KANBAN_COLUMNS_FILE, "r", encoding="utf-8") as f:
                        columns_config = json.load(f)
                        self.kanban_data = {col["key"]: [] for col in columns_config}
                except:
                    self.kanban_data = {"todo": [], "progress": [], "done": []}
            if os.path.exists(PLAYLIST_FILE):
                with open(PLAYLIST_FILE, "r", encoding="utf-8") as f:
                    saved = json.load(f)
                    self.track_list = [p for p in saved if os.path.exists(p)]
            if os.path.exists(NOISES_FILE):
                with open(NOISES_FILE, "r") as f:
                    data = json.load(f)
                    self.noises_volumes.update({k: int(v) for k, v in data.items()})
            if os.path.exists(PLAYER_STATE_FILE):
                with open(PLAYER_STATE_FILE, "r") as f:
                    state = json.load(f)
                    self.last_played_track = state.get("last_track")
            else:
                self.last_played_track = None
            if os.path.exists(os.path.join(DATA_DIR, "file_paths.json")):
                with open(os.path.join(DATA_DIR, "file_paths.json"), "r", encoding="utf-8") as f:
                    self.file_paths = json.load(f)
            else:
                self.file_paths = {}
            self.load_language_preference()
        except Exception as e:
            print(f"❌ Error loading  {e}")
            self.tasks_data = []
            try:
                with open(KANBAN_COLUMNS_FILE, "r", encoding="utf-8") as f:
                    columns_config = json.load(f)
                    self.kanban_data = {col["key"]: [] for col in columns_config}
            except:
                self.kanban_data = {"todo": [], "progress": [], "done": []}
            self.file_paths = {}

    def save_data(self):
        try:
            with open(NOTES_FILE, "w", encoding="utf-8") as f:
                json.dump(self.notes_data, f, indent=2)
            with open(TASKS_FILE, "w", encoding="utf-8") as f:
                json.dump(self.tasks_data, f, indent=2)
            with open(KANBAN_FILE, "w", encoding="utf-8") as f:
                json.dump(self.kanban_data, f, indent=2)
            with open(NOISES_FILE, "w") as f:
                json.dump({k: int(v) for k, v in self.noises_volumes.items()}, f)
            with open(PLAYLIST_FILE, "w", encoding="utf-8") as f:
                json.dump(self.track_list, f, indent=2)
            with open(PLAYER_STATE_FILE, "w", encoding="utf-8") as f:
                last_track = self.track_list[self.current_index] if self.track_list else None
                json.dump({"last_track": last_track}, f, indent=2)
            with open(os.path.join(DATA_DIR, "file_paths.json"), "w", encoding="utf-8") as f:
                json.dump(self.file_paths, f, indent=2)
        except Exception as e:
            print(f"❌ Save error: {e}")

    def load_video(self):
        if not hasattr(self, 'background_files') or len(self.background_files) == 0:
            self.load_backgrounds()
        if len(self.background_files) == 0:
            self.background_label.setStyleSheet("background-color: #111;")
            return
        self.apply_background(self.background_files[self.background_index])

    def update_video(self):
        if not hasattr(self, 'cap') or not self.cap.isOpened():
            return
        ret, frame = self.cap.read()
        if not ret:
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
            return
        frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        h, w, ch = frame.shape
        bytes_per_line = ch * w
        img = QImage(frame.data, w, h, bytes_per_line, QImage.Format_RGB888)
        pixmap = QPixmap.fromImage(img).scaled(self.size(), Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
        self.background_label.setPixmap(pixmap)

    def resizeEvent(self, event):
        self.background_label.setGeometry(0, 0, self.width(), self.height())
        if not hasattr(self, 'cap') or not self.cap.isOpened():
            if self.background_label.pixmap():
                pixmap = self.background_label.pixmap().scaled(
                    self.size(),
                    Qt.KeepAspectRatioByExpanding,
                    Qt.SmoothTransformation
                )
                self.background_label.setPixmap(pixmap)
        self.timer_frame.move(self.width() - 270, 10)
        self.timer_frame.show()
        self.player_frame.move(30, self.height() - 90)
        self.player_frame.show()
        if hasattr(self, 'notes_btn'):
            notes_y = self.height() // 2 - self.notes_btn.height() // 2
            self.notes_btn.move(self.width() - 60, notes_y)
            self.notes_btn.show()
        self.noises_btn.move(self.width() - 75, self.height() - 75)
        self.noises_btn.show()
        self.radial_trigger_btn.move(20, 20)
        if hasattr(self, 'settings_radial_trigger_btn'):
            self.settings_radial_trigger_btn.move(self.width() // 2 - 25, 20)
            self.settings_radial_trigger_btn.show()
        if self.radial_menu_open:
            self.hide_radial_menu()
        super().resizeEvent(event)

    def closeEvent(self, event):
        self.save_data()
        event.accept()

    # --- УПРАВЛЕНИЕ НАСТРОЙКАМИ ДОСКИ KANBAN ---
    def open_kanban_settings(self):
        tr = self.translations.get(self.current_language, {})
        dialog = QDialog(self)
        dialog.setWindowTitle(tr.get("kanban_settings_title", "Настройки Kanban Board"))
        dialog.setFixedSize(500, 400)
        main_layout = QVBoxLayout(dialog)
        self.kanban_settings_list = QListWidget()
        self.kanban_settings_list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.kanban_settings_list.setDragDropMode(QAbstractItemView.InternalMove)
        self.kanban_settings_list.setDefaultDropAction(Qt.MoveAction)
        self.kanban_settings_list.setStyleSheet("""
            QListWidget {
                background: rgba(30, 30, 40, 200);
                border: 1px solid rgba(100, 100, 150, 150);
                border-radius: 8px;
                color: white;
            }
            QListWidget::item {
                padding: 10px;
                border-bottom: 1px solid rgba(100, 100, 150, 100);
            }
            QListWidget::item:selected {
                background: rgba(100, 140, 255, 180);
                color: white;
            }
        """)
        main_layout.addWidget(self.kanban_settings_list)
        order_layout = QHBoxLayout()
        move_up_btn = QPushButton(tr.get("kanban_column_move_up_button", "▲ Вверх"))
        move_up_btn.clicked.connect(lambda: self.move_selected_column(-1))
        move_up_btn.setStyleSheet("""
            QPushButton {
                background: rgba(80, 80, 120, 180);
                color: white;
                border: 1px solid rgba(100, 100, 150, 180);
                border-radius: 6px;
                padding: 8px;
                font-size: 12px;
            }
            QPushButton:hover {
                background: rgba(100, 100, 150, 220);
            }
            QPushButton:disabled {
                background: rgba(80, 80, 120, 80);
                color: rgba(200, 200, 200, 120);
                border: 1px solid rgba(100, 100, 150, 80);
            }
        """)
        move_down_btn = QPushButton(tr.get("kanban_column_move_down_button", "▼ Вниз"))
        move_down_btn.clicked.connect(lambda: self.move_selected_column(1))
        move_down_btn.setStyleSheet("""
            QPushButton {
                background: rgba(80, 80, 120, 180);
                color: white;
                border: 1px solid rgba(100, 100, 150, 180);
                border-radius: 6px;
                padding: 8px;
                font-size: 12px;
            }
            QPushButton:hover {
                background: rgba(100, 100, 150, 220);
            }
            QPushButton:disabled {
                background: rgba(80, 80, 120, 80);
                color: rgba(200, 200, 200, 120);
                border: 1px solid rgba(100, 100, 150, 80);
            }
        """)
        order_layout.addWidget(move_up_btn)
        order_layout.addWidget(move_down_btn)
        order_layout.addStretch()
        main_layout.addLayout(order_layout)
        buttons_layout = QHBoxLayout()
        add_btn = QPushButton(tr.get("kanban_column_add_button", "Добавить"))
        add_btn.clicked.connect(self.add_kanban_column_dialog)
        buttons_layout.addWidget(add_btn)
        edit_btn = QPushButton(tr.get("kanban_column_edit_button", "Изменить"))
        edit_btn.clicked.connect(self.edit_selected_kanban_column)
        buttons_layout.addWidget(edit_btn)
        delete_btn = QPushButton(tr.get("kanban_column_delete_button", "Удалить"))
        delete_btn.clicked.connect(self.delete_selected_kanban_column)
        buttons_layout.addWidget(delete_btn)
        main_layout.addLayout(buttons_layout)
        ok_cancel_layout = QHBoxLayout()
        ok_btn = QPushButton(tr.get("kanban_column_ok_button", "OK"))
        ok_btn.clicked.connect(lambda: self.apply_kanban_settings(dialog))
        ok_cancel_layout.addWidget(ok_btn)
        cancel_btn = QPushButton(tr.get("kanban_column_cancel_button", "Отмена"))
        cancel_btn.clicked.connect(dialog.reject)
        ok_cancel_layout.addWidget(cancel_btn)
        main_layout.addLayout(ok_cancel_layout)
        self.populate_kanban_settings_list()
        if dialog.exec_() == QDialog.Accepted:
            pass
        else:
            self.restore_kanban_settings()

    def populate_kanban_settings_list(self):
        self.kanban_settings_list.clear()
        try:
            with open(KANBAN_COLUMNS_FILE, "r", encoding="utf-8") as f:
                self.backup_columns_config = json.load(f)
        except:
            self.backup_columns_config = []
        for col_config in self.backup_columns_config:
            key = col_config.get("key", "unknown")
            title = col_config.get("title", key.capitalize())
            task_count = len(self.kanban_data.get(key, []))
            item = QListWidgetItem(title)
            item.setData(Qt.UserRole, col_config)
            self.kanban_settings_list.addItem(item)

    def add_kanban_column_dialog(self):
        tr = self.translations.get(self.current_language, {})
        dialog = QDialog(self)
        dialog.setWindowTitle(tr.get("kanban_column_add_dialog_title", "Добавить колонку"))
        layout = QGridLayout(dialog)
        layout.addWidget(QLabel(tr.get("kanban_column_name_label", "Название:")), 0, 0)
        name_input = QLineEdit()
        layout.addWidget(name_input, 0, 1)
        layout.addWidget(QLabel(tr.get("kanban_column_color_label", "Цвет:")), 1, 0)
        color_button = QPushButton(tr.get("kanban_column_color_label", "Выбрать цвет"))
        color = QColor(100, 100, 100)
        def pick_color():
            nonlocal color
            color = QColorDialog.getColor(initial=color, parent=dialog)
            if color.isValid():
                color_button.setStyleSheet(f"background-color: {color.name()};")
        color_button.clicked.connect(pick_color)
        color_button.setStyleSheet(f"background-color: {color.name()};")
        layout.addWidget(color_button, 1, 1)
        ok_btn = QPushButton(tr.get("kanban_column_ok_button", "OK"))
        cancel_btn = QPushButton(tr.get("kanban_column_cancel_button", "Отмена"))
        ok_btn.clicked.connect(dialog.accept)
        cancel_btn.clicked.connect(dialog.reject)
        layout.addWidget(ok_btn, 2, 0)
        layout.addWidget(cancel_btn, 2, 1)
        if dialog.exec_() == QDialog.Accepted:
            title = name_input.text().strip()
            if not title:
                QMessageBox.warning(self, tr.get("kanban_column_add_dialog_title", "Ошибка"), tr.get("kanban_column_name_label", "Название не может быть пустым."))
                return
            key = self.generate_unique_column_key(title)
            new_config = {
                "key": key,
                "title": title,
                "color": [color.red(), color.green(), color.blue()]
            }
            tr_format = tr.get("kanban_column_task_count_format", " (Задач: {count})")
            item = QListWidgetItem(f"{title}{tr_format.format(count=0)}")
            item.setData(Qt.UserRole, new_config)
            self.kanban_settings_list.addItem(item)
            if not hasattr(self, 'kanban_data'):
                self.kanban_data = {}
            self.kanban_data[key] = []

    def generate_unique_column_key(self, title):
        base_key = "".join(c.lower() for c in title if c.isalnum() or c == '_') or "column"
        key = base_key
        counter = 1
        existing_keys = set()
        for i in range(self.kanban_settings_list.count()):
            item = self.kanban_settings_list.item(i)
            config = item.data(Qt.UserRole)
            if config:
                existing_keys.add(config.get("key", ""))
        while key in existing_keys:
            key = f"{base_key}_{counter}"
            counter += 1
        return key

    def edit_selected_kanban_column(self):
        tr = self.translations.get(self.current_language, {})
        current_row = self.kanban_settings_list.currentRow()
        if current_row < 0:
            QMessageBox.warning(self, tr.get("kanban_column_edit_dialog_title", "Ошибка"), tr.get("kanban_column_edit_button", "Выберите колонку для редактирования."))
            return
        current_item = self.kanban_settings_list.item(current_row)
        old_config = current_item.data(Qt.UserRole)
        if not old_config:
            return
        old_title = old_config.get("title", "")
        old_color_rgb = old_config.get("color", [100, 100, 100])
        old_color = QColor(*old_color_rgb)
        dialog = QDialog(self)
        dialog.setWindowTitle(tr.get("kanban_column_edit_dialog_title", "Изменить колонку"))
        layout = QGridLayout(dialog)
        layout.addWidget(QLabel(tr.get("kanban_column_name_label", "Название:")), 0, 0)
        name_input = QLineEdit(old_title)
        layout.addWidget(name_input, 0, 1)
        layout.addWidget(QLabel(tr.get("kanban_column_color_label", "Цвет:")), 1, 0)
        color_button = QPushButton(tr.get("kanban_column_color_label", "Выбрать цвет"))
        def pick_color():
            nonlocal old_color
            color = QColorDialog.getColor(initial=old_color, parent=dialog)
            if color.isValid():
                old_color = color
                color_button.setStyleSheet(f"background-color: {color.name()};")
        color_button.clicked.connect(pick_color)
        color_button.setStyleSheet(f"background-color: {old_color.name()};")
        layout.addWidget(color_button, 1, 1)
        ok_btn = QPushButton(tr.get("kanban_column_ok_button", "OK"))
        cancel_btn = QPushButton(tr.get("kanban_column_cancel_button", "Отмена"))
        ok_btn.clicked.connect(dialog.accept)
        cancel_btn.clicked.connect(dialog.reject)
        layout.addWidget(ok_btn, 2, 0)
        layout.addWidget(cancel_btn, 2, 1)
        if dialog.exec_() == QDialog.Accepted:
            new_title = name_input.text().strip()
            if not new_title:
                QMessageBox.warning(self, tr.get("kanban_column_edit_dialog_title", "Ошибка"), tr.get("kanban_column_name_label", "Название не может быть пустым."))
                return
            new_config = old_config.copy()
            new_config["title"] = new_title
            new_config["color"] = [old_color.red(), old_color.green(), old_color.blue()]
            task_count = len(self.kanban_data.get(new_config["key"], []))
            tr_format = tr.get("kanban_column_task_count_format", " (Задач: {count})")
            current_item.setText(f"{new_title}{tr_format.format(count=task_count)}")
            current_item.setData(Qt.UserRole, new_config)

    def delete_selected_kanban_column(self):
        tr = self.translations.get(self.current_language, {})
        current_row = self.kanban_settings_list.currentRow()
        if current_row < 0:
            QMessageBox.warning(self, tr.get("kanban_column_delete_button", "Ошибка"), tr.get("kanban_column_delete_button", "Выберите колонку для удаления."))
            return
        current_item = self.kanban_settings_list.item(current_row)
        col_config = current_item.data(Qt.UserRole)
        if not col_config:
            return
        col_key = col_config.get("key", "")
        col_title = col_config.get("title", "")
        task_count = len(self.kanban_data.get(col_key, []))
        if task_count > 0:
            tr_text = tr.get("kanban_column_delete_confirm_text", "В колонке '{col_name}' есть {task_count} задач. Они будут удалены. Продолжить?")
            formatted_text = tr_text.format(col_name=col_title, task_count=task_count)
            reply = QMessageBox.question(
                self,
                tr.get("kanban_column_delete_confirm_title", "Подтверждение удаления"),
                formatted_text,
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No
            )
            if reply == QMessageBox.No:
                return
        self.kanban_data.pop(col_key, None)
        self.kanban_settings_list.takeItem(current_row)

    def move_selected_column(self, direction):
        current_row = self.kanban_settings_list.currentRow()
        if current_row < 0:
            return
        new_row = current_row + direction
        if new_row < 0 or new_row >= self.kanban_settings_list.count():
            return
        current_item = self.kanban_settings_list.takeItem(current_row)
        self.kanban_settings_list.insertItem(new_row, current_item)
        self.kanban_settings_list.setCurrentRow(new_row)

    def apply_kanban_settings(self, dialog):
        try:
            new_columns_config = []
            for i in range(self.kanban_settings_list.count()):
                item = self.kanban_settings_list.item(i)
                config = item.data(Qt.UserRole)
                if config:
                    new_columns_config.append(config)
            with open(KANBAN_COLUMNS_FILE, "w", encoding="utf-8") as f:
                json.dump(new_columns_config, f, indent=2)
            self.create_kanban_columns_from_settings()
            self.refresh_kanban_board()
            self.save_data()
            QMessageBox.information(self, "Успех", "Настройки Kanban Board успешно применены.")
            dialog.accept()
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", f"Не удалось применить настройки: {str(e)}")

    def restore_kanban_settings(self):
        pass

    def show_add_task_input(self, column_key):
        if column_key not in self.kanban_columns:
            return
        column_frame = self.kanban_columns[column_key]
        column_layout = column_frame.layout()
        if not column_layout:
            return
        input_container = QWidget()
        input_layout = QHBoxLayout(input_container)
        input_layout.setContentsMargins(0, 0, 0, 0)
        input_layout.setSpacing(5)
        line_edit = QLineEdit()
        tr = self.translations.get(self.current_language, {})
        line_edit.setPlaceholderText(tr.get("kanban_column_add_task_placeholder", "Введите название задачи..."))
        line_edit.setStyleSheet("""
            QLineEdit {
                background: rgba(255, 255, 255, 25);
                border: 1px solid rgba(255, 255, 255, 50);
                border-radius: 12px;
                color: white;
                padding: 8px;
                font-size: 14px;
            }
            QLineEdit:focus {
                border: 1px solid rgba(200, 220, 255, 150);
                background: rgba(255, 255, 255, 35);
            }
        """)
        cancel_btn = QPushButton("✕")
        cancel_btn.setFixedSize(24, 24)
        cancel_btn.setStyleSheet("""
            QPushButton {
                background: rgba(210, 60, 60, 180);
                color: white;
                border: none;
                border-radius: 12px;
                font-size: 14px;
                font-weight: bold;
            }
            QPushButton:hover {
                background: rgba(255, 70, 70, 220);
            }
        """)
        cancel_btn.clicked.connect(lambda: self.cancel_add_task(input_container, column_layout))
        input_layout.addWidget(line_edit, 1)
        input_layout.addWidget(cancel_btn)
        insert_index = column_layout.count() - 1
        column_layout.insertWidget(insert_index, input_container)
        line_edit.setFocus()
        line_edit.returnPressed.connect(lambda: self.add_task_from_input(line_edit, input_container, column_key, column_layout))
        original_focus_out = line_edit.focusOutEvent
        def new_focus_out(e):
            original_focus_out(e)
            text = line_edit.text().strip()
            if text:
                self.add_task_from_input(line_edit, input_container, column_key, column_layout)
            else:
                self.cancel_add_task(input_container, column_layout)
        line_edit.focusOutEvent = new_focus_out

    def add_task_from_input(self, line_edit, input_container, column_key, column_layout):
        text = line_edit.text().strip()
        if text:
            for col in self.kanban_columns.keys():
                if text in self.kanban_data.get(col, []):
                    self.kanban_data[col].remove(text)
            if column_key not in self.kanban_data:
                self.kanban_data[column_key] = []
            self.kanban_data[column_key].append(text)
            if column_key in ["progress", "done"]:
                found = False
                for task in self.tasks_data:
                    if task["text"] == text:
                        task["completed"] = (column_key == "done")
                        found = True
                        break
                if not found:
                    initial_status = True if column_key == "done" else False
                    self.tasks_data.append({"text": text, "completed": initial_status})
            else:
                self.tasks_data = [task for task in self.tasks_data if task["text"] != text]
            self.save_data()
            self.refresh_kanban_board()
            self.refresh_todo_list()
        self.cancel_add_task(input_container, column_layout)

    def cancel_add_task(self, input_container, column_layout):
        column_layout.removeWidget(input_container)
        input_container.deleteLater()

# === DRAGGABLE FRAME ===
class DraggableFrame(QFrame):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowFlags(Qt.FramelessWindowHint)
        self.drag_start_position = None
    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.drag_start_position = event.globalPos() - self.frameGeometry().topLeft()
            event.accept()
    def mouseMoveEvent(self, event):
        if event.buttons() == Qt.LeftButton and self.drag_start_position:
            self.move(event.globalPos() - self.drag_start_position)
            event.accept()

# === KANBAN DROP CONTAINER ===
class KanbanDropContainer(QWidget):
    def __init__(self, parent_app, column_name):
        super().__init__()
        self.parent_app = parent_app
        self.column_name = column_name
        self.setAcceptDrops(True)
    def dragEnterEvent(self, event):
        if event.mimeData().hasText() or event.mimeData().hasUrls():
            event.acceptProposedAction()
    def dropEvent(self, event):
        mime_data = event.mimeData()
        if mime_data.hasUrls():
            for url in mime_data.urls():
                if url.isLocalFile():
                    file_path = url.toLocalFile()
                    file_name = os.path.basename(file_path)
                    app = self.parent_app
                    if isinstance(app, FloatingFocusApp):
                        for col in app.kanban_columns.keys():
                            if file_name in app.kanban_data.get(col, []):
                                app.kanban_data[col].remove(file_name)
                        if self.column_name not in app.kanban_data:
                            app.kanban_data[self.column_name] = []
                        app.kanban_data[self.column_name].append(file_name)
                        if self.column_name in ["progress", "done"]:
                            found = False
                            for task in app.tasks_data:
                                if task["text"] == file_name:
                                    if self.column_name == "done":
                                        task["completed"] = True
                                    else:
                                        task["completed"] = False
                                    found = True
                                    break
                            if not found:
                                initial_status = True if self.column_name == "done" else False
                                app.tasks_data.append({"text": file_name, "completed": initial_status})
                        else:
                            app.tasks_data = [task for task in app.tasks_data if task["text"] != file_name]
                        if not hasattr(app, 'file_paths'):
                            app.file_paths = {}
                        app.file_paths[file_name] = file_path
                        app.refresh_todo_list()
                        app.refresh_kanban_board()
                        app.save_data()
        elif mime_data.hasText():
            data = mime_data.text()
            if "|" in data:
                task_text, source_column = data.rsplit("|", 1)
            else:
                task_text = data
                source_column = "unknown"
            app = self.parent_app
            if isinstance(app, FloatingFocusApp):
                for col in app.kanban_columns.keys():
                    if task_text in app.kanban_data.get(col, []):
                        app.kanban_data[col].remove(task_text)
                if self.column_name not in app.kanban_data:
                    app.kanban_data[self.column_name] = []
                app.kanban_data[self.column_name].append(task_text)
                if self.column_name in ["progress", "done"]:
                    found = False
                    for task in app.tasks_data:
                        if task["text"] == task_text:
                            if self.column_name == "done":
                                task["completed"] = True
                            else:
                                task["completed"] = False
                            found = True
                            break
                    if not found:
                        initial_status = True if self.column_name == "done" else False
                        app.tasks_data.append({"text": task_text, "completed": initial_status})
                else:
                    app.tasks_data = [task for task in app.tasks_data if task["text"] != task_text]
                app.refresh_todo_list()
                app.refresh_kanban_board()
                app.save_data()
        event.accept()

def set_app_icon():
    myappid = 'mycompany.myproduct.subproduct.version'
    ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(myappid)

if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = FloatingFocusApp()
    window.show()
    sys.exit(app.exec_())