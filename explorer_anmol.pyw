#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Folder Analyzer – Interactive, Modern UI
Requirements: PySide6 (pip install PySide6)
Tested on: Windows, macOS, Linux (X11/Wayland)
"""

import os
import sys
import json
import time
import platform
import traceback
import subprocess
import ctypes
import shutil
import html

try:
    from send2trash import send2trash  # pip install Send2Trash
    _HAVE_SEND2TRASH = True
except Exception:
    send2trash = None  # type: ignore
    _HAVE_SEND2TRASH = False

from pathlib import Path
from collections import defaultdict, Counter
from dataclasses import dataclass
from typing import Dict, List, Tuple, Optional

from PySide6.QtCore import (
    Qt, QDir, QSortFilterProxyModel, QThread, Signal, Slot, QModelIndex, QTimer,
    QObject, QRunnable, QThreadPool, QSize
)
from PySide6.QtGui import (
    QAction, QIcon, QKeySequence, QPalette, QColor, QActionGroup, QBrush
)
from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QTreeView, QFileSystemModel,
    QSplitter, QLineEdit, QLabel, QPushButton, QCheckBox, QProgressBar, QMessageBox, QTabWidget,
    QTableWidget, QTableWidgetItem, QFileDialog, QToolBar, QStatusBar, QMenu, QStyleFactory, QFormLayout,
    QHeaderView, QToolButton, QStyle, QInputDialog, QAbstractItemView
)

# ---------------------- Utilities ----------------------

def normalize_extension(name: str, *, compound: bool = True) -> str:
    """
    Return a normalized extension label for 'name'.
    - compound=False -> final suffix only ('.gz' for 'archive.tar.gz')
    - compound=True  -> combined suffixes ('.tar.gz' for 'archive.tar.gz')
    - dotfiles like '.bashrc' become their own type '.bashrc' (not '<no-ext>')
    - empty or trailing-dot names collapse to '<no-ext>'
    """
    name = name.strip()
    p = Path(name)

    if compound:
        combo = ''.join(p.suffixes).strip().lower()
        if combo:
            return combo

    ext = p.suffix.strip().lower()
    if ext in ("", "."):
        # Treat pure dotfiles (no additional dot) as their own "type"
        if name.startswith('.') and '.' not in name[1:]:
            return name.lower()
        return "<no-ext>"
    return ext


def format_bytes(num: int) -> str:
    if num is None:
        return "-"
    if num < 1024:
        return f"{num} B"
    units = ["KB", "MB", "GB", "TB", "PB", "EB"]
    size = float(num)
    for unit in units:
        size /= 1024.0
        if size < 1024.0:
            return f"{size:.2f} {unit}"
    return f"{size:.2f} ZB"


def is_symlink(path: str) -> bool:
    try:
        return os.path.islink(path)
    except Exception:
        return False


def open_with_default_app(path: str):
    try:
        if platform.system() == "Windows":
            os.startfile(path)  # type: ignore[attr-defined]
        elif platform.system() == "Darwin":
            subprocess.run(["open", path], check=False)
        else:
            subprocess.run(["xdg-open", path], check=False)
    except Exception as e:
        QMessageBox.warning(None, "Open Failed", f"Could not open:\n{path}\n\n{e}")


def open_in_explorer(path: str):
    try:
        if platform.system() == "Windows":
            if os.path.isfile(path):
                subprocess.run(["explorer", "/select,", os.path.normpath(path)], check=False)
            else:
                subprocess.run(["explorer", os.path.normpath(path)], check=False)
        elif platform.system() == "Darwin":
            if os.path.isfile(path):
                subprocess.run(["open", "-R", path], check=False)
            else:
                subprocess.run(["open", path], check=False)
        else:
            # Linux: open directory
            dir_to_open = path if os.path.isdir(path) else os.path.dirname(path) or path
            subprocess.run(["xdg-open", dir_to_open], check=False)
    except Exception as e:
        QMessageBox.warning(None, "Open in Explorer Failed", f"Could not open in file manager:\n{path}\n\n{e}")


def human_time(ts: Optional[float]) -> str:
    if ts is None:
        return "-"
    try:
        return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ts))
    except Exception:
        return "-"

# ---------------------- Data Structures ----------------------
# --- 1) ADD THIS CLASS (e.g., near your other helpers) ---
from PySide6.QtWidgets import QTableWidgetItem
from PySide6.QtCore import Qt
class NumericItem(QTableWidgetItem):
    """
    QTableWidgetItem that sorts by a hidden numeric value (Qt.UserRole)
    while displaying a human-readable string (e.g., '2.06 MB').
    """
    def __init__(self, display_text, sort_value):
        super().__init__(display_text)
        self.setData(Qt.UserRole, sort_value)

    def __lt__(self, other):
        # Prefer numeric comparison based on stored sort_value
        a = self.data(Qt.UserRole)
        b = other.data(Qt.UserRole) if isinstance(other, QTableWidgetItem) else None
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return a < b
        return super().__lt__(other)

@dataclass
class FolderStats:
    root: str
    total_size: int
    total_files: int
    total_dirs: int
    ext_counts: Dict[str, int]
    ext_sizes: Dict[str, int]
    top_subfolders: List[Tuple[str, int]]  # (subfolder_name, size)
    largest_files: List[Tuple[str, int]]   # (path, size)
    mtime_min: Optional[float]
    mtime_max: Optional[float]
    errors: List[str]

# ---------------------- Worker Thread ----------------------

class StatsWorker(QThread):
    progress = Signal(str)           # status text
    finished = Signal(object)        # FolderStats or None
    error = Signal(str)

    def __init__(self, root_path: str, top_n: int = 50, parent=None):
        super().__init__(parent)
        self.root_path = root_path
        self.top_n = top_n
        self._stop = False

    def stop(self):
        self._stop = True

    def run(self):
        try:
            stats = self._scan(self.root_path)
            if not self._stop:
                self.finished.emit(stats)
        except Exception:
            self.error.emit(traceback.format_exc())

    def _scan(self, root: str) -> FolderStats:
        total_size = 0
        total_files = 0
        total_dirs = 0
        ext_counts = Counter()
        ext_sizes = defaultdict(int)
        largest_files: List[Tuple[str, int]] = []
        errors: List[str] = []
        # For top subfolders by size (immediate children of root)
        top_level_sizes = defaultdict(int)
        mtime_min = None
        mtime_max = None

        if not os.path.exists(root):
            raise FileNotFoundError(f"Path does not exist: {root}")

        stack = [root]
        root_norm = os.path.normpath(root)

        last_progress_time = 0.0

        while stack and not self._stop:
            current = stack.pop()
            try:
                with os.scandir(current) as it:
                    for entry in it:
                        if self._stop:
                            break
                        path = entry.path
                        name = entry.name
                        # Skip symlinks
                        if is_symlink(path):
                            continue
                        try:
                            if entry.is_dir(follow_symlinks=False):
                                total_dirs += 1
                                stack.append(path)
                            elif entry.is_file(follow_symlinks=False):
                                st = entry.stat(follow_symlinks=False)
                                size = st.st_size
                                total_size += size
                                total_files += 1

                                # Extension stats (compound by default: '.tar.gz')
                                ext = normalize_extension(name, compound=True)
                                ext_counts[ext] += 1
                                ext_sizes[ext] += size

                                # Largest files (keep top_n)
                                if len(largest_files) < self.top_n:
                                    largest_files.append((path, size))
                                    largest_files.sort(key=lambda x: x[1], reverse=True)
                                else:
                                    if size > largest_files[-1][1]:
                                        largest_files[-1] = (path, size)
                                        largest_files.sort(key=lambda x: x[1], reverse=True)

                                # mtime
                                mtime = st.st_mtime
                                if mtime_min is None or mtime < mtime_min:
                                    mtime_min = mtime
                                if mtime_max is None or mtime > mtime_max:
                                    mtime_max = mtime

                                # Top-level subfolder attribution
                                rel = os.path.relpath(path, root_norm)
                                if os.sep in rel:
                                    first_part = rel.split(os.sep, 1)[0]
                                    top_level_sizes[first_part] += size
                                else:
                                    top_level_sizes["<root>"] += size

                            # Throttle progress updates
                            now = time.time()
                            if now - last_progress_time > 0.2:
                                self.progress.emit(f"Scanning… {total_files} files, {total_dirs} folders")
                                last_progress_time = now

                        except Exception as e:
                            errors.append(f"{path}: {e}")
                            continue
            except PermissionError:
                errors.append(f"{current}: Permission denied")
            except FileNotFoundError:
                errors.append(f"{current}: Not found")
            except Exception as e:
                errors.append(f"{current}: {e}")

        if self._stop:
            return None  # type: ignore[return-value]

        subfolders_sorted = sorted(top_level_sizes.items(), key=lambda x: x[1], reverse=True)

        return FolderStats(
            root=root,
            total_size=total_size,
            total_files=total_files,
            total_dirs=total_dirs,
            ext_counts=dict(ext_counts),
            ext_sizes=dict(ext_sizes),
            top_subfolders=subfolders_sorted,
            largest_files=largest_files[: self.top_n],
            mtime_min=mtime_min,
            mtime_max=mtime_max,
            errors=errors
        )

# ---------------------- Models & Filters ----------------------

class NameFilterProxy(QSortFilterProxyModel):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setRecursiveFilteringEnabled(True)
        self.setFilterCaseSensitivity(Qt.CaseInsensitive)
        self.setDynamicSortFilter(True)
        # Key line: use EditRole so QFileSystemModel supplies proper types
        self.setSortRole(Qt.EditRole)
        # New: toggles controlled by the UI
        self._show_files = True
        self._show_dirs = True
        self._show_hidden = False        

    # Toggle setters
    def setShowFiles(self, on: bool):
        self._show_files = bool(on)
        self.invalidateFilter()

    def setShowDirs(self, on: bool):
        self._show_dirs = bool(on)
        self.invalidateFilter()

    def setShowHidden(self, on: bool):
        self._show_hidden = bool(on)
        self.invalidateFilter()

    def _hasAcceptedChildren(self, parent_idx: QModelIndex) -> bool:
        """Return True if any child of parent_idx would be accepted."""
        src = self.sourceModel()
        rows = src.rowCount(parent_idx)
        for r in range(rows):
            if self.filterAcceptsRow(r, parent_idx):
                return True
        return False

    def filterAcceptsRow(self, source_row: int, source_parent: QModelIndex) -> bool:
        src = self.sourceModel()
        idx = src.index(source_row, 0, source_parent)
        if not idx.isValid():
            return False

        # Respect the current text filter (Search box)
        name_ok = super().filterAcceptsRow(source_row, source_parent)

        # Basic type checks
        is_dir = False
        is_hidden = False
        try:
            is_dir = src.isDir(idx)
            fi = src.fileInfo(idx)
            is_hidden = fi.isHidden()
        except Exception:
            pass

        # Hidden filter: if hidden not allowed, reject hidden rows outright
        if is_hidden and not self._show_hidden:
            return False

        # File/Folder filters:
        # - If a directory is not allowed but has children that match,
        #   keep it visible so user can expand into matching content.
        if is_dir and not self._show_dirs:
            return self._hasAcceptedChildren(idx)
        if (not is_dir) and not self._show_files:
            return False

        return name_ok

    # Keep your filterAcceptsRow(...) if you had one; add this:
    def lessThan(self, left: QModelIndex, right: QModelIndex) -> bool:
        src = self.sourceModel()

        # Column indices for QFileSystemModel:
        # 0 = Name, 1 = Size, 2 = Type, 3 = Date Modified
        try:
            if isinstance(src, QFileSystemModel):
                col = left.column()

                # Sort by raw size (bytes) coming from the model's EditRole.
                if col == 1:
                    # Prefer the model's direct helper to avoid QVariant conversion of huge ints
                    if hasattr(src, "get_numeric_size"):
                        try:
                            lv = src.get_numeric_size(left)
                            rv = src.get_numeric_size(right)
                            return int(lv) < int(rv)
                        except Exception:
                            pass
                    # Fallbacks (safe, but directories may be zero if not computed)
                    try:
                        return src.fileInfo(left).size() < src.fileInfo(right).size()
                    except Exception:
                        pass
                # Sort by QDateTime, not formatted string
                if col == 3:
                    dt_l = src.fileInfo(left).lastModified()
                    dt_r = src.fileInfo(right).lastModified()
                    return dt_l < dt_r
        except Exception:
            # Fallback to default
            pass

        # Default: use the configured sort role (Qt.EditRole)
        return super().lessThan(left, right)

# ---------------------- NEW: Directory sizes in the left tree ----------------------
class _DirSizeSignal(QObject):
    done = Signal(str, object)  # path, total_size_bytes (PyObject to avoid 32-bit overflow)


class _DirSizeTask(QRunnable):
    """Background task to compute directory size recursively (no symlinks)."""
    def __init__(self, path: str, signal_obj: _DirSizeSignal):
        super().__init__()
        self.path = path
        self.signal_obj = signal_obj

    def run(self):
        total = 0
        stack = [self.path]
        try:
            while stack:
                d = stack.pop()
                try:
                    with os.scandir(d) as it:
                        for entry in it:
                            p = entry.path
                            # Skip symlinks
                            if is_symlink(p):
                                continue
                            try:
                                if entry.is_file(follow_symlinks=False):
                                    total += entry.stat(follow_symlinks=False).st_size
                                elif entry.is_dir(follow_symlinks=False):
                                    stack.append(p)
                            except Exception:
                                continue
                except Exception:
                    continue
        except Exception:
            pass
        self.signal_obj.done.emit(self.path, total)  # unchanged emit; type now 'object'


class DirectorySizeModel(QFileSystemModel):
    """
    QFileSystemModel subclass that computes and shows directory sizes in the Size column.
    - Files: default QFileSystemModel behavior
    - Directories: shows aggregated size (computed asynchronously). While pending, shows '…'
    """
    def __init__(self, parent=None):
        super().__init__(parent)
        self._sizes: Dict[str, int] = {}
        self._pending: set[str] = set()
        self._pool = QThreadPool.globalInstance()
        self._sig = _DirSizeSignal()
        self._sig.done.connect(self._on_size_done)
        # New: toggle to enable/disable directory-size computation
        self._compute_dir_sizes: bool = False
        # NEW: paths currently "cut" (to render light grey)
        self._cut_marked: set[str] = set()

    def set_cut_marked(self, paths: List[str]) -> None:
        """Mark these file/folder paths as 'cut' (light grey in the view)."""
        prev = set(self._cut_marked)
        self._cut_marked = set(paths or [])
        to_update = prev.union(self._cut_marked)
        for p in to_update:
            try:
                idx = self.index(p)  # column 0 index for this path
                if idx.isValid():
                    # Update all 4 columns for that row (Name, Size, Type, Date)
                    left = idx.sibling(idx.row(), 0)
                    right = idx.sibling(idx.row(), 3)
                    self.dataChanged.emit(left, right, [Qt.ForegroundRole])
            except Exception:
                pass        
        
    def set_compute_dir_sizes(self, enabled: bool) -> None:
        """Enable/disable *directory* size computation & display."""
        self._compute_dir_sizes = bool(enabled)
        # Optional: stop scheduling new tasks when disabled; existing tasks may still finish.
        if not enabled:
            self._pending.clear()       

    def data(self, index: QModelIndex, role: int = Qt.DisplayRole):
        # NEW: make "cut" items appear light grey (like Explorer)
        if index.isValid() and role == Qt.ForegroundRole:
            try:
                path = self.filePath(index)
                if path in getattr(self, "_cut_marked", set()):
                    return QBrush(QColor(160, 160, 160))  # light grey
            except Exception:
                pass

        if index.isValid() and index.column() == 1:  # Size column
            if role == Qt.TextAlignmentRole:
                return int(Qt.AlignLeft | Qt.AlignVCenter)
            if self.isDir(index):
                # If toggle is OFF: don't compute or show folder sizes
                if not self._compute_dir_sizes:
                    if role == Qt.DisplayRole:
                        return ""  # show nothing for folders when disabled
                    if role in (Qt.EditRole, Qt.UserRole):
                        return 0   # numeric 0 so sorting is stable
                    return super().data(index, role)    
                path = self.filePath(index)
                if path in self._sizes:
                    size = self._sizes[path]
                    if role == Qt.DisplayRole:
                        return format_bytes(size)
                    if role in (Qt.EditRole, Qt.UserRole):
                        return 0
                else:
                    # Schedule computation only when enabled
                    if self._compute_dir_sizes and path not in self._pending:
                        self._pending.add(path)
                        self._pool.start(_DirSizeTask(path, self._sig))
                    # Placeholders while computing
                    if role == Qt.DisplayRole:
                        return "…"
                    if role in (Qt.EditRole, Qt.UserRole):
                        return 0
            else:
                # File: return a numeric size for sorting
                if role in (Qt.EditRole, Qt.UserRole):
                    try:
                        return self.fileInfo(index).size()
                    except Exception:
                        return 0
            
        return super().data(index, role)
        
    # --- NEW: helper the proxy can call to get a pure-Python integer size ---
    def get_numeric_size(self, index: QModelIndex) -> int:
        """Return size in bytes for files and directories (0 if unknown)."""
        if not index.isValid() or index.column() != 1:
            return 0
        try:
            if self.isDir(index):
                if not self._compute_dir_sizes:
                    return 0
                size = self._sizes.get(self.filePath(index), 0)
                return int(size) if size is not None else 0
            else:
                return int(self.fileInfo(index).size())
        except Exception:
            return 0        

    @Slot(str, object)
    def _on_size_done(self, path: str, size_obj):
        # Ignore updates if feature is off (prevents UI churn and surprises)
        if not getattr(self, "_compute_dir_sizes", False):
            self._pending.discard(path)
            return
        try:
            size = int(size_obj)
        except Exception:
            size = 0
        self._sizes[path] = size    
        self._pending.discard(path)
        # Notify view: update only the Size column for this path
        idx = self.index(path)
        if idx.isValid():
            size_idx = idx.sibling(idx.row(), 1)
            self.dataChanged.emit(size_idx, size_idx, [Qt.DisplayRole, Qt.EditRole, Qt.UserRole])


# ---------------------- Main Window ----------------------

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        # ---- THEME: single source of truth -----
        self.theme = "light"  # 'light' or 'dark'
        self.setWindowTitle("Explorer")
        # Track navigation root (left tree root) vs. analysis root (right pane report)
        self.current_root: Optional[str] = None
        self.analysis_root: Optional[str] = None
        self._suppress_next_selection_analyze = False

        self.resize(1200, 720)
        self.setWindowIcon(QIcon.fromTheme("folder"))

        # State
        self.worker: Optional[StatsWorker] = None
        self.auto_analyze = True
        
        # Internal file clipboard for copy/cut/paste
        self._file_clipboard: List[str] = []
        self._clipboard_mode: Optional[str] = None  # "copy" | "cut" | None

        # Toolbar
        self._init_toolbar()

        # Central layout (splitter)
        splitter = QSplitter(Qt.Horizontal, self)
        self.setCentralWidget(splitter)

        # Left pane (tree + controls)
        self.left_widget = QWidget()
        left_layout = QVBoxLayout(self.left_widget)
        left_layout.setContentsMargins(6, 6, 6, 6)

        # Search row
        search_row = QHBoxLayout()
        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("Search (name contains)…")
        self.clear_btn = QPushButton("Clear")

        # Small "Up" button near search
        self.btn_up = QToolButton()
        self.btn_up.setIcon(self.style().standardIcon(QStyle.SP_FileDialogToParent))
        self.btn_up.setToolTip("Go up to parent folder")
        self.btn_up.clicked.connect(self.go_up_one)

        search_row.addWidget(QLabel("Search:"))
        search_row.addWidget(self.search_edit, 1)
        search_row.addWidget(self.clear_btn)
        search_row.addWidget(self.btn_up)

        # Filters row
        filters_row = QHBoxLayout()
        self.show_files_cb = QCheckBox("Files")
        self.show_files_cb.setChecked(True)
        self.show_dirs_cb = QCheckBox("Folders")
        self.show_dirs_cb.setChecked(True)
        self.show_hidden_cb = QCheckBox("Hidden")
        self.show_hidden_cb.setChecked(False)
        # New: checkbox to toggle folder size measurement
        self.cb_folder_sizes = QCheckBox("Folder sizes")
        self.cb_folder_sizes.setChecked(False)  # default OFF
        filters_row.addWidget(QLabel("Show:"))
        filters_row.addWidget(self.show_files_cb)
        filters_row.addWidget(self.show_dirs_cb)
        filters_row.addWidget(self.show_hidden_cb)
        filters_row.addSpacing(16)
        filters_row.addWidget(self.cb_folder_sizes)
        filters_row.addStretch()

        # TreeView
        self.fs_model = DirectorySizeModel()  # <-- changed: use model that shows folder sizes
        self.fs_model.setRootPath(QDir.rootPath())
        self.fs_model.setResolveSymlinks(False)

        self.tree_proxy = NameFilterProxy(self)
        self.tree_proxy.setSourceModel(self.fs_model)

        self.tree = QTreeView()
        self.tree.setModel(self.tree_proxy)
        self.tree.setSortingEnabled(True)
        self.tree.sortByColumn(0, Qt.AscendingOrder)
        self.tree.setAlternatingRowColors(True)
        self.tree.setExpandsOnDoubleClick(True)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.setEditTriggers(QTreeView.NoEditTriggers)
        # Allow multi-selection with Shift/Ctrl (Cmd on macOS)
        self.tree.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.tree.setDragEnabled(True)  # optional if you plan drag & drop moves
        self.tree.setSelectionBehavior(QAbstractItemView.SelectRows)        
        self.tree.setUniformRowHeights(True)
        self.tree.setHeaderHidden(False)
        header = self.tree.header()
        header.setStretchLastSection(False)
        # Make columns user-resizable (Interactive) with sensible initial sizes
        header.setMinimumSectionSize(70)
        for c in range(4):  # 0=Name, 1=Size, 2=Type, 3=Date Modified
            header.setSectionResizeMode(c, QHeaderView.Interactive)
        # Initial widths: wider "Name", others sized to contents once
        self.tree.setColumnWidth(0, 320)
        for c in (1, 2, 3):
            self.tree.resizeColumnToContents(c)
        header.setSectionsMovable(True)    
        left_layout.addLayout(search_row)
        left_layout.addLayout(filters_row)
        left_layout.addWidget(self.tree, 1)

        # Right pane (tabs + progress + status)
        self.right_widget = QWidget()
        right_layout = QVBoxLayout(self.right_widget)
        right_layout.setContentsMargins(6, 6, 6, 6)

        # Status + progress
        status_row = QHBoxLayout()
        self.status_label = QLabel("Ready")
        self.progress = QProgressBar()
        a = self.progress
        a.setVisible(False)
        a.setRange(0, 0)  # Busy by default
        status_row.addWidget(self.status_label, 1)
        status_row.addWidget(self.progress, 0)

        # Tabs
        self.tabs = QTabWidget()
        # Summary tab
        self.summary_tab = QWidget()
        self.summary_form = QFormLayout(self.summary_tab)
        self.lbl_root = QLabel("-")
        self.lbl_total_size = QLabel("-")
        self.lbl_total_files = QLabel("-")
        self.lbl_total_dirs = QLabel("-")
        self.lbl_avg_size = QLabel("-")
        self.lbl_mtime_range = QLabel("-")
        self.summary_form.addRow("Analyzed Path:", self.lbl_root)
        self.summary_form.addRow("Total Size:", self.lbl_total_size)
        self.summary_form.addRow("Total Files:", self.lbl_total_files)
        self.summary_form.addRow("Total Folders:", self.lbl_total_dirs)
        self.summary_form.addRow("Average File Size:", self.lbl_avg_size)
        self.summary_form.addRow("Modified Range:", self.lbl_mtime_range)

        # File types tab
        self.types_table = QTableWidget(0, 3)
        self.types_table.setHorizontalHeaderLabels(["Extension", "Count", "Total Size"])
        self.types_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.Stretch)
        self.types_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeToContents)
        self.types_table.horizontalHeader().setSectionResizeMode(2, QHeaderView.ResizeToContents)
        self.types_table.setSortingEnabled(True)

        # Subfolders tab
        self.subfolders_table = QTableWidget(0, 2)
        self.subfolders_table.setHorizontalHeaderLabels(["Top-level Subfolder", "Size"])
        self.subfolders_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.Stretch)
        self.subfolders_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeToContents)
        self.subfolders_table.setSortingEnabled(True)

        # Largest files tab
        self.largest_table = QTableWidget(0, 2)
        self.largest_table.setHorizontalHeaderLabels(["Path", "Size"])
        self.largest_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.Stretch)
        self.largest_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeToContents)
        self.largest_table.setSortingEnabled(True)

        # Pack tabs
        self.tabs.addTab(self.summary_tab, " Summary ")
        self.tabs.addTab(self.types_table, " File Types ")
        self.tabs.addTab(self.subfolders_table, " Subfolders ")
        self.tabs.addTab(self.largest_table, " Largest Files ")

        right_layout.addLayout(status_row)
        right_layout.addWidget(self.tabs, 1)

        splitter.addWidget(self.left_widget)
        splitter.addWidget(self.right_widget)
        splitter.setSizes([400, 800])

        # Status bar
        self.setStatusBar(QStatusBar(self))

        # Connect signals
        self.search_edit.textChanged.connect(self._apply_search)
        self.clear_btn.clicked.connect(lambda: self.search_edit.setText(""))
        self.show_files_cb.toggled.connect(self._apply_filters)
        self.show_dirs_cb.toggled.connect(self._apply_filters)
        self.show_hidden_cb.toggled.connect(self._apply_filters)
        self.cb_folder_sizes.toggled.connect(self._toggle_folder_sizes)
        self.tree.customContextMenuRequested.connect(self._tree_context_menu)
        self.tree.doubleClicked.connect(self._tree_double_clicked)
        self.tree.selectionModel().selectionChanged.connect(self._tree_selection_changed)
        
        # Keyboard shortcuts for file ops
        self._install_shortcuts()

        # Apply initial look
        QApplication.setStyle(QStyleFactory.create("Fusion"))
        self.set_theme("light")  # default
        self._update_nav_actions()
        # Default icon size to match the checked preset in View ▸ Icon size
        self.set_tree_icon_size(24)        

        # Prompt for folder on startup
        QTimer.singleShot(200, self.choose_folder)

    # ---------- Theme ----------
    def set_theme(self, theme: str):
        theme = (theme or "").strip().lower()
        if theme not in ("light", "dark"):
            theme = "light"
        self.theme = theme
        # Update menu checks if they exist
        if hasattr(self, "act_theme_light"):
            self.act_theme_light.setChecked(self.theme == "light")
        if hasattr(self, "act_theme_dark"):
            self.act_theme_dark.setChecked(self.theme == "dark")
        self._apply_theme()

    def _selected_paths(self) -> List[str]:
        """Return all selected item paths (column 0) in the tree."""
        paths: List[str] = []
        if not self.tree.selectionModel():
            return paths
        for idx in self.tree.selectionModel().selectedRows(0):
            src_idx = self.tree_proxy.mapToSource(idx)
            paths.append(self.fs_model.filePath(src_idx))
        return paths
        
    def _current_path_sel(self):
        """Return (path, is_dir) for the current selection, or (None, None) if none."""
        idx = self.tree.currentIndex()
        if not idx.isValid():
            return None, None
        src_idx = self.tree_proxy.mapToSource(idx)
        path = self.fs_model.filePath(src_idx)
        return path, self.fs_model.isDir(src_idx)        

    def _apply_theme(self):
        # Order matters: Style -> clear stylesheets -> palette -> stylesheet
        app = QApplication.instance()
        QApplication.setStyle(QStyleFactory.create("Fusion"))

        # Clear any existing stylesheets to avoid mixing
        app.setStyleSheet("")
        self.setStyleSheet("")

        pal = QPalette()
        if self.theme == "dark":
            pal.setColor(QPalette.Window, QColor(43, 43, 43))
            pal.setColor(QPalette.WindowText, QColor(220, 220, 220))
            pal.setColor(QPalette.Base, QColor(35, 35, 35))
            pal.setColor(QPalette.AlternateBase, QColor(50, 50, 50))
            pal.setColor(QPalette.ToolTipBase, QColor(255, 255, 255))
            pal.setColor(QPalette.ToolTipText, QColor(0, 0, 0))
            pal.setColor(QPalette.Text, QColor(220, 220, 220))
            pal.setColor(QPalette.Button, QColor(53, 53, 53))
            pal.setColor(QPalette.ButtonText, QColor(220, 220, 220))
            pal.setColor(QPalette.BrightText, QColor(255, 0, 0))
            pal.setColor(QPalette.Highlight, QColor(58, 86, 131))
            pal.setColor(QPalette.HighlightedText, QColor(255, 255, 255))
            pal.setColor(QPalette.Link, QColor(90, 150, 250))

            pal.setColor(QPalette.Disabled, QPalette.Text, QColor(160, 160, 160))
            pal.setColor(QPalette.Disabled, QPalette.ButtonText, QColor(160, 160, 160))
            pal.setColor(QPalette.Disabled, QPalette.WindowText, QColor(160, 160, 160))
            pal.setColor(QPalette.Disabled, QPalette.Highlight, QColor(70, 70, 70))
            pal.setColor(QPalette.Disabled, QPalette.HighlightedText, QColor(180, 180, 180))

            app.setPalette(pal)
            # Minimal dark stylesheet for certain widgets
            app.setStyleSheet("""
                QWidget { background-color: #2b2b2b; color: #dddddd; }
                QTreeView::item:selected { background: #3a5683; color: white; }
                QHeaderView::section { background-color: #3a3a3a; color: #dddddd; }
                QLineEdit, QTableView, QTabBar::tab, QComboBox, QTextEdit {
                    background-color: #3a3a3a; color: #dddddd; border: 1px solid #555;
                }
                /* ---- Context menu styling (dark) ---- */
                QMenu { background-color: #2b2b2b; color: #dddddd; border: 1px solid #555; }
                QMenu::item { background: transparent; padding: 6px 24px; }
                QMenu::item:selected, QMenu::item:hover { background: #3a5683; color: white; }
                QMenu::separator { height: 1px; background: #555; margin: 4px 6px; }
                
                QToolBar { background: #2b2b2b; border: 0; }
                QStatusBar { background: #2b2b2b; }
                QPushButton { background-color: #414141; border: 1px solid #666; padding: 4px 8px; }
                QPushButton:hover { background-color: #4a4a4a; }
            """)
        else:
            pal.setColor(QPalette.Window, QColor(248, 249, 250))
            pal.setColor(QPalette.WindowText, QColor(30, 30, 30))
            pal.setColor(QPalette.Base, QColor(255, 255, 255))
            pal.setColor(QPalette.AlternateBase, QColor(240, 240, 240))
            pal.setColor(QPalette.ToolTipBase, QColor(255, 255, 220))
            pal.setColor(QPalette.ToolTipText, QColor(30, 30, 30))
            pal.setColor(QPalette.Text, QColor(30, 30, 30))
            pal.setColor(QPalette.Button, QColor(245, 245, 245))
            pal.setColor(QPalette.ButtonText, QColor(30, 30, 30))
            pal.setColor(QPalette.BrightText, QColor(255, 0, 0))
            pal.setColor(QPalette.Highlight, QColor(0, 120, 215))
            pal.setColor(QPalette.HighlightedText, QColor(255, 255, 255))
            pal.setColor(QPalette.Link, QColor(0, 102, 204))

            pal.setColor(QPalette.Disabled, QPalette.Text, QColor(140, 140, 140))
            pal.setColor(QPalette.Disabled, QPalette.ButtonText, QColor(140, 140, 140))
            pal.setColor(QPalette.Disabled, QPalette.WindowText, QColor(140, 140, 140))
            pal.setColor(QPalette.Disabled, QPalette.Highlight, QColor(200, 200, 200))
            pal.setColor(QPalette.Disabled, QPalette.HighlightedText, QColor(100, 100, 100))

            app.setPalette(pal)
            app.setStyleSheet("""
                QWidget { background-color: #f8f9fa; color: #1e1e1e; }
                QHeaderView::section { background-color: #f0f0f0; color: #1e1e1e; }
                QLineEdit, QTableView, QTabBar::tab, QComboBox, QTextEdit {
                    background-color: #ffffff; color: #1e1e1e; border: 1px solid #cfcfcf;
                }
                /* ---- Context menu styling (light) ---- */
                QMenu { background-color: #ffffff; color: #1e1e1e; border: 1px solid #cfcfcf; }
                QMenu::item { background: transparent; padding: 6px 24px; }
                QMenu::item:selected, QMenu::item:hover { background: #dbe9ff; color: #000; }
                QMenu::separator { height: 1px; background: #e0e0e0; margin: 4px 6px; }                
                
                QToolBar { background: #f8f9fa; border: 0; }
                QStatusBar { background: #f8f9fa; }
                QPushButton { background-color: #ffffff; border: 1px solid #cfcfcf; padding: 4px 8px; }
                QPushButton:hover { background-color: #f0f0f0; }
            """)

        # Force a polish to refresh widgets
        app.setStyle(app.style().objectName())
        self.repaint()

    # ---------- UI: Toolbar ----------
    def _init_toolbar(self):
        tb = QToolBar("Main")
        tb.setIconSize(tb.iconSize())
        self.addToolBar(tb)

        act_choose = QAction(" Choose Folder ", self)
        act_choose.setShortcut(QKeySequence("Ctrl+O"))
        act_choose.triggered.connect(self.choose_folder)
        tb.addAction(act_choose)

        tb.addSeparator()

        # Single-click theme toggle (replaces dropdown)
        self.act_theme_toggle = QAction(self.style().standardIcon(QStyle.SP_BrowserReload),
                                        "Light/Dark", self)
        # Optional shortcut: CtrlT on Windows/Linux, ⌘T on macOS
        if platform.system() == "Darwin":
            self.act_theme_toggle.setShortcut(QKeySequence("MetaT"))
        else:
            self.act_theme_toggle.setShortcut(QKeySequence("CtrlT"))
        self.act_theme_toggle.setStatusTip("Toggle between Light and Dark theme")
        self.act_theme_toggle.triggered.connect(self._toggle_theme)
        tb.addAction(self.act_theme_toggle)

        # Up button (toolbar)
        self.act_up = QAction(self.style().standardIcon(QStyle.SP_FileDialogToParent), "Up", self)
        if platform.system() == "Darwin":
            self.act_up.setShortcut(QKeySequence("Meta+Up"))   # ⌘+↑
        else:
            self.act_up.setShortcut(QKeySequence("Alt+Up"))    # Alt+↑
        self.act_up.setStatusTip("Go to parent folder")
        self.act_up.triggered.connect(self.go_up_one)
        tb.addAction(self.act_up)

        # Rescan / Export
        self.act_rescan = QAction(" Rescan ", self)
        self.act_rescan.setShortcut(QKeySequence.Refresh)
        self.act_rescan.triggered.connect(self.rescan)
        self.act_rescan.setEnabled(True)
        tb.addAction(self.act_rescan)

        self.act_export = QAction(" Export HTML ", self)
        self.act_export.triggered.connect(self.export_html)
        self.act_export.setEnabled(False)
        tb.addAction(self.act_export)

        tb.addSeparator()

        self.act_auto = QAction(" Auto-analyze ", self)
        self.act_auto.setCheckable(True)
        self.act_auto.setChecked(True)
        self.act_auto.toggled.connect(self._toggle_auto)
        tb.addAction(self.act_auto)

        tb.addSeparator()

        # Expand/Collapse All
        act_expand_all = QAction(" Expand All ", self)
        act_expand_all.triggered.connect(self.expand_all)
        tb.addAction(act_expand_all)

        act_collapse_all = QAction("Collapse All", self)
        act_collapse_all.triggered.connect(self.collapse_all)
        tb.addAction(act_collapse_all)

        # ----- View menu: Icon size presets -----
        view_menu = QMenu("View", self)
        icon_menu = QMenu("Icon size", view_menu)
        self.icon_size_group = QActionGroup(self)
        self.icon_size_group.setExclusive(True)

        def add_icon_size(label: str, px: int, checked: bool = False):
            act = QAction(label, self, checkable=True)
            act.setChecked(checked)
            act.triggered.connect(lambda _=False, s=px: self.set_tree_icon_size(s))
            self.icon_size_group.addAction(act)
            icon_menu.addAction(act)

        # Presets: adjust values if you prefer different sizes
        add_icon_size("Small (16 px)", 16, checked=False)
        add_icon_size("Medium (24 px)", 24, checked=True)   # default
        add_icon_size("Large (32 px)", 32, checked=False)
        add_icon_size("Extra Large (48 px)", 48, checked=False)

        view_menu.addMenu(icon_menu)
        tb.addAction(view_menu.menuAction())

    def set_tree_icon_size(self, px: int):
        """Set the icon size for the left tree view."""
        try:
            self.tree.setIconSize(QSize(px, px))
            # (Optional) feedback in status bar
            if self.statusBar():
                self.statusBar().showMessage(f"Icon size: {px}px", 2000)
        except Exception:
            pass

    def _toggle_theme(self):
        """Flip theme between 'light' and 'dark' with one click."""
        next_theme = "dark" if (self.theme or "").lower() == "light" else "light"
        self.set_theme(next_theme)        

    def _toggle_auto(self, checked: bool):
        self.auto_analyze = checked

    # ---------- Folder selection & scanning ----------
    def choose_folder(self):
        directory = QFileDialog.getExistingDirectory(self, "Choose folder to analyze", QDir.homePath())
        if directory:
            self.set_root(directory)
            
    def _target_dir_for_paste(self, path: str, is_dir: bool) -> str:
        """Return the directory where pasted items should go based on the clicked item."""
        return path if is_dir else (os.path.dirname(path) or path)

    def _ensure_unique_name(self, dst_path: str) -> str:
        """Return a non-conflicting path by appending ' - Copy', ' - Copy (2)', ... if needed."""
        if not os.path.exists(dst_path):
            return dst_path
        base = os.path.basename(dst_path)
        parent = os.path.dirname(dst_path)
        stem, ext = os.path.splitext(base)
        # If it's a folder, ext is '' which is fine
        candidate = f"{stem} - Copy{ext}"
        i = 2
        while os.path.exists(os.path.join(parent, candidate)):
            candidate = f"{stem} - Copy ({i}){ext}"
            i += 1
        return os.path.join(parent, candidate)

    def _delete_path_permanent(self, path: str):
        what = "folder" if os.path.isdir(path) else "file"
        reply = QMessageBox.question(
            self, "Confirm Delete",
            f"Are you sure you want to permanently delete this {what}?\n\n{path}",
            QMessageBox.Yes | QMessageBox.No, QMessageBox.No
        )
        if reply != QMessageBox.Yes:
            return
        try:
            if os.path.isdir(path):
                shutil.rmtree(path)
            else:
                os.remove(path)
        except Exception as e:
            QMessageBox.critical(self, "Delete Failed", str(e))

    def _rename_path(self, path: str):
        parent = os.path.dirname(path) or os.path.abspath(os.sep)
        old_name = os.path.basename(path)
        new_name, ok = QInputDialog.getText(self, "Rename", "New name:", text=old_name)
        if not ok or not new_name.strip():
            return
        new_name = new_name.strip()
        new_path = os.path.join(parent, new_name)
        if os.path.exists(new_path):
            QMessageBox.warning(self, "Rename", "A file/folder with that name already exists.")
            return
        try:
            os.rename(path, new_path)
        except Exception as e:
            QMessageBox.critical(self, "Rename Failed", str(e))

    def _copy_paths(self, paths: List[str]):
        self._file_clipboard = list(paths)
        self._clipboard_mode = "copy"
        # Ensure nothing appears as 'cut'
        try:
            self.fs_model.set_cut_marked([])
        except Exception:
            pass        

    def _cut_paths(self, paths: List[str]):
        self._file_clipboard = list(paths)
        self._clipboard_mode = "cut"
        # Show light grey for all cut items
        try:
            self.fs_model.set_cut_marked(paths)
        except Exception:
            pass        

    def _paste_paths(self, dest_dir: str):
        if not self._file_clipboard or not self._clipboard_mode:
            return
        try:
            QApplication.setOverrideCursor(Qt.WaitCursor)
            for src in self._file_clipboard:
                name = os.path.basename(src)
                dst = os.path.join(dest_dir, name)
                if self._clipboard_mode == "copy":
                    if os.path.isdir(src):
                        # Copy into dest_dir/name (make unique if exists)
                        dst = self._ensure_unique_name(dst)
                        shutil.copytree(src, dst, dirs_exist_ok=False)
                    else:
                        # If file exists, create " - Copy" style name
                        if os.path.exists(dst):
                            dst = self._ensure_unique_name(dst)
                        shutil.copy2(src, dst)
                elif self._clipboard_mode == "cut":
                    # If destination exists, move into a unique name
                    if os.path.exists(dst):
                        dst = self._ensure_unique_name(dst)
                    shutil.move(src, dst)
            # If we moved (cut), clear clipboard afterwards
            if self._clipboard_mode == "cut":
                self._file_clipboard = []
                self._clipboard_mode = None
                # Clear 'cut' visuals after paste
                try:
                    self.fs_model.set_cut_marked([])
                except Exception:
                    pass                
        except Exception as e:
            QMessageBox.critical(self, "Paste Failed", str(e))
        finally:
            QApplication.restoreOverrideCursor()

    def _new_folder(self, dest_dir: str):
        name, ok = QInputDialog.getText(self, "New folder", "Folder name:", text="New Folder")
        if not ok or not name.strip():
            return
        folder = os.path.join(dest_dir, name.strip())
        if os.path.exists(folder):
            QMessageBox.warning(self, "New Folder", "A file/folder with that name already exists.")
            return
        try:
            os.makedirs(folder, exist_ok=False)
        except Exception as e:
            QMessageBox.critical(self, "New Folder Failed", str(e))

    def _trash_paths(self, paths: List[str]):
        """Move multiple items to Recycle Bin/Trash with a single confirmation."""
        if not paths:
            return
        if len(paths) == 1:
            return self._trash_path(paths[0])
        sample = os.path.basename(paths[0]) or paths[0]
        reply = QMessageBox.question(
            self, "Move to Recycle Bin",
            f"Do you want to move {len(paths)} items to Recycle Bin?\n\nFirst: {sample}",
            QMessageBox.Yes | QMessageBox.No,
            defaultButton=QMessageBox.Yes
        )
        if reply != QMessageBox.Yes:
            return
        try:
            QApplication.setOverrideCursor(Qt.WaitCursor)
            for p in paths:
                try:
                    if _HAVE_SEND2TRASH and send2trash:
                        send2trash(p)
                    elif platform.system() == "Windows":
                        # Windows fallback to Recycle Bin via Shell API
                        import ctypes
                        import ctypes.wintypes as wt
                        SHFileOperationW = ctypes.windll.shell32.SHFileOperationW
                        FO_DELETE = 3
                        FOF_ALLOWUNDO = 0x0040
                        FOF_NOCONFIRMATION = 0x0010
                        class SHFILEOPSTRUCTW(ctypes.Structure):
                            _fields_ = [
                                ("hwnd", wt.HWND), ("wFunc", wt.UINT),
                                ("pFrom", wt.LPCWSTR), ("pTo", wt.LPCWSTR),
                                ("fFlags", wt.USHORT), ("fAnyOperationsAborted", wt.BOOL),
                                ("hNameMappings", wt.LPVOID), ("lpszProgressTitle", wt.LPCWSTR),
                            ]
                        pFrom = p + "\x00\x00"
                        op = SHFILEOPSTRUCTW(0, FO_DELETE, pFrom, None,
                                             FOF_ALLOWUNDO | FOF_NOCONFIRMATION, False, None, None)
                        res = SHFileOperationW(ctypes.byref(op))
                        if res != 0:
                            raise OSError(f"Recycle Bin move failed (code {res}) for {p}")
                    else:
                        raise RuntimeError("Please install Send2Trash:  pip install Send2Trash")
                except Exception as e:
                    QMessageBox.warning(self, "Trash Error", f"{p}\n\n{e}")
        finally:
            QApplication.restoreOverrideCursor()
            # Clear any cut overlay after trash
            try:
                self.fs_model.set_cut_marked([])
            except Exception:  
                pass

    def _delete_paths_permanent(self, paths: List[str]):
        """Permanently delete multiple items with a single confirmation."""
        if not paths:
            return
        if len(paths) == 1:
            return self._delete_path_permanent(paths[0])
        sample = os.path.basename(paths[0]) or paths[0]
        reply = QMessageBox.warning(
            self, "Delete Permanently",
            f"PERMANENTLY delete {len(paths)} items? This cannot be undone.\n\nFirst: {sample}",
            QMessageBox.Yes | QMessageBox.No,
            defaultButton=QMessageBox.No
        )
        if reply != QMessageBox.Yes:
            return
        for p in paths:
            try:
                if os.path.isdir(p):
                    shutil.rmtree(p)
                else:
                    os.remove(p)
            except Exception as e:
                QMessageBox.critical(self, "Permanent Delete Failed", f"{p}\n\n{e}")
        # Clear any cut overlay after permanent delete
        try:
            self.fs_model.set_cut_marked([])
        except Exception:
            pass

    def _open_terminal_here(self, dir_path: str):
        try:
            if not os.path.isdir(dir_path):
                dir_path = os.path.dirname(dir_path) or dir_path
            if platform.system() == "Windows":
                subprocess.Popen(["cmd.exe", "/K", "cd", "/d", dir_path], shell=True)
            elif platform.system() == "Darwin":
                subprocess.Popen(["open", "-a", "Terminal", dir_path])
            else:
                # Best-effort on Linux (user may have different terminal)
                for cand in (["x-terminal-emulator"], ["gnome-terminal", "--working-directory", dir_path],
                             ["konsole", "--workdir", dir_path], ["xfce4-terminal", "--working-directory", dir_path]):
                    try:
                        subprocess.Popen(cand if len(cand) > 1 else cand + [dir_path])
                        break
                    except Exception:
                        continue
        except Exception as e:
            QMessageBox.warning(self, "Open Terminal Failed", str(e))

    def _show_properties(self, path: str):
        try:
            st = os.stat(path)
            kind = "Folder" if os.path.isdir(path) else "File"
            size = st.st_size if os.path.isfile(path) else None
            mtime = human_time(st.st_mtime)
            lines = [
                f"Path: {path}",
                f"Type: {kind}",
                f"Size: {format_bytes(size) if size is not None else '-'}",
                f"Modified: {mtime}",
            ]
            # If your DirectorySizeModel has a computed folder size, show it:
            if os.path.isdir(path):
                try:
                    idx = self.fs_model.index(path)
                    if idx.isValid():
                        size_idx = idx.sibling(idx.row(), 1)
                        # Use the model's internal cache if present
                        if hasattr(self.fs_model, "_sizes"):
                            folder_size = self.fs_model._sizes.get(path)
                            if folder_size is not None:
                                lines[2] = f"Size: {format_bytes(int(folder_size))} (computed)"
                except Exception:
                    pass
            QMessageBox.information(self, "Properties", "\n".join(lines))
        except Exception as e:
            QMessageBox.warning(self, "Properties", str(e))

    def _install_shortcuts(self):
        """Create global actions with keyboard shortcuts for file operations."""
        # Scope: work anywhere in the window (tree/tabs focus etc.)
        ctx = Qt.WidgetWithChildrenShortcut

        # Copy (Ctrl+C / ⌘C)
        self.act_copy_global = QAction("Copy", self)
        self.act_copy_global.setShortcut(QKeySequence.Copy)
        self.act_copy_global.setShortcutContext(ctx)
        self.act_copy_global.triggered.connect(self._shortcut_copy)
        self.addAction(self.act_copy_global)

        # Cut (Ctrl+X / ⌘X)
        self.act_cut_global = QAction("Cut", self)
        self.act_cut_global.setShortcut(QKeySequence.Cut)
        self.act_cut_global.setShortcutContext(ctx)
        self.act_cut_global.triggered.connect(self._shortcut_cut)
        self.addAction(self.act_cut_global)

        # Paste (Ctrl+V / ⌘V)
        self.act_paste_global = QAction("Paste", self)
        self.act_paste_global.setShortcut(QKeySequence.Paste)
        self.act_paste_global.setShortcutContext(ctx)
        self.act_paste_global.triggered.connect(self._shortcut_paste)
        self.addAction(self.act_paste_global)

        # Delete (Del) -> Recycle Bin / Trash
        self.act_delete_global = QAction("Move to Recycle Bin", self)
        self.act_delete_global.setShortcut(QKeySequence.Delete)
        self.act_delete_global.setShortcutContext(ctx)
        self.act_delete_global.triggered.connect(self._shortcut_delete_to_trash)
        self.addAction(self.act_delete_global)

        # Permanent Delete (ShiftDel)
        self.act_delete_perm_global = QAction("Delete Permanently", self)
        self.act_delete_perm_global.setShortcut(QKeySequence("ShiftDelete"))
        self.act_delete_perm_global.setShortcutContext(ctx)
        self.act_delete_perm_global.triggered.connect(self._shortcut_delete_permanent)
        self.addAction(self.act_delete_perm_global)

        # Rename (F2)
        self.act_rename_global = QAction("Rename", self)
        self.act_rename_global.setShortcut(QKeySequence("F2"))
        self.act_rename_global.setShortcutContext(ctx)
        self.act_rename_global.triggered.connect(self._shortcut_rename)
        self.addAction(self.act_rename_global)

        # New Folder (Ctrl+N / ⌘N)
        self.act_new_folder_global = QAction("New Folder", self)
        if platform.system() == "Darwin":
            self.act_new_folder_global.setShortcut(QKeySequence("Meta+N"))
        else:
            self.act_new_folder_global.setShortcut(QKeySequence("Ctrl+N"))
        self.act_new_folder_global.setShortcutContext(ctx)
        self.act_new_folder_global.triggered.connect(self._shortcut_new_folder)
        self.addAction(self.act_new_folder_global)

        # Copy Path (Ctrl+Shift+C / ⌘⇧C)
        self.act_copy_path_global = QAction("Copy Path", self)
        if platform.system() == "Darwin":
            self.act_copy_path_global.setShortcut(QKeySequence("Meta+Shift+C"))
        else:
            self.act_copy_path_global.setShortcut(QKeySequence("Ctrl+Shift+C"))
        self.act_copy_path_global.setShortcutContext(ctx)
        self.act_copy_path_global.triggered.connect(self._shortcut_copy_path)
        self.addAction(self.act_copy_path_global)

        # Open Terminal here (Ctrl+Alt+T)  – avoids clashing with your theme toggle
        self.act_terminal_global = QAction("Open Terminal here", self)
        self.act_terminal_global.setShortcut(QKeySequence("Ctrl+Alt+T"))
        self.act_terminal_global.setShortcutContext(ctx)
        self.act_terminal_global.triggered.connect(self._shortcut_terminal)
        self.addAction(self.act_terminal_global)

        # Properties (Alt+Enter / Alt+Return)
        self.act_props_global = QAction("Properties", self)
        self.act_props_global.setShortcuts([QKeySequence("Alt+Enter"), QKeySequence("Alt+Return")])
        self.act_props_global.setShortcutContext(ctx)
        self.act_props_global.triggered.connect(self._shortcut_properties)
        self.addAction(self.act_props_global)            

    def _shortcut_copy(self):
        paths = self._selected_paths()
        if not paths:
            path, _ = self._current_path_sel()
            paths = [path] if path else []
        if paths:
            self._copy_paths(paths)

    def _shortcut_cut(self):
        paths = self._selected_paths()
        if not paths:
            path, _ = self._current_path_sel()
            paths = [path] if path else []
        if paths:
            self._cut_paths(paths)

    def _shortcut_paste(self):
        path, is_dir = self._current_path_sel()
        # Default to current root if nothing selected
        dest_dir = None
        if path is not None:
            dest_dir = self._target_dir_for_paste(path, bool(is_dir))
        elif self.current_root:
            dest_dir = self.current_root
        if dest_dir:
            self._paste_paths(dest_dir)

    def _shortcut_delete(self):
        path, _is_dir = self._current_path_sel()
        if path:
            self._delete_path(path)

    def _shortcut_rename(self):
        path, _is_dir = self._current_path_sel()
        if path:
            self._rename_path(path)

    def _shortcut_new_folder(self):
        path, is_dir = self._current_path_sel()
        dest_dir = None
        if path is not None:
            dest_dir = self._target_dir_for_paste(path, bool(is_dir))
        elif self.current_root:
            dest_dir = self.current_root
        if dest_dir:
            self._new_folder(dest_dir)

    def _shortcut_copy_path(self):
        path, _is_dir = self._current_path_sel()
        if path:
            QApplication.clipboard().setText(path)

    def _shortcut_terminal(self):
        path, is_dir = self._current_path_sel()
        dest_dir = None
        if path is not None:
            dest_dir = self._target_dir_for_paste(path, bool(is_dir))
        elif self.current_root:
            dest_dir = self.current_root
        if dest_dir:
            self._open_terminal_here(dest_dir)

    def _shortcut_properties(self):
        path, _is_dir = self._current_path_sel()
        if path:
            self._show_properties(path)
            
    def _shortcut_delete_to_trash(self):
        paths = self._selected_paths()
        if not paths:
            path, _ = self._current_path_sel()
            paths = [path] if path else []
        if paths:
            self._trash_paths(paths)

    def _shortcut_delete_permanent(self):
        paths = self._selected_paths()
        if not paths:
            path, _ = self._current_path_sel()
            paths = [path] if path else []
        if paths:
            self._delete_paths_permanent(paths)          

    def _trash_path(self, path: str):
        """Move a file/folder to Recycle Bin / Trash (default delete)."""
        what = "folder" if os.path.isdir(path) else "file"
        reply = QMessageBox.question(
            self, "Move to Recycle Bin",
            f"Do you want to move this {what} to Recycle Bin?\n\n{path}",
            QMessageBox.Yes | QMessageBox.No,
            defaultButton=QMessageBox.Yes
        )
        if reply != QMessageBox.Yes:
            return

        try:
            if _HAVE_SEND2TRASH and send2trash:
                send2trash(path)
                return

            # Fallback: Windows Shell API (no extra dependency)
            if platform.system() == "Windows":
                import ctypes
                import ctypes.wintypes as wt
                SHFileOperationW = ctypes.windll.shell32.SHFileOperationW
                FO_DELETE = 3
                FOF_ALLOWUNDO = 0x0040      # send to Recycle Bin
                FOF_NOCONFIRMATION = 0x0010 # we've already confirmed
                class SHFILEOPSTRUCTW(ctypes.Structure):
                    _fields_ = [
                        ("hwnd", wt.HWND),
                        ("wFunc", wt.UINT),
                        ("pFrom", wt.LPCWSTR),
                        ("pTo", wt.LPCWSTR),
                        ("fFlags", wt.USHORT),
                        ("fAnyOperationsAborted", wt.BOOL),
                        ("hNameMappings", wt.LPVOID),
                        ("lpszProgressTitle", wt.LPCWSTR),
                    ]
                # pFrom must be double-NULL-terminated and multi-select is \0-separated
                pFrom = path + "\x00\x00"
                op = SHFILEOPSTRUCTW(0, FO_DELETE, pFrom, None,
                                     FOF_ALLOWUNDO | FOF_NOCONFIRMATION, False, None, None)
                res = SHFileOperationW(ctypes.byref(op))
                if res != 0:
                    raise OSError(f"Windows recycle-bin move failed (code {res})")

            else:
                # Non-Windows without Send2Trash: instruct user to install the tiny dependency
                raise RuntimeError("Please install Send2Trash:  pip install Send2Trash")

        except Exception as e:
            QMessageBox.critical(self, "Move to Recycle Bin Failed", str(e))

    def _delete_path_permanent(self, path: str):
        """Permanent delete (Shift+Delete)."""
        what = "folder" if os.path.isdir(path) else "file"
        reply = QMessageBox.warning(
            self, "Delete Permanently",
            f"PERMANENTLY delete this {what}? This cannot be undone.\n\n{path}",
            QMessageBox.Yes | QMessageBox.No,
            defaultButton=QMessageBox.No
        )
        if reply != QMessageBox.Yes:
            return
        try:
            if os.path.isdir(path):
                shutil.rmtree(path)
            else:
                os.remove(path)
        except Exception as e:
            QMessageBox.critical(self, "Permanent Delete Failed", str(e))            

    def _get_parent_dir(self, path: str) -> Optional[str]:
        if not path:
            return None
        norm = os.path.normpath(path)
        parent = os.path.dirname(norm)
        if parent == norm:
            return None
        return parent

    def go_up_one(self):
        if not self.current_root:
            return
        parent = self._get_parent_dir(self.current_root)
        if parent:
            self.set_root(parent)

    def _update_nav_actions(self):
        has_parent = bool(self.current_root and self._get_parent_dir(self.current_root))
        if hasattr(self, "act_up"):
            self.act_up.setEnabled(has_parent)
        if hasattr(self, "btn_up"):
            self.btn_up.setEnabled(has_parent)

    def set_root(self, path: str):
        """Navigate the left tree root to 'path' and (optionally) analyze it."""
        self.current_root = path

        # Update file system model root
        src_index = self.fs_model.index(path)
        proxy_index = self.tree_proxy.mapFromSource(src_index)
        self.tree.setRootIndex(proxy_index)
        self.tree.setCurrentIndex(proxy_index)
        self.tree.expand(proxy_index)
        self.statusBar().showMessage(f"Root: {path}")
        self._update_nav_actions()

        # If auto-analyze, analyze this navigated folder
        if self.auto_analyze:
            self.analyze(path)

    def analyze(self, path: str):
        """Analyze 'path' without changing the left tree root."""
        if not path or not os.path.isdir(path):
            return
        self._stop_worker()

        # Set current analysis target; update Summary root label immediately
        self.analysis_root = path
        self.lbl_root.setText(path)

        self.progress.setVisible(True)
        self.status_label.setText(f"Scanning… {path}")
        self.act_export.setEnabled(False)

        self.worker = StatsWorker(path, top_n=100, parent=self)
        self.worker.progress.connect(self._on_worker_progress)
        self.worker.error.connect(self._on_worker_error)
        self.worker.finished.connect(self._on_worker_finished)
        self.worker.start()

    def rescan(self):
        """Rescan the last analyzed path, or current root if none."""
        target = self.analysis_root or self.current_root
        if not target:
            return
        self.analyze(target)

    def _stop_worker(self):
        if self.worker and self.worker.isRunning():
            self.worker.stop()
            self.worker.wait(500)
        self.worker = None

    @Slot(str)
    def _on_worker_progress(self, text: str):
        self.status_label.setText(text)

    @Slot(str)
    def _on_worker_error(self, err: str):
        self.progress.setVisible(False)
        self.status_label.setText("Error")
        QMessageBox.critical(self, "Scan Error", err)

    @Slot(object)
    def _on_worker_finished(self, result):
        self.progress.setVisible(False)
        if result is None:
            self.status_label.setText("Scan canceled")
            return
        self.status_label.setText(f"Scan complete: {format_bytes(result.total_size)}")
        self._populate_report(result)
        self._apply_numeric_sorting_to_tables()
        self._last_stats = result
        self.act_export.setEnabled(True)

    # ---------- Tree interactions ----------
    def _apply_search(self, text: str):
        self.tree_proxy.setFilterWildcard(f"*{text}*")

    def _apply_filters(self):
        flags = QDir.NoDotAndDotDot | QDir.Drives
        if self.show_files_cb.isChecked():
            flags |= QDir.Files
        if self.show_dirs_cb.isChecked():
            flags |= QDir.AllDirs
        if self.show_hidden_cb.isChecked():
            flags |= QDir.Hidden | QDir.System
        self.fs_model.setFilter(QDir.Filters(flags))
        # Model: load both files & dirs so the tree can navigate;
        # apply Hidden/System only if requested.
        flags = QDir.NoDotAndDotDot | QDir.Drives | QDir.Files | QDir.AllDirs
        if self.show_hidden_cb.isChecked():
            flags |= QDir.Hidden | QDir.System
        self.fs_model.setFilter(QDir.Filters(flags))

        # Proxy: actually show/hide rows per the checkboxes
        self.tree_proxy.setShowFiles(self.show_files_cb.isChecked())
        self.tree_proxy.setShowDirs(self.show_dirs_cb.isChecked())
        self.tree_proxy.setShowHidden(self.show_hidden_cb.isChecked())        
        
    def _toggle_folder_sizes(self, checked: bool):
        """Enable/disable directory size computation/display."""
        try:
            self.fs_model.set_compute_dir_sizes(checked)
        # Nudge the view to re-evaluate & repaint the Size column
            self.tree.viewport().update()        
        except Exception as e:
            QMessageBox.critical(self, "Folder sizes toggle failed", str(e))

    def _tree_context_menu(self, pos):
        index = self.tree.indexAt(pos)
        if not index.isValid():
            return
        src_index = self.tree_proxy.mapToSource(index)
        path = self.fs_model.filePath(src_index)
        is_dir = self.fs_model.isDir(src_index)

        menu = QMenu(self)
        menu.setMouseTracking(True)  # ensure immediate hover highlight
        act_open = QAction("Open", self)
        act_open.triggered.connect(lambda: open_with_default_app(path))
        menu.addAction(act_open)

        act_explorer = QAction("Open in Explorer", self)
        act_explorer.triggered.connect(lambda: open_in_explorer(path))
        menu.addAction(act_explorer)
        
        # New quick utility
        act_copy_path = QAction("Copy Path", self)
        act_copy_path.triggered.connect(lambda: QApplication.clipboard().setText(path))
        menu.addAction(act_copy_path)

        menu.addSeparator()

        act_expand = QAction("Expand", self)
        act_expand.triggered.connect(lambda: self.tree.expand(index))
        menu.addAction(act_expand)
        act_collapse = QAction("Collapse", self)
        act_collapse.triggered.connect(lambda: self.tree.collapse(index))
        menu.addAction(act_collapse)

        act_expand_all = QAction("Expand All (careful)", self)
        act_expand_all.triggered.connect(lambda: self.tree.expandRecursively(index))
        menu.addAction(act_expand_all)

        menu.addSeparator()
        act_analyze_here = QAction("Analyze This Folder", self)
        act_analyze_here.triggered.connect(
            lambda: self.analyze(path if is_dir else os.path.dirname(path))
        )
        menu.addAction(act_analyze_here)
        
        # --- NEW: File operations ---
        menu.addSeparator()

        # Copy / Cut / Paste
        sel_paths = self._selected_paths()
        targets = sel_paths if sel_paths else [path]
        multi = len(targets) > 1
    
        act_copy = QAction("Copy", self)
        act_copy.triggered.connect(lambda: self._copy_paths(targets))
        menu.addAction(act_copy)

        act_cut = QAction("Cut", self)
        act_cut.triggered.connect(lambda: self._cut_paths(targets))
        menu.addAction(act_cut)

        dest_dir = self._target_dir_for_paste(path, is_dir)
        act_paste = QAction(f"Paste into '{os.path.basename(dest_dir) or dest_dir}'", self)
        act_paste.setEnabled(bool(self._file_clipboard))
        act_paste.triggered.connect(lambda: self._paste_paths(dest_dir))
        menu.addAction(act_paste)

        menu.addSeparator()

        # Rename / Delete / New Folder
        act_rename = QAction("Rename", self)
        act_rename.setEnabled(not multi)  # Rename only when a single item is selected
        act_rename.triggered.connect(lambda: self._rename_path(path))
        menu.addAction(act_rename)

        # Default delete: send to Recycle Bin / Trash
        act_delete = QAction("Move to Recycle Bin", self)
        act_delete.triggered.connect(lambda: self._trash_paths(targets))
        menu.addAction(act_delete)
        
        # Optional: permanent delete (Shift+Delete)
        act_delete_perm = QAction("Delete Permanently", self)
        act_delete_perm.triggered.connect(lambda: self._delete_paths_permanent(targets))
        menu.addAction(act_delete_perm)

        # Show hints next to menu items (purely visual)
        if hasattr(self, "act_delete_global"):
            act_delete.setShortcuts(self.act_delete_global.shortcuts())
        if hasattr(self, "act_delete_perm_global"):
            act_delete_perm.setShortcuts(self.act_delete_perm_global.shortcuts())             

        act_new_folder = QAction("New Folder", self)
        act_new_folder.triggered.connect(lambda: self._new_folder(dest_dir))
        menu.addAction(act_new_folder)

        menu.addSeparator()

        # Open Terminal  Properties
        act_terminal = QAction("Open Terminal here", self)
        act_terminal.triggered.connect(lambda: self._open_terminal_here(dest_dir))
        menu.addAction(act_terminal)

        act_props = QAction("Properties", self)
        act_props.triggered.connect(lambda: self._show_properties(path))
        menu.addAction(act_props)        

        menu.exec(self.tree.viewport().mapToGlobal(pos))

    def _tree_double_clicked(self, index: QModelIndex):
        src_index = self.tree_proxy.mapToSource(index)
        path = self.fs_model.filePath(src_index)
        if self.fs_model.isDir(src_index):
            # Navigate (change left root) on double-click
            self._suppress_next_selection_analyze = False
            self.set_root(path)
        else:
            open_with_default_app(path)

    def _tree_selection_changed(self, *_):
        # If navigation (double-click) just happened, skip this one auto-analyze
        if self._suppress_next_selection_analyze:
            self._suppress_next_selection_analyze = False
            return
        if not self.auto_analyze:
            return
        index = self.tree.currentIndex()
        if not index.isValid():
            return
        src_index = self.tree_proxy.mapToSource(index)
        path = self.fs_model.filePath(src_index)
        folder = path if self.fs_model.isDir(src_index) else os.path.dirname(path)
        # Debounce rapid selections; analyze without navigating
        QTimer.singleShot(200, lambda: self.analyze(folder))

    # ---------- Report population ----------
    def _populate_report(self, stats: FolderStats):
        # Summary
        self.lbl_root.setText(stats.root)
        self.lbl_total_size.setText(format_bytes(stats.total_size))
        self.lbl_total_files.setText(f"{stats.total_files:,}")
        self.lbl_total_dirs.setText(f"{stats.total_dirs:,}")
        avg = stats.total_size / stats.total_files if stats.total_files > 0 else 0
        self.lbl_avg_size.setText(format_bytes(int(avg)))
        self.lbl_mtime_range.setText(f"{human_time(stats.mtime_min)}  →  {human_time(stats.mtime_max)}")

        if stats.errors:
            self.statusBar().showMessage(f"{len(stats.errors)} items skipped due to errors/permissions.")

        # File types table
        self._fill_types_table(stats)
        # Subfolders table
        self._fill_subfolders_table(stats)
        # Largest files table
        self._fill_largest_files_table(stats)

    # --- 2) ADD THIS METHOD INSIDE MainWindow (e.g., below _populate_report) ---
    def _apply_numeric_sorting_to_tables(self):
        """
        Replace display-only items with NumericItem in numeric columns so sorting
        uses the raw bytes/count values instead of the formatted text.
        """
        # (table, numeric columns)
        tables = [
            (self.types_table,      [1, 2]),  # Count, Total Size
            (self.subfolders_table, [1]),     # Size
            (self.largest_table,    [1]),     # Size
        ]

        for table, num_cols in tables:
            if table is None:
                continue

            # Preserve current sort indicator
            header = table.horizontalHeader()
            current_col = header.sortIndicatorSection()
            current_order = header.sortIndicatorOrder()
            was_sorting = table.isSortingEnabled()

            table.setSortingEnabled(False)
            for r in range(table.rowCount()):
                for c in num_cols:
                    item = table.item(r, c)
                    if not item:
                        continue
                    raw = item.data(Qt.UserRole)
                    text = item.text()
                    # Fallback if no raw value was stored
                    raw = int(raw) if isinstance(raw, (int, float)) else 0
                    new_item = NumericItem(text, raw)
                    new_item.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
                    table.setItem(r, c, new_item)

            table.setSortingEnabled(was_sorting)
            if was_sorting:
                # Re-apply the sort the user last selected
                table.sortItems(current_col, current_order)

    def _fill_types_table(self, stats: FolderStats):
        rows = []
        for ext, count in stats.ext_counts.items():
            size = stats.ext_sizes.get(ext, 0)
            rows.append((ext, count, size))
        rows.sort(key=lambda x: x[2], reverse=True)

        was_sorting = self.types_table.isSortingEnabled()
        self.types_table.setSortingEnabled(False)
        self.types_table.clearContents()
        self.types_table.setRowCount(len(rows))

        for r, (ext, count, size) in enumerate(rows):
            self.types_table.setItem(r, 0, QTableWidgetItem(ext))

            cnt_item = QTableWidgetItem(f"{count:,}")
            cnt_item.setData(Qt.UserRole, count)
            cnt_item.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
            self.types_table.setItem(r, 1, cnt_item)

            size_item = QTableWidgetItem(format_bytes(size))
            size_item.setData(Qt.UserRole, size)
            size_item.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
            self.types_table.setItem(r, 2, size_item)

        self.types_table.setSortingEnabled(was_sorting)
        if was_sorting:
            self.types_table.sortItems(2, Qt.DescendingOrder)

    def _fill_subfolders_table(self, stats: FolderStats):
        rows = stats.top_subfolders
        self.subfolders_table.setRowCount(len(rows))
        for r, (name, size) in enumerate(rows):
            self.subfolders_table.setItem(r, 0, QTableWidgetItem(name))
            size_item = QTableWidgetItem(format_bytes(size))
            size_item.setData(Qt.UserRole, size)
            size_item.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
            self.subfolders_table.setItem(r, 1, size_item)
        self.subfolders_table.sortItems(1, Qt.DescendingOrder)

    def _fill_largest_files_table(self, stats: FolderStats):
        rows = stats.largest_files
        self.largest_table.setRowCount(len(rows))
        for r, (path, size) in enumerate(rows):
            self.largest_table.setItem(r, 0, QTableWidgetItem(path))
            size_item = QTableWidgetItem(format_bytes(size))
            size_item.setData(Qt.UserRole, size)
            size_item.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
            self.largest_table.setItem(r, 1, size_item)
        self.largest_table.sortItems(1, Qt.DescendingOrder)

    # ---------- Export ----------
    def export_html(self):
        """Export a detailed HTML report for the last analysis."""
        if not hasattr(self, "_last_stats") or self._last_stats is None:
            return

        stats: FolderStats = self._last_stats
        default_name = f"folder_report_{int(time.time())}.html"
        path, _ = QFileDialog.getSaveFileName(
            self,
            "Export report as HTML",
            default_name,
            "HTML Files (*.html)"
        )
        if not path:
            return

        def esc(x) -> str:
            return html.escape("" if x is None else str(x), quote=True)

        # Summary values
        exported_at = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
        root = esc(stats.root)
        total_size_h = esc(format_bytes(stats.total_size))
        total_files_h = f"{stats.total_files:,}"
        total_dirs_h = f"{stats.total_dirs:,}"
        avg = stats.total_size / stats.total_files if stats.total_files > 0 else 0
        avg_size_h = esc(format_bytes(int(avg)))
        mtime_range = f"{esc(human_time(stats.mtime_min))} → {esc(human_time(stats.mtime_max))}"

        # File types (sorted by total size desc)
        types_rows = []
        for ext, cnt in stats.ext_counts.items():
            size = stats.ext_sizes.get(ext, 0)
            types_rows.append((ext, cnt, size))
        types_rows.sort(key=lambda x: x[2], reverse=True)

        # Top subfolders (already sorted desc by size in StatsWorker)
        sub_rows = stats.top_subfolders or []

        # Largest files
        large_rows = stats.largest_files or []

        # --- Precompute the dynamic table bodies safely (no complex expressions inside main f-string) ---
        types_body = "".join(
            (
                f"<tr>"
                f"<td>{esc(ext)}</td>"
                f"<td class='num'>{cnt:,}</td>"
                f"<td class='num'>{esc(format_bytes(size))}</td>"
                f"</tr>"
            )
            for ext, cnt, size in types_rows
        )

        sub_body = "".join(
            (
                f"<tr>"
                f"<td>{esc(name)}</td>"
                f"<td class='num'>{esc(format_bytes(sz))}</td>"
                f"</tr>"
            )
            for name, sz in sub_rows
        )

        files_body = "".join(
            (
                f"<tr>"
                f"<td>{esc(p)}</td>"
                f"<td class='num'>{esc(format_bytes(sz))}</td>"
                f"</tr>"
            )
            for p, sz in large_rows
        )

        errors_html = (
            "<div class='small'>None</div>"
            if not stats.errors
            else "<pre>" + esc("\n".join(stats.errors)) + "</pre>"
        )

        # --- Static parts + simple variable interpolation only ---
        # NOTE: CSS braces are doubled in f-strings ({{ }}) to render as literal { }
        html_top = f"""<!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="utf-8">
      <meta name="viewport" content="width=device-width, initial-scale=1">
      <title>Folder Report — {root}</title>
      <style>
        :root {{
          --bg: #ffffff;
          --fg: #1e1e1e;
          --muted: #666;
          --line: #ddd;
          --head: #f0f0f0;
          --accent: #0b6cfb;
        }}
        html, body {{ background: var(--bg); color: var(--fg); font: 14px/1.4 -apple-system,BlinkMacSystemFont,Segoe UI,Roboto,Segoe UI Emoji,Segoe UI Symbol,Arial,sans-serif; margin: 0; }}
        .wrap {{ max-width: 1100px; margin: 24px auto; padding: 0 16px; }}
        h1 {{ font-size: 22px; margin: 0 0 8px; }}
        h2 {{ font-size: 18px; margin: 24px 0 8px; }}
        .meta {{ color: var(--muted); margin-bottom: 16px; }}
        table {{ width: 100%; border-collapse: collapse; margin: 8px 0 16px; }}
        th, td {{ border: 1px solid var(--line); padding: 6px 8px; vertical-align: top; }}
        th {{ background: var(--head); text-align: left; }}
        td.num {{ text-align: right; white-space: nowrap; }}
        code, pre {{ background: #fafafa; border: 1px solid var(--line); padding: 8px; display: block; white-space: pre-wrap; word-break: break-word; }}
        .small {{ color: var(--muted); font-size: 12px; }}
      </style>
    </head>
    <body>
      <div class="wrap">
        <h1>Folder Report</h1>
        <div class="meta small">
          <div><b>Analyzed Path:</b> {root}</div>
          <div><b>Exported:</b> {esc(exported_at)}</div>
          <div><b>App:</b> Explorer by Anmol</div>
        </div>

        <h2>Summary</h2>
        <table>
          <tbody>
            <tr><th>Total Size</th><td>{total_size_h}</td></tr>
            <tr><th>Total Files</th><td class="num">{total_files_h}</td></tr>
            <tr><th>Total Folders</th><td class="num">{total_dirs_h}</td></tr>
            <tr><th>Average File Size</th><td>{avg_size_h}</td></tr>
            <tr><th>Modified Range</th><td>{mtime_range}</td></tr>
          </tbody>
        </table>

        <h2>File Types</h2>
        <table>
          <thead>
            <tr>
              <th>Extension</th>
              <th>Count</th>
              <th>Total Size</th>
            </tr>
          </thead>
          <tbody>
    """

        mid2 = """
          </tbody>
        </table>

        <h2>Top-level Subfolders</h2>
        <table>
          <thead>
            <tr>
              <th>Subfolder</th>
              <th>Size</th>
            </tr>
          </thead>
          <tbody>
    """

        mid3 = """
          </tbody>
        </table>

        <h2>Largest Files</h2>
        <table>
          <thead>
            <tr>
              <th>Path</th>
              <th>Size</th>
            </tr>
          </thead>
          <tbody>
    """

        footer = f"""
          </tbody>
        </table>

        <h2>Errors</h2>
        {errors_html}

        <div class="small">© {time.strftime("%Y")} Explorer by Anmol</div>
      </div>
    </body>
    </html>"""

        html_doc = html_top + types_body + mid2 + sub_body + mid3 + files_body + footer

        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write(html_doc)
            self.statusBar().showMessage(f"Exported: {path}", 5000)
        except Exception as e:
            QMessageBox.critical(self, "Export Failed", str(e))


    # ---------- Close event ----------
    def closeEvent(self, event):
        self._stop_worker()
        super().closeEvent(event)

    # ---------- Expand/Collapse ----------
    def expand_all(self):
        self.tree.expandAll()

    def collapse_all(self):
        self.tree.collapseAll()


def main():
    app = QApplication(sys.argv)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
