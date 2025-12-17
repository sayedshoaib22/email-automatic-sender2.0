import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
import pandas as pd
import smtplib, ssl
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.image import MIMEImage
from email.mime.base import MIMEBase
from email import encoders
import mimetypes
from datetime import datetime
import threading
import re
import os
import html
import json
import sqlite3
from PIL import Image, ImageTk  # Required for Logo/Watermark handling

# ------------------ CONFIG ------------------
SENDER_EMAIL = "vartisticstudio@gmail.com"
SENDER_APP_PASSWORD = "ncei olgn ykrl bwop"   # DO NOT SHARE THIS FILE PUBLICLY
SMTP_SERVER = "smtp.gmail.com"
SMTP_PORT = 587

EMAIL_REGEX = re.compile(r"[^@]+@[^@]+\.[^@]+")
PLACEHOLDER_REGEX = re.compile(r"\{([^}]+)\}")

# Possible column names
NAME_COLUMN_CANDIDATES = {"name", "names", "full name", "customer name", "student name"}
EMAIL_COLUMN_CANDIDATES = {"email", "emails", "e-mail", "mail", "mail id", "email id", "gmail"}
SUBJECT_COLUMN_CANDIDATES = {"subject", "heading", "title"}
BODY_COLUMN_CANDIDATES = {"body", "message", "content", "description"}

DB_FILE = "mailer.db"


# ------------------ SQLITE HELPERS ------------------
def init_sqlite():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS sent_emails (
        email TEXT PRIMARY KEY,
        sent_at TEXT
    )''')
    c.execute('''CREATE TABLE IF NOT EXISTS recovery_state (
        id INTEGER PRIMARY KEY CHECK (id = 1),
        file_path TEXT,
        current_index INTEGER
    )''')
    conn.commit()
    conn.close()


def sqlite_load_sent_emails():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute("SELECT email FROM sent_emails")
    rows = c.fetchall()
    conn.close()
    return set(r[0].strip().lower() for r in rows)


def sqlite_save_sent_email(email):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    sent_at = datetime.now().isoformat()
    try:
        c.execute("INSERT OR IGNORE INTO sent_emails (email, sent_at) VALUES (?, ?)", (email.strip().lower(), sent_at))
        conn.commit()
    except:
        pass
    conn.close()


def sqlite_load_recovery_state():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute("SELECT file_path, current_index FROM recovery_state WHERE id = 1")
    row = c.fetchone()
    conn.close()
    if row:
        return {"file_path": row[0], "current_index": row[1]}
    return None


def sqlite_save_recovery_state(file_path, current_index):
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute("INSERT OR REPLACE INTO recovery_state (id, file_path, current_index) VALUES (1, ?, ?)", (file_path, int(current_index)))
    conn.commit()
    conn.close()


def sqlite_clear_recovery_state():
    conn = sqlite3.connect(DB_FILE)
    c = conn.cursor()
    c.execute("DELETE FROM recovery_state WHERE id = 1")
    conn.commit()
    conn.close()


# ------------------ APP CLASS ------------------
class EmailAutomationApp:
    def __init__(self, root):
        init_sqlite()
        self.root = root
        self.root.title("Vartistic Studio | Pro Mailer Engine")
        self.root.geometry("1300x850")
        self.root.minsize(1200, 750)
        
        # Logic Variables
        self.file_path = None
        self.selected_image_path = None
        self.inline_images = []
        self.general_attachments = [] # NEW: For files/videos/photos
        self.image_url_column = ""
        self.is_sending = False

        self.skip_duplicates_in_file = tk.BooleanVar(value=True)
        self.respect_global_history = tk.BooleanVar(value=False)
        self.mark_excel_with_status = tk.BooleanVar(value=False)
        self.use_row_content = tk.BooleanVar(value=False)

        self.sent_count = 0
        self.failed_count = 0
        self.skipped_count = 0
        self.total_count = 0

        self.state_file = "email_state.json"
        self.resume_from_index = 0
        self.resuming = False
        self.sent_email_store = "sent_emails.json"
        self.sent_emails_global = self._load_sent_emails()
        self.result_rows = []

        # UI Initialization
        self._setup_style()
        self.create_ui()
        self._check_recovery_state()

    # ------------------ DARK THEME STYLING ------------------
    def _setup_style(self):
        style = ttk.Style()
        try:
            style.theme_use("alt")
        except tk.TclError:
            pass

        self.colors = {
            "bg_dark": "#1e1e1e",
            "panel_bg": "#252526",
            "input_bg": "#3c3c3c",
            "text_main": "#ffffff",
            "text_dim": "#cccccc",
            "accent": "#007acc",
            "accent_hover": "#0098ff",  
            "success": "#4ec9b0",
            "warning": "#ce9178",
            "border": "#3e3e42"
        }

        self.root.configure(bg=self.colors["bg_dark"])

        style.configure("Main.TFrame", background=self.colors["bg_dark"])
        style.configure("Panel.TFrame", background=self.colors["panel_bg"], relief="flat")
        
        style.configure("H1.TLabel", background=self.colors["bg_dark"], foreground=self.colors["text_main"], font=("Segoe UI", 24, "bold"))
        style.configure("H2.TLabel", background=self.colors["panel_bg"], foreground=self.colors["accent"], font=("Segoe UI", 14, "bold"))
        style.configure("Label.TLabel", background=self.colors["panel_bg"], foreground=self.colors["text_dim"], font=("Segoe UI", 10))

        # Buttons
        style.configure("Accent.TButton", background=self.colors["accent"], foreground="white", font=("Segoe UI", 11, "bold"), borderwidth=0, padding=10)
        style.map("Accent.TButton", background=[("active", self.colors["accent_hover"])])

        style.configure("Dark.TButton", background=self.colors["input_bg"], foreground=self.colors["text_main"], borderwidth=1, font=("Segoe UI", 10))
        style.map("Dark.TButton", background=[("active", "#505050")])

        # --- MODIFIED CHECKBUTTON (Removed white selection box) ---
        style.configure("TCheckbutton", 
                        background=self.colors["panel_bg"], 
                        foreground=self.colors["text_main"], 
                        font=("Segoe UI", 10),
                        focuscolor=self.colors["panel_bg"]) # Removes the focus border
        style.map("TCheckbutton", 
                  background=[("active", self.colors["panel_bg"]), ("selected", self.colors["panel_bg"])],
                  foreground=[("active", self.colors["text_main"])],
                  indicatorcolor=[("selected", self.colors["accent"]), ("!selected", self.colors["bg_dark"])])

        style.configure("TEntry", fieldbackground=self.colors["input_bg"], foreground="white", insertcolor="white", borderwidth=0)
        style.configure("StatNum.TLabel", background=self.colors["input_bg"], foreground=self.colors["text_main"], font=("Consolas", 22, "bold"))

    def create_ui(self):
        # --- HEADER ---
        header = ttk.Frame(self.root, style="Main.TFrame", padding=(20, 20, 20, 0))
        header.pack(fill="x")
        
        # LOGO INTEGRATION (TOP LEFT)
        try:
            logo_img = Image.open("logo.png")
            logo_img = logo_img.resize((150, 80), Image.Resampling.LANCZOS)
            self.logo_photo = ImageTk.PhotoImage(logo_img)
            logo_label = tk.Label(header, image=self.logo_photo, bg=self.colors["bg_dark"])
            logo_label.pack(side="left", padx=(10, 10))
        except:
            pass # Logo file missing

        ttk.Label(header, text="VARTISTIC STUDIO | AUTOMATION ENGINE", style="H1.TLabel").pack(side="left")
        
        status_frame = ttk.Frame(header, style="Main.TFrame")
        status_frame.pack(side="right")
        self.status_dot = tk.Label(status_frame, text="●", bg=self.colors["bg_dark"], fg="#555555", font=("Arial", 16))
        self.status_dot.pack(side="left")
        self.status_text = tk.Label(status_frame, text="SYSTEM IDLE", bg=self.colors["bg_dark"], fg="#555555", font=("Segoe UI", 10, "bold"))
        self.status_text.pack(side="left", padx=5)

        # --- MAIN CONTENT SPLIT ---
        main_body = ttk.Frame(self.root, style="Main.TFrame", padding=20)
        main_body.pack(fill="both", expand=True)

        left_col = ttk.Frame(main_body, style="Main.TFrame")
        left_col.pack(side="left", fill="both", expand=True, padx=(0, 10))

        right_col = ttk.Frame(main_body, style="Main.TFrame")
        right_col.pack(side="right", fill="both", expand=True, padx=(10, 0))

        # --- PANEL 1: DATA SOURCE ---
        p1 = ttk.Frame(left_col, style="Panel.TFrame", padding=15)
        p1.pack(fill="x", pady=(0, 15))
        
        ttk.Label(p1, text="1. DATA SOURCE", style="H2.TLabel").pack(anchor="w", pady=(0, 10))
        file_row = ttk.Frame(p1, style="Panel.TFrame")
        file_row.pack(fill="x")
        self.file_label = ttk.Label(file_row, text="No file loaded", background=self.colors["input_bg"], foreground=self.colors["text_dim"], padding=8, width=40)
        self.file_label.pack(side="left", fill="x", expand=True, padx=(0, 10))
        ttk.Button(file_row, text="BROWSE FILES", style="Dark.TButton", command=self.browse_file).pack(side="right")

        conf_grid = ttk.Frame(p1, style="Panel.TFrame")
        conf_grid.pack(fill="x", pady=(15, 0))
        ttk.Checkbutton(conf_grid, text="Skip Duplicates (File)", variable=self.skip_duplicates_in_file).grid(row=0, column=0, sticky="w", padx=10, pady=5)
        ttk.Checkbutton(conf_grid, text="Global History Check", variable=self.respect_global_history).grid(row=0, column=1, sticky="w", padx=10, pady=5)
        ttk.Checkbutton(conf_grid, text="Mark Excel Status", variable=self.mark_excel_with_status).grid(row=1, column=0, sticky="w", padx=10, pady=5)
        ttk.Checkbutton(conf_grid, text="Per-Row Content", variable=self.use_row_content).grid(row=1, column=1, sticky="w", padx=10, pady=5)

        # --- PANEL 2: COMPOSER ---
        p2 = ttk.Frame(left_col, style="Panel.TFrame", padding=15)
        p2.pack(fill="both", expand=True, pady=(0, 15))
        ttk.Label(p2, text="2. MESSAGE COMPOSER", style="H2.TLabel").pack(anchor="w", pady=(0, 10))

        ttk.Label(p2, text="Subject Line", style="Label.TLabel").pack(anchor="w")
        self.subject_entry = tk.Entry(p2, bg=self.colors["input_bg"], fg="white", insertbackground="white", relief="flat", font=("Segoe UI", 11))
        self.subject_entry.pack(fill="x", ipady=5, pady=(2, 10))

        ttk.Label(p2, text="Email Body (HTML)", style="Label.TLabel").pack(anchor="w")
        self.body_text = scrolledtext.ScrolledText(p2, height=8, bg=self.colors["input_bg"], fg="white", insertbackground="white", relief="flat", font=("Consolas", 10))
        self.body_text.pack(fill="both", expand=True, pady=(2, 10))

        # NEW: ATTACHMENTS AREA
        attach_frame = ttk.Frame(p2, style="Panel.TFrame")
        attach_frame.pack(fill="x")
        
        # Inline Images
        img_row = ttk.Frame(attach_frame, style="Panel.TFrame")
        img_row.pack(side="left")
        ttk.Button(img_row, text="+ INLINE IMAGES", style="Dark.TButton", command=self.browse_image).pack(side="left")
        self.image_label = ttk.Label(img_row, text="0 images", style="Label.TLabel")
        self.image_label.pack(side="left", padx=5)

        # General Files (NEW)
        gen_row = ttk.Frame(attach_frame, style="Panel.TFrame")
        gen_row.pack(side="right")
        ttk.Button(gen_row, text="+ ATTACH FILES/VIDEO", style="Dark.TButton", command=self.browse_general_files).pack(side="left")
        self.gen_attach_label = ttk.Label(gen_row, text="0 files", style="Label.TLabel")
        self.gen_attach_label.pack(side="left", padx=5)

        # --- PANEL 3: ACTIONS ---
        p3 = ttk.Frame(left_col, style="Panel.TFrame", padding=15)
        p3.pack(fill="x")
        self.recovery_btn = ttk.Button(p3, text="↺ RECOVERY TOOLS", style="Dark.TButton", command=self.open_recovery_window)
        self.recovery_btn.pack(side="left")
        self.send_btn = ttk.Button(p3, text="INITIATE SEQUENCE ➤", style="Accent.TButton", command=self.start_sending)
        self.send_btn.pack(side="right", fill="x", expand=True, padx=(10, 0))

        # --- STATS & LOGS ---
        stats_frame = ttk.Frame(right_col, style="Main.TFrame")
        stats_frame.pack(fill="x", pady=(0, 15))
        
        def make_stat_box(parent, title, var_name, color):
            box = tk.Frame(parent, bg=self.colors["input_bg"], padx=15, pady=10)
            box.pack(side="left", fill="x", expand=True, padx=4)
            tk.Label(box, text=title, bg=self.colors["input_bg"], fg=self.colors["text_dim"], font=("Segoe UI", 9, "bold")).pack(anchor="w")
            lbl_val = tk.Label(box, text="0", bg=self.colors["input_bg"], fg=color, font=("Consolas", 26, "bold"))
            lbl_val.pack(anchor="e")
            setattr(self, var_name, lbl_val)

        make_stat_box(stats_frame, "SENT", "lbl_sent", self.colors["success"])
        make_stat_box(stats_frame, "FAILED", "lbl_failed", self.colors["warning"])
        make_stat_box(stats_frame, "SKIPPED", "lbl_skipped", "#888888")

        # --- TERMINAL LOG WITH WATERMARK ---
        log_panel = ttk.Frame(right_col, style="Panel.TFrame")
        log_panel.pack(fill="both", expand=True)

        # The Log Box
        self.log_box = scrolledtext.ScrolledText(
            log_panel, state="disabled", background="#000000", foreground="#00ff00",
            insertbackground="#00ff00", font=("Consolas", 9), borderwidth=0, padx=10, pady=10
        )
        self.log_box.pack(fill="both", expand=True)

        # WATERMARK INTEGRATION (Bottom Right of Log Panel)
        self._add_watermark(log_panel)

    def _add_watermark(self, parent):
        try:
            w_img = Image.open("logo.png").convert("RGBA")
            # Make it 150px wide and very transparent (alpha 30/255)
            w_img.thumbnail((180, 180))
            datas = w_img.getdata()
            newData = []
            for item in datas:
                # item is (r, g, b, a) -> reduce 'a' for transparency
                newData.append((item[0], item[1], item[2], int(item[3] * 0.15))) 
            w_img.putdata(newData)
            
            self.watermark_photo = ImageTk.PhotoImage(w_img)
            wm_label = tk.Label(parent, image=self.watermark_photo, bg="#000000", borderwidth=0)
            # Place it absolutely in the bottom right of the log panel
            wm_label.place(relx=1.0, rely=1.0, anchor="se", x=-20, y=-20)
        except:
            pass

    # ------------------ LOGIC ------------------
    def browse_general_files(self):
        paths = filedialog.askopenfilenames(title="Select Files to Attach (Direct)")
        if paths:
            self.general_attachments = list(paths)
            self.gen_attach_label.config(text=f"{len(self.general_attachments)} files", foreground=self.colors["success"])

    def browse_file(self):
        self.file_path = filedialog.askopenfilename(filetypes=[("Excel/CSV", "*.xlsx *.csv")])
        if self.file_path:
            self.file_label.config(text=os.path.basename(self.file_path), foreground=self.colors["text_main"])

    def browse_image(self):
        paths = filedialog.askopenfilenames(filetypes=[("Images", "*.png *.jpg *.jpeg *.gif")])
        if not paths: return
        self.inline_images = list(paths)
        try:
            insert_text = "\n"
            for i in range(1, len(self.inline_images) + 1):
                insert_text += f"{{Image{i}}}\n"
            self.body_text.insert("insert", insert_text)
        except: pass
        self.image_label.config(text=f"{len(self.inline_images)} images", foreground=self.colors["success"])

    def log(self, text):
        self.log_box.configure(state="normal")
        ts = datetime.now().strftime("[%H:%M:%S]")
        self.log_box.insert("end", f"{ts} > {text}\n")
        self.log_box.configure(state="disabled")
        self.log_box.yview("end")

    def set_status(self, text, color):
        self.status_dot.config(fg=color)
        self.status_text.config(text=text.upper(), fg=color)
        self.root.update()

    def update_summary(self):
        self.lbl_sent.config(text=str(self.sent_count))
        self.lbl_failed.config(text=str(self.failed_count))
        self.lbl_skipped.config(text=str(self.skipped_count))

    def _load_sent_emails(self):
        return sqlite_load_sent_emails()

    def _save_sent_emails(self):
        pass

    def find_column(self, df, candidate_set):
        for col in df.columns:
            if str(col).strip().lower() in candidate_set: return col
        return None

    def fill_placeholders(self, text, row):
        if not text: return ""
        lookup = {str(col).strip().lower(): ("" if pd.isna(val) else str(val)) for col, val in row.items()}
        name_k = next((k for k in lookup if k in NAME_COLUMN_CANDIDATES), None)
        email_k = next((k for k in lookup if k in EMAIL_COLUMN_CANDIDATES), None)

        def _replace(match):
            key = match.group(1).strip().lower()
            if key in lookup: return lookup[key]
            if key in ("name", "names") and name_k: return lookup[name_k]
            if key in ("email", "mail") and email_k: return lookup[email_k]
            return match.group(0)
        return PLACEHOLDER_REGEX.sub(_replace, text)

    def split_emails_from_cell(self, raw_value: str):
        if raw_value is None: return []
        text = str(raw_value).strip()
        if not text: return []
        return [p.strip() for p in re.split(r"[,\s;]+", text) if p.strip()]

    def start_sending(self):
        if not self.use_row_content.get():
            if not self.subject_entry.get().strip() or not self.body_text.get("1.0", "end").strip():
                messagebox.showerror("Input Error", "Subject and Body are required.")
                return
        if not self.file_path:
            messagebox.showerror("Input Error", "No source file selected.")
            return
        self.send_btn.configure(state="disabled")
        threading.Thread(target=self.send_emails, daemon=True).start()

    def send_emails(self):
        self.is_sending = True
        self.sent_count = 0
        self.failed_count = 0
        self.skipped_count = 0
        self.result_rows = []

        try:
            if self.file_path.endswith(".csv"): df = pd.read_csv(self.file_path)
            else: df = pd.read_excel(self.file_path, engine="openpyxl")
        except Exception as e:
            self.set_status("FILE ERROR", "red")
            self.send_btn.configure(state="normal")
            messagebox.showerror("Error", f"Read failed: {e}")
            return

        email_col = self.find_column(df, EMAIL_COLUMN_CANDIDATES)
        if not email_col:
            self.send_btn.configure(state="normal")
            messagebox.showerror("Error", "No 'Email' column found.")
            return

        name_col = self.find_column(df, NAME_COLUMN_CANDIDATES)
        subj_col = self.find_column(df, SUBJECT_COLUMN_CANDIDATES)
        body_col = self.find_column(df, BODY_COLUMN_CANDIDATES)

        g_subj = self.subject_entry.get().strip()
        g_body = self.body_text.get("1.0", "end").strip()

        try:
            context = ssl.create_default_context()
            server = smtplib.SMTP(SMTP_SERVER, SMTP_PORT)
            server.starttls(context=context)
            server.login(SENDER_EMAIL, SENDER_APP_PASSWORD)
        except Exception as e:
            self.set_status("CONNECTION FAILED", "red")
            self.send_btn.configure(state="normal")
            messagebox.showerror("SMTP Error", f"{e}")
            return

        self.set_status("SENDING...", self.colors["success"])
        start = self.resume_from_index if self.resuming else 0
        seen_in_file = set()

        # --- Performance cache: read files into memory once to avoid repeated disk I/O ---
        image_bytes_cache = {}
        for p in set(self.inline_images or []):
            try:
                with open(p, 'rb') as _f:
                    image_bytes_cache[p] = _f.read()
            except: 
                image_bytes_cache[p] = None

        attach_bytes_cache = {}
        for p in set(self.general_attachments or []):
            try:
                with open(p, 'rb') as _f:
                    data = _f.read()
                ctype, encoding = mimetypes.guess_type(p)
                if ctype is None or encoding is not None:
                    maintype, subtype = ('application', 'octet-stream')
                else:
                    maintype, subtype = ctype.split('/', 1)
                attach_bytes_cache[p] = (data, maintype, subtype, os.path.basename(p))
            except:
                attach_bytes_cache[p] = (None, None, None, os.path.basename(p))

        # Cache logo bytes
        logo_bytes = None
        try:
            with open('logo.png', 'rb') as lf:
                logo_bytes = lf.read()
        except: 
            logo_bytes = None

        for index, row in df.iterrows():
            if index < start: continue
            if not self.is_sending: break
            self._save_recovery_state(index)

            name = str(row.get(name_col, "")).strip() if name_col else ""
            raw_email = row.get(email_col, "")
            email_list = self.split_emails_from_cell(raw_email)

            if not email_list:
                self.skipped_count += 1
                self.update_summary()
                continue

            if not email_list:
                self.skipped_count += 1
                self.update_summary()
                # record skipped for rows without email
                for _ in []: pass
                continue
                body = b_tmpl or g_body
            else:
                subj = g_subj
                body = g_body

            subj_fin = self.fill_placeholders(subj, row)
            body_fin = self.fill_placeholders(body, row)

            inline_att = []
            def build_img(match, r_idx):
                ph = match.group(0)
                m_idx = re.search(r"\d+", ph)
                idx = int(m_idx.group(0)) if m_idx else 1
                if 1 <= idx <= len(self.inline_images):
                    cid = f"img{r_idx}_{idx}"
                    inline_att.append((cid, self.inline_images[idx-1]))
                    return f'<img src="cid:{cid}" style="max-width:100%">'
                return ""

            parts = re.split(r"(\{Image\d*\}|\{[^}]+\})", body_fin)
            final_html_parts = []
            for p in parts:
                if p.startswith("{Image"):
                    final_html_parts.append(build_img(re.match(r"\{Image\d*\}", p), index))
                else:
                    final_html_parts.append(html.escape(p).replace("\n", "<br>"))
            
            html_content = "".join(final_html_parts)
            full_html = f"""<!doctype html>
<html>
    <head>
        <meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1.0"/>
        <style>
            /* Basic reset */
            body {{ margin:0; padding:0; -webkit-text-size-adjust:100%; -ms-text-size-adjust:100%; background-color:#eef3fb; }}
            table {{ border-collapse:collapse; mso-table-lspace:0pt; mso-table-rspace:0pt; }}
            img {{ border:0; -ms-interpolation-mode:bicubic; max-width:100%; height:auto; display:block; }}
            a {{ color:inherit; text-decoration:none; }}

            /* Container helpers */
            .outer {{ width:100%; background-color:#eef3fb; padding:24px 12px; }}
            .container {{ max-width:720px; margin:0 auto; }}
            .card {{ background:#ffffff; border-radius:12px; overflow:hidden; box-shadow:0 6px 18px rgba(12,34,64,0.06); }}
            .pad {{ padding:24px 26px; }}

            /* Typography */
            .h1 {{ font-size:20px; font-weight:700; color:#134AAD; margin:0; }}
            .muted {{ color:#6b7280; font-size:12px; }}
            .body-text {{ font-size:15px; color:#0f1724; line-height:1.55; }}

            /* Responsive: stack columns and reduce padding */
            @media only screen and (max-width:600px) {{
                .container {{ width:100% !important; padding:0 8px !important; }}
                .pad {{ padding:16px !important; }}
                .two-col {{ display:block !important; width:100% !important; }}
                .logo {{ width:48px !important; }}
                .h1 {{ font-size:18px !important; }}
                .body-text {{ font-size:14px !important; line-height:1.45 !important; }}
            }}
        </style>
    </head>
    <body>
        <table role="presentation" class="outer" width="100%" cellpadding="0" cellspacing="0">
            <tr>
                <td align="center">
                    <table role="presentation" class="container" width="100%" cellpadding="0" cellspacing="0">
                        <tr><td style="padding-bottom:12px; text-align:center;">&nbsp;</td></tr>
                        <tr>
                            <td align="center">
                                <table role="presentation" width="100%" class="card" cellpadding="0" cellspacing="0">

                                    <!-- Header -->
                                    <tr>
                                        <td style="padding:18px 22px; background:linear-gradient(180deg,#ffffff 0%,#f7fbff 100%);">
                                            <table role="presentation" width="100%" cellpadding="0" cellspacing="0">
                                                <tr>
                                                    <td style="vertical-align:middle;">
                                                        <table role="presentation" cellpadding="0" cellspacing="0">
                                                            <tr>
                                                                <td style="vertical-align:middle; padding-right:12px;">
                                                                    <img src="cid:logo" alt="logo" width="56" class="logo" style="border-radius:8px;" />
                                                                </td>
                                                                <td style="vertical-align:middle; text-align:left;">
                                                                    <div class="h1">Vartistic Studio</div>
                                                                    <div class="muted">Creative Studio &amp; Design</div>
                                                                </td>
                                                            </tr>
                                                        </table>
                                                    </td>
                                                    <td style="text-align:right; vertical-align:middle; width:140px;">
                                                        <div class="muted">{datetime.now().year} • Vartistic Studio</div>
                                                    </td>
                                                </tr>
                                            </table>
                                        </td>
                                    </tr>

                                    <!-- Body -->
                                    <tr>
                                        <td class="pad">
                                            <table role="presentation" width="100%" cellpadding="0" cellspacing="0">
                                                <tr>
                                                    <td class="body-text">
                                                        {html_content}
                                                    </td>
                                                </tr>
                                            </table>
                                        </td>
                                    </tr>

                                    <!-- Divider -->
                                    <tr>
                                        <td style="padding:0 22px;"><div style="height:1px; background:#eef5ff;">&nbsp;</div></td>
                                    </tr>

                                    <!-- Footer -->
                                    <tr>
                                        <td style="padding:18px 22px 26px 22px; background:#ffffff;">
                                            <table role="presentation" width="100%" cellpadding="0" cellspacing="0">
                                                <tr>
                                                    <td valign="top" style="font-size:12px; color:#6b7280;">
                                                        <div style="font-weight:700; color:#134AAD; font-size:13px; margin-bottom:6px;">Vartistic Studio</div>
                                                        <div style="margin-bottom:6px;">Turning ideas into visual stories.</div>
                                                        <div style="color:#9aa0a6; font-size:11px;">&copy; {datetime.now().year} Vartistic Studio. All rights reserved.</div>
                                                    </td>
                                                    <td valign="top" style="width:160px; text-align:right;">
                                                        <div style="font-size:12px; color:#6b7280;">Follow us</div>
                                                        <div style="margin-top:8px; font-size:12px; color:#9aa0a6;">Instagram • Behance • Dribbble</div>
                                                    </td>
                                                </tr>
                                            </table>
                                        </td>
                                    </tr>

                                </table>
                            </td>
                        </tr>
                        <tr><td style="padding-top:12px; text-align:center; font-size:11px; color:#9aa0a6;">&nbsp;</td></tr>
                    </table>
                </td>
            </tr>
        </table>
    </body>
</html>
"""

            for e_addr in email_list:
                e_clean = e_addr.strip().lower()
                if not EMAIL_REGEX.match(e_clean) or (self.skip_duplicates_in_file.get() and e_clean in seen_in_file) or (self.respect_global_history.get() and e_clean in self.sent_emails_global):
                    self.skipped_count += 1
                    self.update_summary()
                    continue

                # MSG Construct (Support Mixed for general attachments)
                msg = MIMEMultipart("mixed")
                msg_alt = MIMEMultipart("related")
                msg.attach(msg_alt)
                
                msg["From"] = SENDER_EMAIL
                msg["To"] = e_clean
                msg["Subject"] = subj_fin
                msg_alt.attach(MIMEText(full_html, "html"))

                # 1. Inline Images
                for cid, path in inline_att:
                    try:
                        data = image_bytes_cache.get(path)
                        if data:
                            img = MIMEImage(data)
                            img.add_header("Content-ID", f"<{cid}>")
                            msg_alt.attach(img)
                    except: pass

                # Attach brand logo as inline image if available (CID used in template: 'logo')
                try:
                    if logo_bytes:
                        logo_img = MIMEImage(logo_bytes)
                        logo_img.add_header("Content-ID", "<logo>")
                        logo_img.add_header("Content-Disposition", "inline", filename="logo.png")
                        msg_alt.attach(logo_img)
                except: pass

                # 2. General File Attachments (NEW)
                for f_path in self.general_attachments:
                    try:
                        data, maintype, subtype, fname = attach_bytes_cache.get(f_path, (None, None, None, os.path.basename(f_path)))
                        if data is None:
                            # fallback to reading directly
                            with open(f_path, 'rb') as fp:
                                data = fp.read()
                            ctype, encoding = mimetypes.guess_type(f_path)
                            if ctype is None or encoding is not None:
                                maintype, subtype = ('application', 'octet-stream')
                            else:
                                maintype, subtype = ctype.split('/', 1)
                            fname = os.path.basename(f_path)

                        part = MIMEBase(maintype, subtype)
                        part.set_payload(data)
                        encoders.encode_base64(part)
                        part.add_header('Content-Disposition', 'attachment', filename=fname)
                        msg.attach(part)
                    except Exception as e:
                        self.log(f"Attach Error: {e}")

                try:
                    server.send_message(msg)
                    self.sent_count += 1
                    self.sent_emails_global.add(e_clean)
                    sqlite_save_sent_email(e_clean)
                    seen_in_file.add(e_clean)
                    self.log(f"SENT -> {e_clean}")
                    self.result_rows.append({"Name": name, "Email": e_clean, "Status": "✓", "RowIndex": index})
                except Exception as ex:
                    self.failed_count += 1
                    self.log(f"FAILED -> {e_clean} ({ex})")
                self.update_summary()

        server.quit()
        self.set_status("COMPLETED", self.colors["success"])
        self._clear_recovery_state()
        # If requested, mark the source file with send status or write a status file
        try:
            if self.mark_excel_with_status.get() and self.file_path:
                base, ext = os.path.splitext(self.file_path)
                # Build a DataFrame from result_rows
                if self.result_rows:
                    status_df = pd.DataFrame(self.result_rows)
                else:
                    status_df = pd.DataFrame(columns=["Name", "Email", "Status", "RowIndex"])

                # If original file is Excel, attempt to load and write back a new Excel with a 'Mailer_Status' column
                out_path = None
                if ext.lower() in ('.xlsx', '.xls'):
                    try:
                        orig = pd.read_excel(self.file_path, engine="openpyxl")
                        orig_cols = orig.columns.tolist()
                        # default status column
                        orig['Mailer_Status'] = ""
                        for r in self.result_rows:
                            try:
                                ri = int(r.get('RowIndex', 0))
                                # if index is within orig, set status
                                if 0 <= ri < len(orig):
                                    orig.at[ri, 'Mailer_Status'] = r.get('Status', '')
                            except: pass
                        out_path = f"{base}_status.xlsx"
                        orig.to_excel(out_path, index=False)
                    except Exception:
                        # fallback: write summary file
                        out_path = f"{base}_status.xlsx"
                        status_df.to_excel(out_path, index=False)
                else:
                    # For CSV or other, write a CSV status summary
                    out_path = f"{base}_status.csv"
                    status_df.to_csv(out_path, index=False)

                if out_path:
                    self.log(f"Status file written: {out_path}")
        except Exception as e:
            self.log(f"Status export error: {e}")
        self.send_btn.configure(state="normal")
        messagebox.showinfo("Done", "Email sequence completed.")

    # ------------------ RECOVERY ------------------
    def _check_recovery_state(self):
        try:
            data = sqlite_load_recovery_state()
            if data:
                saved_file = data.get("file_path")
                if saved_file and os.path.exists(saved_file):
                    if messagebox.askyesno("Recovery", "Resume session?"):
                        self.file_path = saved_file
                        self.resume_from_index = data.get("current_index", 0)
                        self.resuming = True
        except: pass

    def _save_recovery_state(self, current_index):
        try:
            sqlite_save_recovery_state(self.file_path, current_index)
        except: pass

    def _clear_recovery_state(self):
        try:
            sqlite_clear_recovery_state()
        except: pass
        self.resuming = False

    def open_recovery_window(self) -> None:
        win = tk.Toplevel(self.root)
        win.geometry("300x200")
        win.configure(bg=self.colors["panel_bg"])

        ttk.Button(
            win,
            text="CLEAR RECOVERY",
            command=self._clear_recovery_state
        ).pack(pady=20)

if __name__ == "__main__":
    root = tk.Tk()
    app = EmailAutomationApp(root)
    root.mainloop()
