"""
Электронные торги на RSA: одно приложение для сервера и клиентов.
Исправлена потокобезопасность Tkinter, добавлены автоматические уведомления о победе.
"""
import json
import math
import socket
import threading
from datetime import datetime
import tkinter as tk
from tkinter import ttk, messagebox

SERVER_ROLE_PASSWORD = "admin123"
MAX_BIDS = 4

AUTHORIZED_PARTICIPANT_CODES = {
    "101": "Участник 1",
    "202": "Участник 2",
    "303": "Участник 3",
    "404": "Участник 4",
}

class SimpleRandomGenerator:
    def __init__(self, seed: int = 123456789):
        if not isinstance(seed, int):
            raise ValueError("Начальное значение генератора должно быть целым числом")
        self.modulus = 2 ** 31
        self.multiplier = 1103515245
        self.increment = 12345
        self.state = seed % self.modulus
        if self.state == 0:
            self.state = 1

    def next_value(self) -> int:
        self.state = (self.multiplier * self.state + self.increment) % self.modulus
        return self.state

    def randint(self, left: int, right: int) -> int:
        if left > right:
            raise ValueError("Неверный диапазон генерации")
        return left + self.next_value() % (right - left + 1)

simple_rng = SimpleRandomGenerator(seed=123456789)

# ==========================================================
# RSA И ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ
# ==========================================================
def is_prime_trial(n: int) -> bool:
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0: return False
    limit = int(math.sqrt(n)) + 1
    for divisor in range(3, limit, 2):
        if n % divisor == 0: return False
    return True

def is_prime_fermat(n: int, rounds: int = 5) -> bool:
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0: return False
    for _ in range(rounds):
        a = simple_rng.randint(2, n - 2)
        if pow(a, n - 1, n) != 1: return False
    return True

def generate_prime(min_value: int = 1000, max_value: int = 9000) -> int:
    while True:
        candidate = simple_rng.randint(min_value, max_value)
        if candidate % 2 == 0: candidate += 1
        if candidate > max_value: candidate = min_value | 1
        if is_prime_trial(candidate) and is_prime_fermat(candidate):
            return candidate

def gcd(a: int, b: int) -> int:
    while b: a, b = b, a % b
    return abs(a)

def extended_gcd(a: int, b: int):
    if b == 0: return a, 1, 0
    g, x1, y1 = extended_gcd(b, a % b)
    x = y1
    y = x1 - (a // b) * y1
    return g, x, y

def mod_inverse(a: int, m: int) -> int:
    g, x, _ = extended_gcd(a, m)
    if g != 1: raise ValueError("Обратный элемент не существует")
    return x % m

def choose_public_exponent(phi: int) -> int:
    preferred = [65537, 257, 17, 5, 3]
    for e in preferred:
        if e < phi and gcd(e, phi) == 1: return e
    e = 3
    while e < phi:
        if gcd(e, phi) == 1: return e
        e += 2
    raise ValueError("Не удалось подобрать открытую экспоненту")

def generate_rsa_keys(min_prime: int = 1000, max_prime: int = 9000) -> dict:
    p = generate_prime(min_prime, max_prime)
    q = generate_prime(min_prime, max_prime)
    while q == p: q = generate_prime(min_prime, max_prime)
    n = p * q
    phi = (p - 1) * (q - 1)
    e = choose_public_exponent(phi)
    d = mod_inverse(e, phi)
    return {
        "p": p, "q": q, "n": n, "phi": phi, "e": e, "d": d,
        "public": {"e": e, "n": n},
        "private": {"d": d, "n": n},
    }

def rsa_encrypt_number(message_number: int, e: int, n: int) -> int:
    if message_number < 0: raise ValueError("Сообщение не может быть отрицательным")
    if message_number >= n: raise ValueError("Число ставки должно быть меньше n")
    return pow(message_number, e, n)

def rsa_decrypt_number(cipher_number: int, d: int, n: int) -> int:
    return pow(cipher_number, d, n)

def simple_hash(text: str, modulo: int) -> int:
    result = 0
    for ch in text: result = (result * 31 + ord(ch)) % modulo
    return result

def sign_text(text: str, d: int, n: int) -> int:
    h = simple_hash(text, n)
    return pow(h, d, n)

def verify_signature(text: str, signature: int, e: int, n: int) -> bool:
    expected_hash = simple_hash(text, n)
    received_hash = pow(signature, e, n)
    return expected_hash == received_hash

def make_signed_text(name: str, bid: int, timestamp: str, participant_code: str = "") -> str:
    if participant_code: return f"{participant_code}|{name}|{bid}|{timestamp}"
    return f"{name}|{bid}|{timestamp}"

def send_json_line(sock: socket.socket, data: dict):
    raw = json.dumps(data, ensure_ascii=False).encode("utf-8") + b"\n"
    sock.sendall(raw)

def read_json_line(sock: socket.socket) -> dict:
    buffer = b""
    while b"\n" not in buffer:
        chunk = sock.recv(4096)
        if not chunk: raise ConnectionError("Соединение закрыто")
        buffer += chunk
    line, _ = buffer.split(b"\n", 1)
    return json.loads(line.decode("utf-8"))

# ==========================================================
# GUI-ПРИЛОЖЕНИЕ
# ==========================================================
class AuctionApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Электронные торги RSA — сервер и клиент")
        self.root.geometry("1200x780")
        self.root.minsize(1080, 700)

        self.current_role = None
        self.server_keys = None
        self.client_keys = None
        self.server_socket = None
        self.server_running = False
        self.auction_closed = False
        self.received_bids = []
        self.used_participant_codes = set()
        self.bids_lock = threading.Lock()
        self.client_server_public_key = None
        self.final_winner = None
        self.is_auction_closed = False # Флаг для клиента

        self._setup_styles()
        self._build_gui()

    def _setup_styles(self):
        style = ttk.Style()
        bg_color = "#f5f7fa"
        frame_bg = "#ffffff"
        accent_color = "#4a90e2"
        accent_hover = "#357abd"
        text_color = "#2c3e50"

        self.root.configure(bg=bg_color)
        style.configure("Custom.TNotebook", background=bg_color, borderwidth=0)
        style.configure("Custom.TNotebook.Tab", background="#e8edf2", foreground=text_color, padding=[20, 10], font=("Segoe UI", 11))
        style.map("Custom.TNotebook.Tab", background=[("selected", accent_color), ("active", "#d4e4f7")], foreground=[("selected", "#ffffff")])
        style.configure("Custom.TLabelframe", background=frame_bg, borderwidth=1, relief="solid")
        style.configure("Custom.TLabelframe.Label", background=frame_bg, foreground=accent_color, font=("Segoe UI", 10, "bold"))
        style.configure("Custom.TLabel", background=frame_bg, foreground=text_color, font=("Segoe UI", 10))
        style.configure("Title.TLabel", background=frame_bg, foreground=accent_color, font=("Segoe UI", 18, "bold"))
        style.configure("Custom.TEntry", fieldbackground="#ffffff", foreground=text_color, borderwidth=1, relief="solid")
        style.configure("Custom.TButton", background=accent_color, foreground="#ffffff", borderwidth=0, font=("Segoe UI", 10), padding=[12, 6])
        style.map("Custom.TButton", background=[("active", accent_hover), ("disabled", "#bdc3c7")], foreground=[("disabled", "#7f8c8d")])
        style.configure("Custom.Treeview", background=frame_bg, foreground=text_color, fieldbackground=frame_bg, font=("Segoe UI", 9))
        style.configure("Custom.Treeview.Heading", background="#e8edf2", foreground=text_color, font=("Segoe UI", 9, "bold"))

    def log(self, text: str):
        """Потокобезопасный метод логирования для Tkinter"""
        def _do_log():
            now = datetime.now().strftime("%H:%M:%S")
            message = f"[{now}] {text}\n"
            self.log_text.insert(tk.END, message)
            self.log_text.see(tk.END)
        
        # Если вызов из фонового потока (сервер), переносим в главный поток UI
        if threading.current_thread() is threading.main_thread():
            _do_log()
        else:
            self.root.after(0, _do_log)

    def get_local_ip(self) -> str:
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.connect(("8.8.8.8", 80))
            ip = s.getsockname()[0]
            s.close()
            return ip
        except Exception:
            return "127.0.0.1"

    def safe_int(self, value: str, field_name: str) -> int:
        try: return int(value.strip())
        except ValueError: raise ValueError(f"Поле '{field_name}' должно быть целым числом")

    def _build_gui(self):
        self.notebook = ttk.Notebook(self.root, style="Custom.TNotebook")
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.tab_info = ttk.Frame(self.notebook)
        self.tab_primes = ttk.Frame(self.notebook)
        self.tab_keys = ttk.Frame(self.notebook)
        self.tab_server = ttk.Frame(self.notebook)
        self.tab_client = ttk.Frame(self.notebook)
        self.tab_log = ttk.Frame(self.notebook)

        self.notebook.add(self.tab_info, text=" Роль и справка ")
        self.notebook.add(self.tab_primes, text=" Простые числа ")
        self.notebook.add(self.tab_keys, text=" RSA и ЭЦП ")
        self.notebook.add(self.tab_server, text=" Сервер торгов ")
        self.notebook.add(self.tab_client, text=" Клиент торгов ")
        self.notebook.add(self.tab_log, text=" Журнал ")

        self._build_info_tab()
        self._build_primes_tab()
        self._build_keys_tab()
        self._build_server_tab()
        self._build_client_tab()
        self._build_log_tab()
        self.apply_role_restrictions()

    def apply_role_restrictions(self):
        server_state = "normal" if self.current_role == "server" else "disabled"
        client_state = "normal" if self.current_role == "client" else "disabled"
        self.notebook.tab(self.tab_server, state=server_state)
        self.notebook.tab(self.tab_client, state=client_state)

    def login_as_server(self):
        password = self.server_password_var.get().strip()
        if password != SERVER_ROLE_PASSWORD:
            messagebox.showerror("Доступ запрещен", "Неверный пароль организатора торгов")
            return
        self.current_role = "server"
        self.role_status_var.set("Текущая роль: сервер / организатор торгов")
        self.apply_role_restrictions()
        self.notebook.select(self.tab_server)

    def login_as_client(self):
        if self.server_running:
            messagebox.showerror("Сервер запущен", "Сначала остановите сервер на этой машине (или используйте другой ПК).")
            # return # Закомментировано, чтобы можно было тестировать на 1 ПК, но лучше не запускать сервер и клиент одновременно в 1 процессе без блокировок порта.
        self.current_role = "client"
        self.role_status_var.set("Текущая роль: клиент / участник торгов")
        self.apply_role_restrictions()
        self.notebook.select(self.tab_client)

    def reset_role(self):
        if self.server_running: self.stop_server()
        self.current_role = None
        self.role_status_var.set("Роль не выбрана")
        self.apply_role_restrictions()
        self.notebook.select(self.tab_info)

    def require_server_role(self) -> bool:
        if self.current_role != "server":
            messagebox.showerror("Недостаточно прав", "Войдите как сервер по паролю.")
            return False
        return True

    def require_client_role(self) -> bool:
        if self.current_role != "client":
            messagebox.showerror("Недостаточно прав", "Войдите как клиент.")
            return False
        return True

    def _build_info_tab(self):
        frame = ttk.Frame(self.tab_info, padding=20)
        frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frame, text="Электронные торги на RSA", style="Title.TLabel").pack(anchor="w", pady=(0, 16))
        
        role_box = ttk.LabelFrame(frame, text="Разграничение ролей", padding=16)
        role_box.pack(fill=tk.X, pady=(0, 16))
        ttk.Label(role_box, text="Пароль сервера:").grid(row=0, column=0, sticky="e", padx=6, pady=6)
        self.server_password_var = tk.StringVar(value="")
        ttk.Entry(role_box, textvariable=self.server_password_var, width=22, show="*").grid(row=0, column=1, padx=6, pady=6)
        ttk.Button(role_box, text="Войти как сервер", command=self.login_as_server).grid(row=0, column=2, padx=6, pady=6)
        ttk.Button(role_box, text="Войти как клиент", command=self.login_as_client).grid(row=0, column=3, padx=6, pady=6)
        ttk.Button(role_box, text="Сбросить роль", command=self.reset_role).grid(row=0, column=4, padx=6, pady=6)
        
        self.role_status_var = tk.StringVar(value="Роль не выбрана")
        ttk.Label(role_box, textvariable=self.role_status_var, font=("Segoe UI", 12, "bold")).grid(row=1, column=0, columnspan=5, sticky="w", padx=6, pady=(12, 0))

    def _build_primes_tab(self):
        frame = ttk.Frame(self.tab_primes, padding=16)
        frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frame, text="Генерация простых чисел", style="Title.TLabel").pack(anchor="w", pady=(0, 16))
        
        gen_box = ttk.LabelFrame(frame, text="Параметры", padding=14)
        gen_box.pack(fill=tk.X, pady=(0, 16))
        ttk.Label(gen_box, text="Мин:").grid(row=0, column=0, padx=6, pady=6)
        self.prime_min_var = tk.StringVar(value="1000")
        ttk.Entry(gen_box, textvariable=self.prime_min_var, width=10).grid(row=0, column=1, padx=6, pady=6)
        ttk.Label(gen_box, text="Макс:").grid(row=0, column=2, padx=6, pady=6)
        self.prime_max_var = tk.StringVar(value="9000")
        ttk.Entry(gen_box, textvariable=self.prime_max_var, width=10).grid(row=0, column=3, padx=6, pady=6)
        ttk.Button(gen_box, text="Сгенерировать", command=self.generate_prime_action).grid(row=0, column=4, padx=6, pady=6)
        
        self.prime_result_var = tk.StringVar(value="Результат: ...")
        ttk.Label(frame, textvariable=self.prime_result_var, font=("Segoe UI", 16, "bold"), foreground="#27ae60").pack(pady=20)

    def generate_prime_action(self):
        try:
            p = generate_prime(self.safe_int(self.prime_min_var.get(), "Мин"), self.safe_int(self.prime_max_var.get(), "Макс"))
            self.prime_result_var.set(f"Результат: {p}")
        except Exception as exc:
            messagebox.showerror("Ошибка", str(exc))

    def _build_keys_tab(self):
        frame = ttk.Frame(self.tab_keys, padding=16)
        frame.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frame, text="RSA и ЭЦП (Тест)", style="Title.TLabel").pack(anchor="w", pady=(0, 16))
        ttk.Button(frame, text="Сгенерировать пару ключей", command=self.generate_keys_action).pack(pady=10)
        self.keys_text = tk.Text(frame, height=8, font=("Consolas", 11))
        self.keys_text.pack(fill=tk.BOTH, expand=True, pady=10)
        
        sign_box = ttk.LabelFrame(frame, text="Тест подписи", padding=14)
        sign_box.pack(fill=tk.X, pady=10)
        ttk.Label(sign_box, text="Текст:").grid(row=0, column=0, padx=6, pady=6)
        self.sign_text_var = tk.StringVar(value="Тестовое сообщение")
        ttk.Entry(sign_box, textvariable=self.sign_text_var, width=40).grid(row=0, column=1, padx=6, pady=6)
        ttk.Button(sign_box, text="Подписать и проверить", command=self.test_signature_action).grid(row=0, column=2, padx=6, pady=6)
        self.sign_result_var = tk.StringVar(value="")
        ttk.Label(sign_box, textvariable=self.sign_result_var, font=("Segoe UI", 10, "bold")).grid(row=1, column=0, columnspan=3, pady=10)

    def generate_keys_action(self):
        keys = generate_rsa_keys()
        self.keys_text.delete("1.0", tk.END)
        self.keys_text.insert(tk.END, f"Публичный (e, n):\ne = {keys['e']}\nn = {keys['n']}\n\nПриватный (d, n):\nd = {keys['d']}\nn = {keys['n']}\n")
        self.temp_keys = keys

    def test_signature_action(self):
        if not hasattr(self, 'temp_keys') or not self.temp_keys:
            messagebox.showwarning("Внимание", "Сначала сгенерируйте ключи!")
            return
        text = self.sign_text_var.get()
        keys = self.temp_keys
        sig = sign_text(text, keys['d'], keys['n'])
        is_valid = verify_signature(text, sig, keys['e'], keys['n'])
        res = " ЭЦП ВЕРНА" if is_valid else " ЭЦП НЕВЕРНА"
        self.sign_result_var.set(f"Подпись: {sig}\nПроверка: {res}")

    def _build_server_tab(self):
        frame = ttk.Frame(self.tab_server, padding=16)
        frame.pack(fill=tk.BOTH, expand=True)
        
        controls = ttk.LabelFrame(frame, text="Организатор торгов", padding=14)
        controls.pack(fill=tk.X)
        
        ttk.Label(controls, text="IP:").grid(row=0, column=0, padx=6, pady=6)
        self.server_ip_var = tk.StringVar(value=self.get_local_ip())
        ttk.Entry(controls, textvariable=self.server_ip_var, width=15).grid(row=0, column=1, padx=6, pady=6)
        
        ttk.Label(controls, text="Порт:").grid(row=0, column=2, padx=6, pady=6)
        self.server_port_var = tk.StringVar(value="5000")
        ttk.Entry(controls, textvariable=self.server_port_var, width=8).grid(row=0, column=3, padx=6, pady=6)
        
        ttk.Button(controls, text="Сгенерировать ключи", command=self.generate_server_keys).grid(row=0, column=4, padx=6, pady=6)
        ttk.Button(controls, text="Запустить сервер", command=self.start_server).grid(row=0, column=5, padx=6, pady=6)
        ttk.Button(controls, text="Остановить", command=self.stop_server).grid(row=0, column=6, padx=6, pady=6)

        self.server_key_text = tk.Text(frame, height=5, font=("Consolas", 10))
        self.server_key_text.pack(fill=tk.X, pady=10)

        table_box = ttk.LabelFrame(frame, text="Ставки", padding=10)
        table_box.pack(fill=tk.BOTH, expand=True, pady=10)
        
        columns = ("code", "name", "time", "encrypted", "bid", "signature", "status")
        self.bids_tree = ttk.Treeview(table_box, columns=columns, show="headings", height=10)
        for col in columns: self.bids_tree.heading(col, text=col.capitalize())
        self.bids_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        res_box = ttk.Frame(frame)
        res_box.pack(fill=tk.X, pady=10)
        ttk.Button(res_box, text="Завершить торги", command=self.close_auction).pack(side=tk.LEFT, padx=6)
        ttk.Button(res_box, text="Определить победителя", command=self.determine_winner).pack(side=tk.LEFT, padx=6)
        
        self.winner_var = tk.StringVar(value="Победитель не определен")
        ttk.Label(res_box, textvariable=self.winner_var, font=("Segoe UI", 12, "bold"), foreground="#27ae60").pack(side=tk.LEFT, padx=20)

    def _build_client_tab(self):
        frame = ttk.Frame(self.tab_client, padding=16)
        frame.pack(fill=tk.BOTH, expand=True)
        
        connect_box = ttk.LabelFrame(frame, text="Подключение", padding=14)
        connect_box.pack(fill=tk.X)
        ttk.Label(connect_box, text="IP сервера:").grid(row=0, column=0, padx=6, pady=6)
        self.client_server_ip_var = tk.StringVar(value="127.0.0.1")
        ttk.Entry(connect_box, textvariable=self.client_server_ip_var, width=15).grid(row=0, column=1, padx=6, pady=6)
        ttk.Label(connect_box, text="Порт:").grid(row=0, column=2, padx=6, pady=6)
        self.client_server_port_var = tk.StringVar(value="5000")
        ttk.Entry(connect_box, textvariable=self.client_server_port_var, width=8).grid(row=0, column=3, padx=6, pady=6)
        ttk.Button(connect_box, text="Получить ключ сервера", command=self.client_get_server_key).grid(row=0, column=4, padx=6, pady=6)

        bid_box = ttk.LabelFrame(frame, text="Отправка ставки", padding=14)
        bid_box.pack(fill=tk.X, pady=12)
        
        ttk.Label(bid_box, text="Код:").grid(row=0, column=0, padx=6, pady=6)
        self.client_code_var = tk.StringVar(value="101")
        ttk.Entry(bid_box, textvariable=self.client_code_var, width=10).grid(row=0, column=1, padx=6, pady=6)
        
        ttk.Label(bid_box, text="ФИО:").grid(row=0, column=2, padx=6, pady=6)
        self.client_name_var = tk.StringVar(value="Иванов Иван")
        ttk.Entry(bid_box, textvariable=self.client_name_var, width=25).grid(row=0, column=3, padx=6, pady=6)
        
        ttk.Label(bid_box, text="Ставка:").grid(row=0, column=4, padx=6, pady=6)
        self.client_bid_var = tk.StringVar(value="150")
        ttk.Entry(bid_box, textvariable=self.client_bid_var, width=10).grid(row=0, column=5, padx=6, pady=6)
        
        ttk.Button(bid_box, text="Подготовить и отправить", command=self.send_client_bid).grid(row=1, column=0, columnspan=6, pady=10)

        ttk.Button(bid_box, text="Проверить итоги торгов (Кто победил?)", command=self.check_auction_results, style="Custom.TButton").grid(row=2, column=0, columnspan=6, pady=10)

        self.client_status_text = tk.Text(frame, height=10, font=("Consolas", 10))
        self.client_status_text.pack(fill=tk.BOTH, expand=True)

    def _build_log_tab(self):
        frame = ttk.Frame(self.tab_log, padding=16)
        frame.pack(fill=tk.BOTH, expand=True)
        self.log_text = tk.Text(frame, font=("Consolas", 10))
        self.log_text.pack(fill=tk.BOTH, expand=True)
        self.log("Приложение запущено")

    # --- Логика Сервера ---
    def generate_server_keys(self):
        if not self.require_server_role(): return
        self.server_keys = generate_rsa_keys()
        self.server_key_text.delete("1.0", tk.END)
        self.server_key_text.insert(tk.END, f"e={self.server_keys['e']}\nn={self.server_keys['n']}\nd={self.server_keys['d']}")

    def start_server(self):
        if not self.require_server_role(): return
        if self.server_keys is None: self.generate_server_keys()
        host = self.server_ip_var.get().strip()
        port = self.safe_int(self.server_port_var.get(), "Порт")
        try:
            self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.server_socket.bind((host, port))
            self.server_socket.listen(10)
            self.server_socket.settimeout(1.0)
            self.server_running = True
            threading.Thread(target=self.server_accept_loop, daemon=True).start()
            self.log(f"Сервер запущен на {host}:{port}")
        except Exception as e:
            messagebox.showerror("Ошибка запуска", str(e))

    def stop_server(self):
        self.server_running = False
        if self.server_socket: 
            try: self.server_socket.close()
            except: pass
        self.log("Сервер остановлен")

    def server_accept_loop(self):
        while self.server_running:
            try:
                client_socket, address = self.server_socket.accept()
                threading.Thread(target=self.handle_client_connection, args=(client_socket, address), daemon=True).start()
            except socket.timeout: continue
            except OSError: break

    def handle_client_connection(self, client_socket: socket.socket, address):
        try:
            greeting_data = {
                "type": "SERVER_PUBLIC_KEY",
                "server_public_key": self.server_keys["public"],
                "auction_closed": self.auction_closed,
            }
            # Передаем информацию о победителе, если торги закрыты
            if self.auction_closed and self.final_winner:
                greeting_data["winner_info"] = {
                    "name": self.final_winner["name"],
                    "bid": self.final_winner["bid"],
                    "code": self.final_winner.get("participant_code", "")
                }
            
            send_json_line(client_socket, greeting_data)
            
            try:
                request = read_json_line(client_socket)
            except ConnectionError:
                return

            if request.get("type") == "GET_RESULT":
                client_code = str(request.get("participant_code", "")).strip()
                you_won = (self.final_winner and self.final_winner.get("participant_code") == client_code)
                send_json_line(client_socket, {
                    "type": "RESULT",
                    "status": "finished" if self.final_winner else "waiting",
                    "winner_name": self.final_winner.get("name") if self.final_winner else "",
                    "winner_bid": self.final_winner.get("bid") if self.final_winner else 0,
                    "you_won": bool(you_won)
                })
                return

            if request.get("type") != "BID": return
            if self.auction_closed:
                send_json_line(client_socket, {"type": "ERROR", "message": "Торги уже завершены"})
                return

            result = self.process_bid(request)
            if result["accepted"]:
                send_json_line(client_socket, {"type": "OK", "message": "Ставка принята", "bid": result["bid"]})
            else:
                send_json_line(client_socket, {"type": "ERROR", "message": result["error"]})
        except Exception as exc:
            self.log(f"Ошибка клиента {address}: {exc}")
        finally:
            try: client_socket.close()
            except: pass

    def process_bid(self, data: dict) -> dict:
        try:
            participant_code = str(data.get("participant_code", "")).strip()
            name = str(data.get("name", "")).strip()
            timestamp = str(data.get("timestamp", "")).strip()
            encrypted_bid = int(data.get("encrypted_bid"))
            signature = int(data.get("signature"))
            client_public_key = data.get("client_public_key", {})
            
            if participant_code not in AUTHORIZED_PARTICIPANT_CODES:
                return {"accepted": False, "error": "Код не найден в реестре"}
                
            with self.bids_lock:
                if len(self.received_bids) >= MAX_BIDS: return {"accepted": False, "error": "Лимит ставок"}
                if participant_code in self.used_participant_codes: return {"accepted": False, "error": "Код уже использован"}

            bid = rsa_decrypt_number(encrypted_bid, self.server_keys["private"]["d"], self.server_keys["private"]["n"])
            signed_text = make_signed_text(name, bid, timestamp, participant_code)
            signature_ok = verify_signature(signed_text, signature, int(client_public_key["e"]), int(client_public_key["n"]))
            
            if not signature_ok: return {"accepted": False, "error": "ЭЦП неверна"}

            record = {"participant_code": participant_code, "name": name, "timestamp": timestamp, 
                      "encrypted_bid": encrypted_bid, "bid": bid, "signature": signature, 
                      "signature_status": "Верна" if signature_ok else "Неверна"}
            
            with self.bids_lock:
                self.received_bids.append(record)
                self.used_participant_codes.add(participant_code)
                if len(self.received_bids) >= MAX_BIDS: 
                    self.auction_closed = True
                    self.log(f"Достигнут лимит ставок ({MAX_BIDS}). Торги автоматически закрыты.")
                
            self.root.after(0, self.add_bid_to_table, record)
            return {"accepted": True, "bid": bid}
        except Exception as exc:
            return {"accepted": False, "error": str(exc)}

    def add_bid_to_table(self, record: dict):
        self.bids_tree.insert("", tk.END, values=(record["participant_code"], record["name"], record["timestamp"], 
                                                  record["encrypted_bid"], record["bid"], record["signature"], record["signature_status"]))

    def close_auction(self):
        self.auction_closed = True
        self.log("Торги принудительно завершены организатором.")

    def determine_winner(self):
        with self.bids_lock:
            valid_bids = [item for item in self.received_bids if item["signature_status"] == "Верна"]
        if not valid_bids:
            self.winner_var.set("Нет корректных ставок")
            return
        winner = max(valid_bids, key=lambda item: item["bid"])
        self.final_winner = winner
        self.auction_closed = True # Фиксируем закрытие после определения
        self.winner_var.set(f"Победитель: {winner['name']} (Ставка: {winner['bid']})")
        self.log(f"Определен победитель: {winner['name']}")
        messagebox.showinfo("Победитель", f"Победил: {winner['name']}\nСтавка: {winner['bid']}")

    # --- Логика Клиента ---
    def client_get_server_key(self):
        if not self.require_client_role(): return
        try:
            host = self.client_server_ip_var.get().strip()
            port = self.safe_int(self.client_server_port_var.get(), "Порт")
            with socket.create_connection((host, port), timeout=5) as sock:
                response = read_json_line(sock)
            
            self.client_server_public_key = response["server_public_key"]
            self.is_auction_closed = response.get("auction_closed", False)
            
            # АВТОМАТИЧЕСКАЯ ПРОВЕРКА ПОБЕДЫ ПРИ ПОДКЛЮЧЕНИИ
            if self.is_auction_closed and response.get("winner_info"):
                win_info = response["winner_info"]
                my_code = self.client_code_var.get().strip()
                
                if not my_code:
                    messagebox.showinfo("Торги завершены", f"Аукцион уже завершен!\nПобедитель: {win_info['name']}\nСтавка: {win_info['bid']}\n(Введите ваш код, чтобы проверить, победили ли вы)")
                elif my_code == win_info.get("code"):
                    messagebox.showinfo(" ПОБЕДА!", f"Аукцион завершен!\nПоздравляем, вы победили!\nВаша ставка: {win_info['bid']}")
                else:
                    messagebox.showinfo("Торги завершены", f"Аукцион уже завершен!\nПобедитель: {win_info['name']} (Код: {win_info.get('code')})\nСтавка: {win_info['bid']}\nК сожалению, вы не победили.")
                
        except Exception as exc:
            messagebox.showerror("Ошибка подключения", str(exc))

    def send_client_bid(self):
        if not self.require_client_role(): return
        try:
            if self.client_keys is None: self.client_keys = generate_rsa_keys()
            if self.client_server_public_key is None: self.client_get_server_key()
            
            # Блокировка отправки, если мы уже знаем, что торги закрыты
            if getattr(self, 'is_auction_closed', False):
                messagebox.showinfo("Торги завершены", "Вы не можете сделать ставку, торги уже завершены.")
                return
            
            participant_code = self.client_code_var.get().strip()
            name = self.client_name_var.get().strip()
            bid = self.safe_int(self.client_bid_var.get(), "Ставка")
            timestamp = datetime.now().strftime("%d.%m.%Y %H:%M:%S")
            
            signed_text = make_signed_text(name, bid, timestamp, participant_code)
            signature = sign_text(signed_text, self.client_keys["private"]["d"], self.client_keys["private"]["n"])
            encrypted_bid = rsa_encrypt_number(bid, int(self.client_server_public_key["e"]), int(self.client_server_public_key["n"]))
            
            data = {
                "type": "BID", "participant_code": participant_code, "name": name, "timestamp": timestamp,
                "encrypted_bid": encrypted_bid, "signature": signature, "client_public_key": self.client_keys["public"]
            }
            
            with socket.create_connection((self.client_server_ip_var.get().strip(), self.safe_int(self.client_server_port_var.get(), "Порт")), timeout=5) as sock:
                read_json_line(sock) # Читаем приветствие
                send_json_line(sock, data)
                response = read_json_line(sock)
                
            if response.get("type") == "OK":
                messagebox.showinfo("Успех", "Ставка принята сервером!")
            else:
                msg = response.get("message", "Отклонено")
                if "завершены" in msg.lower():
                    self.is_auction_closed = True # Обновляем локальный флаг
                messagebox.showerror("Ошибка", msg)
        except Exception as exc:
            messagebox.showerror("Ошибка", str(exc))

    def check_auction_results(self):
        """Клиент запрашивает у сервера итоги торгов и проверяет, победил ли он."""
        if not self.require_client_role(): return
        try:
            host = self.client_server_ip_var.get().strip()
            port = self.safe_int(self.client_server_port_var.get(), "Порт")
            participant_code = self.client_code_var.get().strip()
            
            if not participant_code:
                messagebox.showwarning("Внимание", "Введите ваш код участника")
                return

            data = {"type": "GET_RESULT", "participant_code": participant_code}
            
            with socket.create_connection((host, port), timeout=5) as sock:
                read_json_line(sock) # Читаем приветствие
                send_json_line(sock, data)
                response = read_json_line(sock)

            if response.get("type") == "RESULT":
                if response.get("status") == "waiting":
                    messagebox.showinfo("Результаты", "Торги еще не завершены или победитель не определен.")
                else:
                    winner_name = response.get("winner_name")
                    winner_bid = response.get("winner_bid")
                    you_won = response.get("you_won")
                    
                    if you_won:
                        messagebox.showinfo(" ПОБЕДА!", f"Поздравляем!\nВаша ставка победила!\nИтоговая ставка: {winner_bid}")
                    else:
                        messagebox.showinfo("Результаты", f"Победил другой участник: {winner_name}.\nСтавка победителя: {winner_bid}")
        except Exception as exc:
            messagebox.showerror("Ошибка", str(exc))

def main():
    root = tk.Tk()
    app = AuctionApp(root)
    def on_close():
        app.stop_server()
        root.destroy()
    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()

if __name__ == "__main__":
    main()