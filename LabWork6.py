# -*- coding: utf-8 -*-
"""
Практическая работа №6.
Инфраструктура открытых ключей и удостоверяющие центры.

Сценарий работы:
1. Получатель: "Сформировать ключи" -> ключи появляются только у него.
2. Получатель: "Послать" -> открытый ключ и сертификат уходят отправителю.
3. Отправитель: "Получить" -> ключ получателя заносится в блок "Для сообщения".
4. Отправитель: вводит ЛЮБОЕ ЧИСЛО в выделенное желтое поле "Ввод числа",
   нажимает "Закодировать и подписаться", затем "Послать".
5. Получатель: "Проверить" -> расшифровывает число, проверяет подпись
   и выводит "ПОДПИСЬ ВЕРНА" и расшифрованное число.

Зависимости: только стандартная библиотека Python (tkinter).
"""

import json
import math
import secrets
import hashlib
from collections import deque
from datetime import datetime, timedelta, timezone

import tkinter as tk
from tkinter import messagebox

KEY_BITS = 64  # учебный размер ключа: e и N отображаются как целые числа

# Цвет выделенного поля ввода числа
INPUT_BG = "#fff8c4"
FRAME_BG = "#fffbe6"


# ------------------------------------------------------------
# Учебный RSA: ключи как числа (e, d, N)
# ------------------------------------------------------------

def _is_prime(n):
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n % p == 0:
            return n == p
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in small:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def _gen_prime(bits):
    while True:
        n = secrets.randbits(bits) | (1 << (bits - 1)) | 1
        if _is_prime(n):
            return n


def generate_rsa(bits=KEY_BITS):
    """Формирование пары ключей: (e, d, N)."""
    while True:
        p = _gen_prime(bits // 2)
        q = _gen_prime(bits // 2)
        if p == q:
            continue
        n = p * q
        phi = (p - 1) * (q - 1)
        e = secrets.randbelow(phi - 3) + 3
        if e % 2 == 0:
            e += 1
        if math.gcd(e, phi) != 1:
            continue
        d = pow(e, -1, phi)
        return e, d, n


def canonical_json(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def hash_bytes(data: bytes, n: int) -> int:
    return int(hashlib.sha256(data).hexdigest(), 16) % n


# ------------------------------------------------------------
# Удостоверяющий центр
# ------------------------------------------------------------

class CertificationAuthority:
    def __init__(self, name="УЦ"):
        self.name = name
        self.e, self.d, self.n = generate_rsa()
        self.directory = {}  # общедоступное хранилище открытых ключей

    def register(self, subject, e, n):
        now = datetime.now(timezone.utc)
        payload = {
            "subject": subject,
            "e": e,
            "N": n,
            "ca_name": self.name,
            "ca_e": self.e,
            "ca_N": self.n,
            "serial": secrets.token_hex(6),
            "not_before": now.isoformat(),
            "not_after": (now + timedelta(days=365)).isoformat(),
        }
        sig = pow(hash_bytes(canonical_json(payload).encode("utf-8"), self.n),
                  self.d, self.n)
        cert = dict(payload)
        cert["sig"] = sig
        self.directory[subject] = (e, n)
        return cert


def verify_certificate(cert, ca_e, ca_n):
    if not isinstance(cert, dict):
        return False, "Сертификат имеет неверный формат"
    if cert.get("ca_e") != ca_e or cert.get("ca_N") != ca_n:
        return False, "Сертификат выдан другим удостоверяющим центром"
    now = datetime.now(timezone.utc)
    try:
        if not (datetime.fromisoformat(cert["not_before"]) <= now
                <= datetime.fromisoformat(cert["not_after"])):
            return False, "Срок действия сертификата недействителен"
    except Exception:
        return False, "Некорректные даты сертификата"
    payload = {k: v for k, v in cert.items() if k != "sig"}
    h = hash_bytes(canonical_json(payload).encode("utf-8"), ca_n)
    if pow(cert.get("sig", 0), ca_e, ca_n) == h:
        return True, "Сертификат подтвержден УЦ"
    return False, "Подпись сертификата недействительна"


# ------------------------------------------------------------
# Окно клиента (вид зависит от роли)
# ------------------------------------------------------------

class NodeWindow:
    def __init__(self, master, app, role, counterpart):
        self.master = master
        self.app = app
        self.role = role
        self.counterpart = counterpart

        self.keys = None          # (e, d, N) - свои ключи
        self.certificate = None
        self.trusted_ca = None    # (ca_e, ca_N)
        self.peer_key = None      # (e, N) собеседника
        self.out_package = None

        master.title(role)
        master.geometry("640x420")

        # -------------------- Меню --------------------
        menubar = tk.Menu(master)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Переслать сертификат",
                              command=self.send_certificate)
        file_menu.add_separator()
        file_menu.add_command(label="Очистить окно сообщения",
                              command=self.clear_text)
        file_menu.add_separator()
        file_menu.add_command(label="Выход", command=self.app.quit_all)
        menubar.add_cascade(label="Файл", menu=file_menu)
        if role == "Отправитель":
            menubar.add_command(label="О программе...", command=self.about)
        master.config(menu=menubar)

        bold = ("TkDefaultFont", 10, "bold")
        body = tk.Frame(master, padx=10, pady=6)
        body.pack(fill=tk.BOTH, expand=True)

        # -------------------- Заголовки блоков --------------------
        if role == "Отправитель":
            left_title, right_title = "Для подписи", "Для сообщения"
        else:
            left_title, right_title = "Для сообщения", "Для подписи"

        tk.Label(body, text=left_title, font=bold, anchor="w").grid(
            row=0, column=0, columnspan=2, sticky="w")
        tk.Label(body, text=right_title, font=bold, anchor="w").grid(
            row=0, column=2, columnspan=2, sticky="w", padx=(24, 0))

        # -------------------- Свои ключи (слева) --------------------
        self.own_e_label = tk.Label(body, text="Открытый ключ", anchor="w")
        self.own_e_label.grid(row=1, column=0, columnspan=2, sticky="w", pady=(4, 0))
        self.own_n_label = tk.Label(body, text="N", anchor="w")
        self.own_n_label.grid(row=2, column=0, columnspan=2, sticky="w", pady=(4, 0))

        # -------------------- Ключи собеседника (справа) --------------------
        self.peer_e_label = tk.Label(body, text="Открытый ключ", anchor="w")
        self.peer_e_label.grid(row=1, column=2, columnspan=2, sticky="w",
                               padx=(24, 0), pady=(4, 0))
        self.peer_n_label = tk.Label(body, text="N", anchor="w")
        self.peer_n_label.grid(row=2, column=2, columnspan=2, sticky="w",
                               padx=(24, 0), pady=(4, 0))

        # -------------------- Кнопки --------------------
        if role == "Отправитель":
            tk.Button(body, text="Послать", width=16,
                      command=self.send_message).grid(
                row=3, column=3, sticky="e", pady=(8, 0))
            tk.Label(body, text="Окно сообщения", anchor="w").grid(
                row=4, column=0, sticky="w", pady=(8, 0))
            tk.Button(body, text="Сформировать ключи",
                      command=self.generate_keys).grid(
                row=4, column=1, padx=(8, 0), pady=(8, 0))
            tk.Button(body, text="Закодировать и подписаться",
                      command=self.encode_and_sign).grid(
                row=4, column=2, padx=(8, 0), pady=(8, 0))
            tk.Button(body, text="Получить", width=16,
                      command=self.receive).grid(
                row=4, column=3, sticky="e", pady=(8, 0))

            # ---------- ВЫДЕЛЕННАЯ ОБЛАСТЬ ВВОДА ЧИСЛА ----------
            input_frame = tk.LabelFrame(
                body,
                text=" Ввод ",
                bg=FRAME_BG,
                padx=6,
                pady=4,
            )
            input_frame.grid(row=5, column=0, columnspan=4,
                             sticky="ew", pady=(8, 0))

            tk.Label(input_frame, text="Сообщение:", bg=FRAME_BG,
                     font=bold).grid(row=0, column=0, sticky="w")

            self.num_entry = tk.Entry(
                input_frame,
                bg=INPUT_BG,
                relief=tk.SOLID,
                bd=1,
                font=("TkDefaultFont", 11),
            )
            self.num_entry.grid(row=0, column=1, sticky="we", padx=(6, 6))

            input_frame.columnconfigure(1, weight=1)
            text_row = 6
        else:
            tk.Label(body, text="Окно сообщения", anchor="w").grid(
                row=3, column=0, sticky="w", pady=(8, 0))
            tk.Button(body, text="Сформировать ключи",
                      command=self.generate_keys).grid(
                row=3, column=1, padx=(8, 0), pady=(8, 0))
            self.send_btn = tk.Button(body, text="Послать", width=14,
                                      state=tk.DISABLED,
                                      command=self.send_certificate)
            self.send_btn.grid(row=3, column=2, sticky="e", padx=(30, 0), pady=(8, 0))
            self.verify_btn = tk.Button(body, text="Проверить", width=14,
                                        state=tk.DISABLED,
                                        command=self.verify_received)
            self.verify_btn.grid(row=3, column=3, sticky="e", pady=(8, 0))
            text_row = 4

        # -------------------- Окно сообщения (только вывод) --------------------
        self.text = tk.Text(body, height=9, wrap="word", state=tk.DISABLED)
        sb = tk.Scrollbar(body, command=self.text.yview)
        self.text.configure(yscrollcommand=sb.set)
        self.text.grid(row=text_row, column=0, columnspan=3,
                       sticky="nsew", pady=(8, 0))
        sb.grid(row=text_row, column=3, sticky="ns", pady=(8, 0))

        body.rowconfigure(text_row, weight=1)
        body.columnconfigure(1, weight=1)
        body.columnconfigure(3, weight=1)

        self.note(f"УЦ '{self.app.ca.name}' создан. Нажмите 'Сформировать ключи'.")
        if role == "Отправитель":
            self.note("Число для отправки вводите в желтое поле 'Ввод числа'.")
            self.num_entry.focus_set()

        if role == "Получатель":
            master.protocol("WM_DELETE_WINDOW", self._close_self)

    # -------------------- Служебное --------------------
    def _close_self(self):
        self.app.windows.pop(self.role, None)
        self.master.destroy()

    def note(self, msg):
        """Дописать строку в окно сообщения (окно только для вывода)."""
        self.text.configure(state=tk.NORMAL)
        self.text.insert(tk.END, msg + "\n")
        self.text.see(tk.END)
        self.text.configure(state=tk.DISABLED)

    def show_lines(self, lines):
        """Очистить окно сообщения и вывести список строк."""
        self.text.configure(state=tk.NORMAL)
        self.text.delete("1.0", tk.END)
        for ln in lines:
            self.text.insert(tk.END, ln + "\n")
        self.text.configure(state=tk.DISABLED)

    def clear_text(self):
        self.text.configure(state=tk.NORMAL)
        self.text.delete("1.0", tk.END)
        self.text.configure(state=tk.DISABLED)

    def about(self):
        messagebox.showinfo(
            "О программе...",
            "Практическая работа №6\n"
            "Инфраструктура открытых ключей и удостоверяющие центры.\n\n"
            "Отправитель кодирует и подписывает число,\n"
            "получатель проверяет подпись и расшифровывает число.",
        )

    def set_peer_key(self, e, n):
        self.peer_key = (e, n)
        self.peer_e_label.config(text=f"Открытый ключ:  {e}")
        self.peer_n_label.config(text=f"N:  {n}")

    def _refresh_buttons(self):
        """Управление доступностью кнопок в окне получателя."""
        if self.role != "Получатель":
            return
        if self.keys:
            self.send_btn.config(state=tk.NORMAL)
            if self.app.has_message_pending(self.role):
                self.verify_btn.config(state=tk.NORMAL)

    # -------------------- Общие действия --------------------
    def generate_keys(self):
        e, d, n = generate_rsa()
        self.keys = (e, d, n)
        self.own_e_label.config(text=f"Открытый ключ:  {e}")
        self.own_n_label.config(text=f"N:  {n}")

        # Регистрация в УЦ и получение сертификата.
        # Ключи никуда не передаются автоматически.
        self.certificate = self.app.ca.register(self.role, e, n)
        self.trusted_ca = (self.certificate["ca_e"], self.certificate["ca_N"])

        self.note(f"[{self.role}] Сформированы ключи: e={e}, N={n}")
        self.note(f"[{self.role}] Зарегистрирован в УЦ, получен сертификат.")
        if self.role == "Получатель":
            self.note("Ключи будут переданы отправителю только "
                      "после нажатия кнопки 'Послать'.")
        self._refresh_buttons()

    def send_certificate(self):
        """Переслать свой открытый ключ и сертификат собеседнику."""
        if not self.certificate:
            messagebox.showwarning("Сертификат",
                                   "Сначала нажмите 'Сформировать ключи'.")
            return
        self.app.send(self.counterpart, {
            "type": "cert",
            "from": self.role,
            "to": self.counterpart,
            "cert": self.certificate,
        })
        self.note(f"[{self.role}] Открытый ключ и сертификат переданы "
                  f"клиенту {self.counterpart}.")

    # -------------------- Действия отправителя --------------------
    def encode_and_sign(self):
        """Взять число из выделенного поля ввода, подписать и зашифровать."""
        if not self.keys:
            messagebox.showwarning("Ключи", "Сначала нажмите 'Сформировать ключи'.")
            return
        if not self.peer_key:
            messagebox.showwarning(
                "Ключ получателя",
                "В блоке 'Для сообщения' нет открытого ключа получателя.\n"
                "Дождитесь, пока получатель нажмет 'Послать', "
                "и нажмите 'Получить'.")
            return

        raw = self.num_entry.get().strip()
        if not raw:
            messagebox.showwarning(
                "Число",
                "Введите число в выделенное желтое поле 'Ввод числа'.")
            self.num_entry.focus_set()
            return
        try:
            m = int(raw)
        except ValueError:
            messagebox.showwarning(
                "Число",
                "В поле 'Ввод числа' должно быть целое число, например: 12345")
            self.num_entry.focus_set()
            return
        if m < 0:
            messagebox.showwarning("Число", "Число должно быть неотрицательным.")
            self.num_entry.focus_set()
            return

        e, d, n = self.keys        # свои ключи (для подписи)
        pe, pn = self.peer_key     # ключ получателя (для шифрования)

        limit = min(n, pn)
        if m >= limit:
            messagebox.showwarning(
                "Число",
                f"Число слишком большое.\nДопустимый диапазон: 0 .. {limit - 1}")
            return

        # Подпись своим закрытым ключом
        s = pow(m, d, n)
        # Шифрование открытым ключом получателя
        c = pow(m, pe, pn)

        self.out_package = {"C": c, "S": s}

        self.show_lines([
            "[Число закодировано и подписано]",
            f"Исходное число M: {m}",
            f"Подпись S (своим закрытым ключом): {s}",
            f"Закодированное число C (ключом получателя): {c}",
            "",
            "Нажмите 'Послать' для отправки получателю.",
        ])

    def send_message(self):
        if self.out_package is None:
            messagebox.showwarning(
                "Отправка", "Сначала нажмите 'Закодировать и подписаться'.")
            return
        pkg = dict(self.out_package)
        pkg.update({
            "type": "message",
            "from": self.role,
            "to": self.counterpart,
            "cert": self.certificate,
        })
        self.app.send(self.counterpart, pkg)
        self.note(f"[{self.role}] Сообщение отправлено клиенту {self.counterpart}.")

    def receive(self):
        """Получить (у отправителя): ключи и сертификат получателя."""
        pkg = self.app.recv(self.role)
        if pkg is None:
            self.note(f"[{self.role}] Канал пуст: сообщений нет.")
            return
        if pkg.get("to") != self.role:
            self.app.putback(self.role, pkg)
            self.note("Ошибка: пакет предназначен другому адресату.")
            return
        if not self.trusted_ca:
            self.app.putback(self.role, pkg)
            messagebox.showwarning("Ключи", "Сначала нажмите 'Сформировать ключи'.")
            return

        if pkg.get("type") == "cert":
            cert = pkg.get("cert", {})
            ok, reason = verify_certificate(cert, *self.trusted_ca)
            self.note(f"[{self.role}] Проверка сертификата от "
                      f"'{pkg.get('from')}': {reason}")
            if ok:
                self.set_peer_key(cert["e"], cert["N"])
                self.note(f"[{self.role}] Открытый ключ получен и занесен "
                          f"в блок 'Для сообщения'.")
            return

        self.app.putback(self.role, pkg)
        self.note("Получен неожиданный тип пакета.")

    # -------------------- Действия получателя --------------------
    def verify_received(self):
        """Проверить подпись и расшифровать число."""
        pkg = self.app.recv(self.role)
        if pkg is None:
            self.note(f"[{self.role}] Канал пуст.")
            self._refresh_buttons()
            return
        if not self.keys:
            self.app.putback(self.role, pkg)
            messagebox.showwarning("Ключи", "Сначала нажмите 'Сформировать ключи'.")
            return
        if pkg.get("type") != "message":
            self.app.putback(self.role, pkg)
            self.note("Ожидалось подписанное сообщение.")
            return

        cert = pkg.get("cert", {})
        ok, reason = verify_certificate(cert, *self.trusted_ca)
        if not ok:
            self.note(f"[{self.role}] Проверка сертификата от "
                      f"'{pkg.get('from')}': {reason}")
            self._refresh_buttons()
            return

        # Открытый ключ отправителя из сертификата -> блок "Для подписи"
        self.set_peer_key(cert["e"], cert["N"])
        e_s, n_s = cert["e"], cert["N"]

        c = pkg.get("C")
        s = pkg.get("S")
        if c is None or s is None:
            self.note("Ошибка: поврежден формат сообщения.")
            return

        # Расшифрование своим закрытым ключом
        e, d, n = self.keys
        m = pow(c, d, n)

        lines = [
            "--- Результат проверки ---",
            f"Сертификат отправителя: {reason}",
            f"Получено закодированное число C: {c}",
            f"Получена подпись S: {s}",
            "",
        ]
        # Проверка подписи открытым ключом отправителя
        if pow(s, e_s, n_s) == m:
            lines += ["ПОДПИСЬ ВЕРНА", f"Расшифрованное число: {m}"]
        else:
            lines += ["ПОДПИСЬ НЕВЕРНА"]

        self.show_lines(lines)
        self._refresh_buttons()


# ------------------------------------------------------------
# Приложение: УЦ + два окна + канал связи
# ------------------------------------------------------------

class App:
    def __init__(self):
        self.ca = CertificationAuthority("УЦ")
        self.channels = {}
        self.windows = {}

        self.root = tk.Tk()
        self.windows["Отправитель"] = NodeWindow(
            self.root, self, "Отправитель", "Получатель")

        self.root2 = tk.Toplevel(self.root)
        self.root2.geometry("640x420+70+70")
        self.windows["Получатель"] = NodeWindow(
            self.root2, self, "Получатель", "Отправитель")

        self.root.protocol("WM_DELETE_WINDOW", self.quit_all)

    def send(self, role, pkg):
        self.channels.setdefault(role, deque()).append(pkg)
        win = self.windows.get(role)
        if win:
            win._refresh_buttons()

    def recv(self, role):
        q = self.channels.get(role)
        return q.popleft() if q else None

    def putback(self, role, pkg):
        self.channels.setdefault(role, deque()).appendleft(pkg)

    def has_message_pending(self, role):
        return any(p.get("type") == "message"
                   for p in self.channels.get(role, ()))

    def quit_all(self):
        try:
            self.root2.destroy()
        except Exception:
            pass
        self.root.destroy()

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    App().run()