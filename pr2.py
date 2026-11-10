import tkinter as tk
from tkinter import messagebox, simpledialog
import random
import math

class PrimeGeneratorApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Генерация простых чисел, используемых в криптоалгоритмах с открытым ключом")
        self.root.geometry("700x500")
        
        # Создаем меню
        self.create_menu()
        
        # Создаем текстовое поле для вывода результатов
        self.text_area = tk.Text(root, wrap=tk.WORD, font=("Courier", 10))
        self.text_area.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Переменные для хранения результатов
        self.prime_numbers = []
        self.last_checked_number = None
        self.is_prime_result = None
        self.divisor_found = None
        self.fermat_bases = [3, 5]
        
    def create_menu(self):
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # Меню "Генерация простого P"
        gen_menu = tk.Menu(menubar, tearoff=0)
        gen_menu.add_command(label="Сгенерировать простое число", command=self.generate_prime)
        menubar.add_cascade(label="Генерация простого P", menu=gen_menu)
        
        # Меню "Поиск в интервале"
        search_menu = tk.Menu(menubar, tearoff=0)
        search_menu.add_command(label="Найти простые в интервале", command=self.search_in_interval)
        menubar.add_cascade(label="Поиск в интервале", menu=search_menu)
        
        # Меню "Проверка на простоту"
        check_menu = tk.Menu(menubar, tearoff=0)
        check_menu.add_command(label="Проверить число", command=self.check_primality)
        menubar.add_cascade(label="Проверка на простоту", menu=check_menu)
        
        # Меню "Вывод результатов"
        output_menu = tk.Menu(menubar, tearoff=0)
        output_menu.add_command(label="Показать результаты", command=self.show_results)
        menubar.add_cascade(label="Вывод результатов", menu=output_menu)
        
        # Меню "Выход"
        menubar.add_command(label="Выход", command=self.root.quit)
    
    def trial_division(self, n):
        """Проверка на простоту методом пробных делений"""
        if n < 2:
            return False, None
        
        # Проверяем делимость на 2 и 3
        if n % 2 == 0:
            return False, 2
        if n % 3 == 0:
            return False, 3
        
        # Проверяем делимость на числа вида 6k±1 до sqrt(n)
        i = 5
        while i * i <= n:
            if n % i == 0:
                return False, i
            if n % (i + 2) == 0:
                return False, i + 2
            i += 6
        
        return True, None
    
    def fermat_test(self, n, bases=None):
        """Тест Ферма на простоту"""
        if bases is None:
            bases = self.fermat_bases
        
        if n < 2:
            return False
        
        if n == 2 or n == 3:
            return True
        
        if n % 2 == 0:
            return False
        
        for a in bases:
            if a >= n:
                continue
            # Проверяем a^(n-1) ≡ 1 (mod n)
            if pow(a, n - 1, n) != 1:
                return False
        
        return True
    
    def is_carmichael(self, n):
        """Проверка на число Кармайкла"""
        if n < 561:  # Наименьшее число Кармайкла
            return False
        
        # Число должно быть составным
        is_prime, _ = self.trial_division(n)
        if is_prime:
            return False
        
        # Проверяем условие Кармайкла: a^(n-1) ≡ 1 (mod n) для всех a, взаимно простых с n
        for a in range(2, min(n, 100)):
            if math.gcd(a, n) == 1:
                if pow(a, n - 1, n) != 1:
                    return False
        
        return True
    
    def generate_prime(self):
        """Генерация случайного простого числа"""
        # Генерируем случайное число в диапазоне
        n = random.randint(10000, 50000)
        
        # Делаем число нечетным
        if n % 2 == 0:
            n += 1
        
        # Ищем ближайшее простое число
        while True:
            is_prime, divisor = self.trial_division(n)
            if is_prime:
                # Дополнительно проверяем тестом Ферма
                if self.fermat_test(n):
                    self.last_checked_number = n
                    self.is_prime_result = True
                    self.divisor_found = None
                    
                    self.text_area.delete(1.0, tk.END)
                    self.text_area.insert(tk.END, f"ПРОВЕРЕНО ЧИСЛО\n")
                    self.text_area.insert(tk.END, f"p={n}\n")
                    self.text_area.insert(tk.END, f"Число простое.\n")
                    self.text_area.insert(tk.END, f"Количество простых чисел при проверке делимости: {len(self.fermat_bases)}\n")
                    self.text_area.insert(tk.END, f"Количество оснований для теста Ферма: {len(self.fermat_bases)}\n")
                    self.text_area.insert(tk.END, f"Тест Ферма выполнен для оснований: {' '.join(map(str, self.fermat_bases))}\n")
                    return
            n += 2  # Проверяем только нечетные числа
    
    def search_in_interval(self):
        """Поиск простых чисел в интервале"""
        start = simpledialog.askinteger("Интервал", "Введите начало интервала:", minvalue=2, maxvalue=100000)
        if start is None:
            return
        
        end = simpledialog.askinteger("Интервал", "Введите конец интервала:", minvalue=start, maxvalue=100000)
        if end is None:
            return
        
        self.prime_numbers = []
        
        for n in range(start, end + 1):
            is_prime, _ = self.trial_division(n)
            if is_prime:
                self.prime_numbers.append(n)
        
        # Выводим результаты
        self.text_area.delete(1.0, tk.END)
        self.text_area.insert(tk.END, "Простые числа:\n\n")
        
        # Выводим по 10 чисел в строке
        for i in range(0, len(self.prime_numbers), 10):
            row = self.prime_numbers[i:i+10]
            self.text_area.insert(tk.END, " ".join(f"{n:5}" for n in row) + "\n")
        
        self.text_area.insert(tk.END, f"\nВсего чисел: {len(self.prime_numbers)}.\n")
        
        # Вычисляем процент
        total_numbers = end - start + 1
        percentage = (len(self.prime_numbers) / total_numbers) * 100
        self.text_area.insert(tk.END, f"Процент простых чисел в данном интервале: {percentage:.2f} %.\n")
    
    def check_primality(self):
        """Проверка конкретного числа на простоту"""
        n = simpledialog.askinteger("Проверка на простоту", "Введите число для проверки:", minvalue=2, maxvalue=1000000)
        if n is None:
            return
        
        self.last_checked_number = n
        
        # Сначала проверяем тестом пробных делений
        is_prime, divisor = self.trial_division(n)
        
        self.text_area.delete(1.0, tk.END)
        self.text_area.insert(tk.END, f"ПРОВЕРЕНО ЧИСЛО\n")
        self.text_area.insert(tk.END, f"p={n}\n")
        
        if not is_prime:
            self.is_prime_result = False
            self.divisor_found = divisor
            self.text_area.insert(tk.END, f"Число не простое.\n")
            self.text_area.insert(tk.END, f"Делимость на {divisor}\n")
        else:
            self.is_prime_result = True
            self.divisor_found = None
            self.text_area.insert(tk.END, f"Число простое.\n")
        
        self.text_area.insert(tk.END, f"Количество оснований для теста Ферма: {len(self.fermat_bases)}\n")
        self.text_area.insert(tk.END, f"Основания для теста Ферма: {' '.join(map(str, self.fermat_bases))}\n")
        
        # Дополнительно проверяем тестом Ферма
        fermat_result = self.fermat_test(n)
        if not is_prime and fermat_result:
            self.text_area.insert(tk.END, f"\nВнимание! Число {n} прошло тест Ферма, но является составным.\n")
            self.text_area.insert(tk.END, f"Это число Кармайкла: {self.is_carmichael(n)}\n")
    
    def show_results(self):
        """Показать сохраненные результаты"""
        self.text_area.delete(1.0, tk.END)
        
        if self.last_checked_number is not None:
            self.text_area.insert(tk.END, f"Последнее проверенное число: {self.last_checked_number}\n")
            if self.is_prime_result:
                self.text_area.insert(tk.END, "Результат: простое число\n")
            else:
                self.text_area.insert(tk.END, f"Результат: составное число")
                if self.divisor_found:
                    self.text_area.insert(tk.END, f" (делитель: {self.divisor_found})\n")
                else:
                    self.text_area.insert(tk.END, "\n")
        
        if self.prime_numbers:
            self.text_area.insert(tk.END, f"\nНайденные простые числа ({len(self.prime_numbers)} шт.):\n")
            for i in range(0, len(self.prime_numbers), 10):
                row = self.prime_numbers[i:i+10]
                self.text_area.insert(tk.END, " ".join(f"{n:5}" for n in row) + "\n")
        else:
            self.text_area.insert(tk.END, "\nПростые числа еще не найдены.\n")


if __name__ == "__main__":
    root = tk.Tk()
    app = PrimeGeneratorApp(root)
    root.mainloop()