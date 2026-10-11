# Cryptographic Reference Oracle & Test-Vector Architecture for Stainless

> **Test-Driven Verification Framework for Pure Scala & SMT Solvers**

---

## 1. Концепция и архитектура

Данный модуль реализует внешний контур верификации (**Test-Driven Verification**) для расширения фреймворка Stainless криптографическими примитивами.

### Проблема формальной верификации
Анализатор Stainless и лежащие в его основе SMT-решатели (Z3, CVC5) сталкиваются с неразрешимостью нелинейной целочисленной арифметики (NIA):
$$(a \cdot b) \pmod m \equiv ((a \pmod m) \cdot (b \pmod m)) \pmod m$$
при символьном $m$ приводит к зависанию Z3 (>90 секунд).

### Архитектурное решение (по материалам исследований EPFL-LARA):
1. **Разделение контуров (Two-Contour Strategy):**
   * **Внешний оракул (Python / SageMath):** генерирует строго выверенные тестовые векторы по международным стандартам (NIST, RFC).
   * **JVM Cross-Validation:** тестирует исполняемые алгоритмы на `java.math.BigInteger` перед отправкой в SMT.
   * **Stainless Formal Layer:** верифицирует инварианты кода с опорой на леммы.
2. **Абсолютный отказ от GenC (PR #1778, Issue #1779):**
   GenC компилирует `BigInt` как 32-битный `int`, что фатально для 256-битной криптографии. Весь рантайм строится строго на **JVM (Scala 3 / Java BigInteger)**.
3. **Паттерн свидетелей без кванторов (из `epfl-lara/bolts`):**
   Исключение кванторов ($\forall, \exists$) в пользу явных структур-свидетелей (witnesses), как в `MoreExtendedEuclidGCD.scala`:
   ```scala
   case class BezoutResult(gcd: BigInt, ka: BigInt, kb: BigInt, x: BigInt, y: BigInt)
   ```
4. **Изоляция лемм через `@opaque @inlineOnce` (PR #1749):**
   Предотвращение разворачивания тел доказательств в месте вызова, разгрузка SMT-солвера.

---

## 2. Структура тестовых векторов (`vectors/`)

Все числовые значения продублированы строками `_dec` для детерминированного парсинга в Scala `BigInt(str)`:

| Файл | Стандарт | Описание |
| :--- | :--- | :--- |
| [`secp256k1_vectors.json`](vectors/secp256k1_vectors.json) | SECG secp256k1 | Точки $k \cdot G$, скалярное умножение, сложение, удвоение, инвариант кривой $y^2 \equiv x^3 + 7 \pmod p$. |
| [`nist_p256_vectors.json`](vectors/nist_p256_vectors.json) | FIPS 186-4 (P-256) | Скалярные произведения на secp256r1 ($y^2 \equiv x^3 - 3x + b \pmod p$). |
| [`edge_cases_vectors.json`](vectors/edge_cases_vectors.json) | Вырожденные точки | Нейтральный элемент $\mathcal{O}$, взаимно обратные $P + (-P) = \mathcal{O}$, удвоение при $y = 0$, $[n]G = \mathcal{O}$, $[n+1]G = G$, $[n-1]G = -G$. |
| [`modular_arithmetic_vectors.json`](vectors/modular_arithmetic_vectors.json) | Теория чисел | Тождество Безу ($a \cdot x + b \cdot y = \gcd$), обратный элемент по модулю, 256-битный Тонелли-Шенкс, `modpow` ($e=65537$). |
| [`rfc6979_vectors.json`](vectors/rfc6979_vectors.json) | RFC 6979 | Детерминированная генерация nonce $k$ через HMAC-SHA256 (ECDSA). |
| [`rfc7748_vectors.json`](vectors/rfc7748_vectors.json) | RFC 7748 Sec. 6.1 | Лестница Монтгомери Curve25519 (X25519 Diffie-Hellman). |
| [`rfc8032_vectors.json`](vectors/rfc8032_vectors.json) | RFC 8032 Sec. 7.1 | Twisted Edwards Ed25519 (сжатие точек, генерация открытого ключа). |

---

## 3. Запуск и интеграция

### Единый скрипт валидации:
```bash
./verification/crypto-oracle/run_all.sh
```

### Запуск тестов оракула (Python):
```bash
python3 verification/crypto-oracle/tests/test_oracle.py
```

### Запуск JVM Cross-Validation на Scala 3:
```bash
scala verification/crypto-oracle/tests/CryptoOracleJvmTest.scala
```

---

## 4. Следующие шаги интеграции (Roadmap)

* **PR 2:** Библиотека модулярных лемм `ModArithLemmas` со свойствами сложения, умножения и дистрибутивности в `stainless.math` (`@opaque @inlineOnce`).
* **PR 3:** Реализация `MoreExtendedEuclidGCD`, `modInverse`, `modPow` на Scala со спецификациями Stainless.
* **PR 4:** Реализация типа `FieldElem[P]` ($GF(p)$) и алгоритма Тонелли-Шенкса для сжатия точек кривой.
