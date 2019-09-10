module IC4 where

-- UNICODE --

{-
    ×    \x
    ′    \'
    →    \r
    ↯    \zd
    ∀    \all
    ∸    \-.
    ≡    \==
    𝔹    \bbB
    ◇    \di
    ⊚    \oo
    ℕ   \bN
-}

-- LIB --

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x

◇ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
◇ ↯ = ↯

infixl 8 _⊚_
_⊚_ : ∀ {A : Set} {x y z : A} → y ≡ z → x ≡ y → x ≡ z
↯ ⊚ ↯ = ↯

{-# BUILTIN EQUALITY _≡_ #-}

-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --
-- FROM SCRATCH --
-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --
data ℕ : Set where

  Z : ℕ

--
-- n : ℕ
-- -------
-- S(n) : ℕ

  S : ℕ → ℕ

-- import for natural numbers, lets the symbol 1 and so on be not a symbol but linked to numbers

{-# BUILTIN NATURAL ℕ #-}

one : ℕ
one = S Z

one' : ℕ
one' = 1

_+_ : ℕ → ℕ → ℕ
Z + n = n
S m + n = S( m + n)

lunit[+] : ∀ (m : ℕ) → 0 + m ≡ m
lunit[+] m = ↯


runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
-- C^u C^u C^c C^,
runit[+] Z = ↯ 
-- runit[+] (S m) = {!!} use rewrite  {runit[+] m}0 C^c C^.    Goal: S ( m + 0) = S m    Have: (m +0) = m
-- runit[+] (S m) runit[+] m = {runit[+] m}
runit[+] (S m) rewrite runit[+] m = ↯
