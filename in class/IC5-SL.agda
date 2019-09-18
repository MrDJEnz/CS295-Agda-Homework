module IC5-SL where

-- UNICODE --

{-
    ×    \x
    ′    \'
    ℕ    \bbN
    →    \r
    ↯    \zd
    ↯    \zd
    ⇄    \rl
    ∀    \all
    ∸    \-.
    ≡    \==
    ≤    \<=
    ⊚    \oo
    ⊴    \t<=
    ⋈    \bow
    ⋚    \<=>=
    ◇    \di
    ⩎    \hm
    𝔹    \bbB
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

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

postulate
  commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m

{-# BUILTIN NATURAL ℕ #-}

-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --
-- FROM SCRATCH --
-- ⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄⌄ --

-- “count up from zero, hit the LHS first”
infix 4 _≤_

-- binary relation of Nat to Nat into a set
-- base case write Z, and use same Z as ℕ
-- show the axiom that for all n Z ≤ n

-- -----
-- Z ≤ n

-- successor case for all m and n where m ≤ n and m+1 ≤ n+1

data _≤_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z ≤ n
--       m ≤ n
--   -----------
--   S(m) ≤ S(n)
  S : ∀ {m n} → m ≤ n → S m ≤ S n


_ : 2 ≤ 4
_ = S (S Z)

_ : 2 ≤ 4 -- ctrl c ctrl r
_ = S (S Z)

-- inversion
e1 : ∀ (m n p : ℕ) → S m ≤ p → {!!} 
e1 m n (S p′) (S eps)  = {!!}

xRx[≤] : ∀ (m : ℕ) → m ≤ m
xRx[≤] Z = Z
xRx[≤] (S m) = S (xRx[≤] m)

_⊚[≤]_ : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
n≤p ⊚[≤] Z = Z
S n≤p ⊚[≤] S m≤n = S (n≤p ⊚[≤] m≤n)

_⋈[≤]_ : ∀ {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
Z ⋈[≤] Z = ↯
S m≤n ⋈[≤] S n≤m rewrite m≤n ⋈[≤] n≤m = ↯

rmono[+/≤] : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
rmono[+/≤] Z n p n≤p = n≤p
rmono[+/≤] (S m) n p n≤p = S (rmono[+/≤] m n p n≤p)

lmono[+/≤] : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
lmono[+/≤] m n p m≤n rewrite commu[+] m p | commu[+] n p = rmono[+/≤] p m n m≤n

-- “count down from RHS”
infix 4 _⊴_
data _⊴_ : ℕ → ℕ → Set where
  Z : ∀ {n} → n ⊴ n
  S : ∀ {m n} → m ⊴ n → m ⊴ S n

xRx[⊴]  : ∀ (m : ℕ) → m ⊴ m
xRx[⊴] m = Z

_⊚[⊴]_ : ∀ {m n p : ℕ} → n ⊴ p → m ⊴ n → m ⊴ p
Z ⊚[⊴] m⊴n = m⊴n
S n⊴p ⊚[⊴] m⊴n = S (n⊴p ⊚[⊴] m⊴n)

-- also “m ≤ n ≜ exists p s.t. m + p ≡ n”
-- we will do this later
