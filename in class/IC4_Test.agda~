module IC4_Test where

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

-- takes natural number and goes from nat to nat
data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ

infixl 5 _+_
_+_ : ℕ → ℕ → ℕ
-- fill hole with case analy on m
Z + n = n
-- (S m) + n == S ( m + n)
S m + n = S(m + n)


{-# BUILTIN NATURAL ℕ #-}
three : ℕ
three  = S ( S( S Z ))

three′ : ℕ
three′ = 3

_ : 3 + 2 ≡ 5
_ = ↯

-- _ : ∀ ( m n p : ℕ ) → ( m + n) + p ≡ m + (n + p)
-- _ = {!!}

infixl 6 _x_
_x_ : ℕ → ℕ → ℕ
Z x n = Z 
S m x n = n + m x n

_ : 2 + 3 x 4 ≡ 14
_ = ↯

infixl 5 _∙_
_∙_ : ℕ → ℕ → ℕ
Z ∙ n = Z
S m ∙ Z = S  m
S m ∙ S n = m ∙ n


--_ : 4 ∙ 3 ≡ 1
-- _ : ∀ ( n : ℕ) → n ∙ Z ≡ Z


_ : 2 + 2 x 3 ∙ 7 ≡ 1
-- _ : (2 +( 2 x 3 ))∙ 7 ≡ 1
_ = ↯

-- use rewrite by m = 4
-- L1 : ∀ ( m : ℕ ) → m ≡ 4 → m + 2 ≡ 6
-- L1 m m≡4 = {!!}

L1' : ∀ ( m : ℕ ) → m ≡ 4 → m + 2 ≡ 6
L1' m m≡4 rewrite m≡4 = ↯

L1 : ∀ ( m : ℕ ) → m ≡ 4 → m + 2 ≡ 6
L1 .4 ↯ = ↯

L2 : ∀ ( m : ℕ) → m ≡ 4 → m ≡ 3 → 1 ≡ 2
L2 .4 ↯ ()


--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- assoc[+]  m n p = {!!}

-- step 1induc on m case analysis
--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+]  m n p = {!m!}

-- assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- assoc[+] Z n p = {!!}
-- assoc[+] (S m) n p = {!!}

-- trivial proof n + p ≡ n + p
-- just do ↯
-- assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- assoc[+] Z n p = ↯
-- assoc[+] (S m) n p = {!!}

-- S (e1) + e2 ≡ S(e1+e2) by def
-- S(m) + (n+p) ≡ (S(m)+n)+p by def
--S(m+(n+p))≡S(m+n)+p
--S(m+(n+p))≡ S((m+n)+p)

-- proe by induction ctrl c ctrl .
--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+] Z n p = ↯
--assoc[+] (S m) n p = {!assoc[+} m n p!}

-- Goal: S (m + n + p) ≡ S (m + (n + p))
-- Have: m + n + p ≡ m + (n + p)]

--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+] Z n p = ↯
--assoc[+] (S m) n p = {!assoc[+] m n p!}

 -- rewrite so the goal changes the parenths 
--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+] Z n p = ↯
--assoc[+] (S m) n p rewrite assoc[+] m n p = {!assoc[+] m n p!}

--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+] Z n p = ↯
--assoc[+] (S m) n p rewrite assoc[+] m n p = ↯


 -- above is correct now different way
 -- use with
--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+] Z n p = ↯
--assoc[+] (S m) n p with assoc[+] m n p
--... | IH = {!!}

--assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
--assoc[+] Z n p = ↯
--assoc[+] (S m) n p with assoc[+] m n p
--... | IH rewrite IH = ↯

assoc[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
assoc[+] Z n p = ↯
assoc[+] (S m) n p with  assoc[+] m n p
... | IH rewrite IH = {!!} 
