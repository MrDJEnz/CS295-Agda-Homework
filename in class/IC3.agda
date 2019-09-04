module IC3 where

-- UNICODE --

-- ′: \'
-- ↯: \zd
-- ∀: \all
-- ≡: \==
-- 𝔹: \bbB
--  
-- LIB --

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- FROM SCRATCH --
 -- create a new type boolean as a set
data 𝔹 : Set where
   True : 𝔹
   False : 𝔹


data color : Set where
   Red : color
   Green : color
   Blue : color
-- ctr-c ctrl-c will create the 3 colors if you do c in goals
-- is-red : {c }0
-- ctr-c ctrl-f forward.... ctr-c ctrl-b back
is-red : color → 𝔹
is-red Red = True
is-red Green = False
is-red Blue = False


data animal : Set where
   Cat : animal
   Dog : animal
   Fish : animal


duncan-has-one : animal → 𝔹
duncan-has-one Cat = False 
duncan-has-one Dog  = True
duncan-has-one Fish = False

-- use duncan-wants function the argument fills the [_]
-- given animal will return T/F
postulate
   duncan-wants[_] : animal → Set
   dwc : duncan-wants[ Cat ]
   dwd : duncan-wants[ Dog ]
   dwf : duncan-wants[ Fish ]

duncan-wants-all-animals : ∀ (a : animal) → duncan-wants[ a ]
duncan-wants-all-animals Cat = dwc
duncan-wants-all-animals Dog = dwd
duncan-wants-all-animals Fish = dwf

has-implies-wants : ∀ (a : animal) → duncan-has-one a ≡ True → duncan-wants[ a ]
has-implies-wants Cat  has[a] = dwc
has-implies-wants Dog has[a] = dwd
-- type in plies-wants Fish has[a] = {has[a}3
has-implies-wants Fish ()


-- natural numbers are a set Zero natural number and succesor natural number
-- semantic {-# BUILTIN NATUAL N #-}   five : nat, and five = 5
-- five' : nat       five' =  S (S ( S ( S (S Z))))

-- lemma-1 : five = five'
-- lemma-1 = { }0    -->    fully reduce and compute  -->  lemma-1  = plies-wants Fish ()  
