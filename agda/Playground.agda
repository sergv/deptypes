-- types are values
-- everything is a value <=> everything is a type!

module Playground where -- mandatory declaration

-- Set - type of all datatypes.
-- Since every value has a type and every type has a value (isomorphism?),
-- every type also has type (actually it's a bit more complicated: types can be populated,
-- i.e. there may exist values of the given type, or not populated, but type itself is always
-- a value of type "one level above" than it currently is. At the very bottom there are types
-- of "plain" values (unsure: posibly they are trivial/atomic types?)).
-- So plain types are of type Set, Set is of type Set\_1 which is of type Set\_2 and so on.


-- polymorphic functions take type and, usually, then operate on
-- values of that type

id : (A : Set) → A → A
id _ x = x

-- NB difficulties arise when writing higher-order functions over dependent functions
-- since then you need to manually keep track of where each type originates from

-- Shorthands:
-- (a : A)(b : B) → C = (a : A) → (b : B) → C
-- (a b : A) → B = (a : A) → (b : A) → B

-- Lambdas:
id₂ : (A : Set) → A → A
id₂ = \A x → x

-- Implicit arguments:
id2 : {A : Set} → A → A
id2 {A} x = x -- can refer to implicit args by {...}

-- No search for implicit arguments will be performed,
-- single unification must resolve it.


-- Sample datatype

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
  -- suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
-- {-# BUILTIN ZERO zero  #-}
-- {-# BUILTIN SUC suc    #-}


-- identity container
data Id (A : Set) : Set where
  pack : A -> Id A

-- empty type, false proposition
-- input with \bot
data ⊥ : Set where

-- also could ask typechecker to infer required arg:
f : ℕ → ℕ
f x = id _ x

-- Vec A is family of types indexed by ℕ.
-- Vec is parameterized by A and indexed by ℕ
data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 50 _::_

-- Dot patterns:
-- If there's unique type-correct value for argument then it should be dotted.
-- Arbitrary terms can be dotted, not just patterns.

vmap : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
vmap _ []        = []
vmap f (x :: xs) = f x :: vmap f xs

-- contrast with vectors with explicit length

data Vec2 (A : Set) : ℕ → Set where
  nil  : Vec2 A zero
  cons : (n : ℕ) → A → Vec2 A n → Vec2 A (suc n)

vmap2 : {A B : Set} → (n : ℕ) → (A → B) → Vec2 A n → Vec2 B n
vmap2 .zero    _ nil           = nil
vmap2 .(suc n) f (cons n x xs) = cons n (f x) (vmap2 n f xs)

-- can put dot in another place (but it seems it must be put somewhere)

vmap3 : {A B : Set} → (n : ℕ) → (A → B) → Vec2 A n → Vec2 B n
vmap3 zero    _ nil            = nil
vmap3 (suc n) f (cons .n x xs) = cons n (f x) (vmap2 n f xs)

-- could've tried it with vmap on Vec:

-- vmap' : {A B : Set}{n : ℕ} → (A → B) → Vec A n → Vec B n
-- vmap' {n = .zero}    _ []                = []
-- vmap' {n = .(suc n)} f (x :: xs {n = n}) = f x :: vmap' f xs -- unsure how to refer to n parameter of ::



-- Case in function definition can be omitted if there's no type-correct way
-- of writing it.

-- Checking type inhabitation is undecidable.

-- Absurd pattern, (), is used when there're no possible constructor arguments to
-- put in>


-- Even integers

-- Parameterization doesn't work, must use indexing by integer.
--
-- n even is a proof that n is even, it's not a container parameterized by
-- natural number!
--
-- data _even (n : ℕ) : Set where -- does not work

data _even : ℕ → Set where
  base : zero even
  step : ∀ {n : ℕ} → n even → (suc (suc n)) even


_+_ : ℕ → ℕ → ℕ
zero    + m = m
(suc n) + m = suc (n + m)

-- _+_ : ℕ → ℕ → ℕ
-- zero    + m    = m
-- n       + zero = n
-- (suc n) + m    = suc (n + m)

_+₂_ : ∀ {n m : ℕ} → n even → m even → (n + m) even
base            +₂ m = m
step hypothesis +₂ m = step (hypothesis +₂ m)

data _⁇ (A : Set) : Set where
  ⟨⟩  : A ⁇
  ⟨_⟩ : A → A ⁇

_⟨$⟩_ : {A B : Set} → (A → B) → A ⁇ -> B ⁇
_ ⟨$⟩ ⟨⟩    = ⟨⟩
f ⟨$⟩ ⟨ x ⟩ = ⟨ f x ⟩

infixl 30 _⟨$⟩_

_⟨⋆⟩_ : {A B : Set} → (A → B) ⁇ → A ⁇ -> B ⁇
⟨⟩    ⟨⋆⟩ _    = ⟨⟩
_    ⟨⋆⟩ ⟨⟩    = ⟨⟩
⟨ f ⟩ ⟨⋆⟩ ⟨ x ⟩ = ⟨ f x ⟩

infixl 30 _⟨⋆⟩_

even? : (n : ℕ) → (n even) ⁇
even? zero          = ⟨ base ⟩
even? (suc zero)    = ⟨⟩
even? (suc (suc n)) = step ⟨$⟩ even? n

proveEvenSum : (n : ℕ) → (m : ℕ) → ((n + m) even) ⁇
proveEvenSum n m = (_+₂_) ⟨$⟩ even? n ⟨⋆⟩ even? m

-- 10 + 15
-- proveEvenSum 20 100

data Bool : Set where
  true  : Bool
  false : Bool

data _≡_ : (n : ℕ) → (m : ℕ) → Set where
  refl₀ : zero ≡ zero
  refl : ∀ {n m : ℕ} → n ≡ m → suc n ≡ suc m

-- data _≡_ (A : Set) (B : Set) : Set where
--   refl : A → B → A ≡ B

--ℝ ℂ ▽ ☻ ℕ ⅀ ⊠ ℤ

-- _==_ : (n : ℕ) → (m : ℕ) → Bool
-- zero    == zero    = true
-- (suc n) == (suc m) = true
-- (suc _) == zero    = false
-- zero    == (suc _) = false
--
-- data reflEq : (b : Bool) -> (n : ℕ) → (m : ℕ) → Set where
--   noProof : reflEq false n m
--   reflProof : {n m : ℕ} → n ≡ m → reflEq true n m

trivialEq : (n : ℕ) → n ≡ n
trivialEq zero    = refl₀
trivialEq (suc n) = refl (trivialEq n)

additionAssociativity : (n : ℕ) → (m : ℕ) → (k : ℕ) → (n + (m + k)) ≡ ((n + m) + k)
additionAssociativity zero    m k = trivialEq (m + k)
additionAssociativity (suc n) m k = refl (additionAssociativity n m k)

-- additionAssociativity 1 2 5

_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x

infixr 20 _$_

trivialEqPlusZeroL : (n : ℕ) → (n + zero) ≡ n
trivialEqPlusZeroL zero    = refl₀
trivialEqPlusZeroL (suc n) = refl (trivialEqPlusZeroL n)

trivialEqPlusZeroR : (n : ℕ) → n ≡ (n + zero)
trivialEqPlusZeroR zero    = refl₀
trivialEqPlusZeroR (suc n) = refl (trivialEqPlusZeroR n)

trivialEqPlusZero' : (n : ℕ) → (zero + n) ≡ (n + zero)
trivialEqPlusZero' zero    = refl₀
trivialEqPlusZero' (suc n) = refl (trivialEqPlusZero' n)

trivialEqPlusOne : (n : ℕ) → suc n ≡ (n + suc zero)
trivialEqPlusOne zero    = refl refl₀
trivialEqPlusOne (suc n) = refl (trivialEqPlusOne n)



liftSumSuc : (n : ℕ) →
             (m : ℕ) →
             (suc (n + m)) ≡ (n + suc m)
liftSumSuc zero    m = refl $ trivialEq m
liftSumSuc (suc n) m = refl $ liftSumSuc n m
-- liftSumSuc zero    zero    = refl refl₀
-- liftSumSuc (suc n) zero    = refl $ refl $ trivialEqPlusZeroL n
-- liftSumSuc zero    (suc m) = refl $ trivialEqPlusOne m
-- liftSumSuc (suc n) (suc m) = refl $ refl $ liftSumSuc n m

-- liftSumSucComm : (n : ℕ) →
--                  (m : ℕ) →
--                  (suc (n + m)) ≡ (n + suc m) →
--                  (suc (n + m)) ≡ (m + suc n)
-- liftSumSucComm zero    zero    _        = refl refl₀
-- liftSumSucComm (suc n) zero    _        = refl $ refl $ trivialEqPlusZeroL n
-- liftSumSucComm zero    (suc m) _        = refl $ trivialEqPlusOne m
-- liftSumSucComm (suc n) (suc m) (refl s) = refl $ refl $ liftSumSucComm n m s

-- liftSumSuc : (n : ℕ) → (m : ℕ) → (suc n + m) ≡ (m + suc n)
-- liftSumSuc zero    m = trivialEqPlusOne m
-- -- liftSumSuc (suc n) m = refl $ liftSumSuc n m
-- liftSumSuc (suc n) m = refl $ liftSumSuc n m

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

lem-identity-plus-zero : (n : ℕ) -> (n + 0) == n
lem-identity-plus-zero zero    = refl
lem-identity-plus-zero (suc n) with n | n + 0 | lem-identity-plus-zero n
lem-identity-plus-zero (suc n) | k | w | refl = {!!}

lem-inc-commutativity : (n : ℕ) → (1 + n) == (n + 1)
lem-inc-commutativity zero    = refl
lem-inc-commutativity (suc n) with 1 + n | n + 1 | lem-inc-commutativity n
lem-inc-commutativity (suc n) | k | .k | refl = refl

lem-move-suc : (n : ℕ) → (m : ℕ) → suc (n + m) == (n + suc m)
lem-move-suc zero    m = refl
lem-move-suc (suc n) zero with suc n | n + 1 | lem-move-suc n zero | lem-inc-commutativity n
lem-move-suc (suc n) zero | k | .k | _ | refl = {!!}
lem-move-suc (suc n) (suc m) = {!!}
-- lem-move-suc (suc n) (suc m) with lem-move-suc n m
-- lem-move-suc (suc n) (suc m) | refl = ?


lem-commutativity : (n : ℕ) → (m : ℕ) → (n + m) == (m + n)
lem-commutativity zero     zero    = refl
lem-commutativity zero     (suc m) with m + zero | lem-commutativity zero m
lem-commutativity zero     (suc .k) | k | refl = refl
lem-commutativity (suc n)  zero    with n + zero | lem-commutativity n zero
lem-commutativity (suc .k) zero     | k | refl = refl
lem-commutativity (suc n)  (suc m) with lem-commutativity n m | lem-commutativity (suc n) m | lem-commutativity n (suc m)
lem-commutativity (suc n)  (suc m)  | _ | _ | _ = {!!}
-- lem-commutativity zero    m with m + zero
-- lem-commutativity zero    m | k = ?
-- lem-commutativity (suc n) m with lem-commutativity n m
-- lem-commutativity (suc n) m | refl = ?

-- lem-commutativity (suc n) m = refl (lem-commutativity n m)
  -- case liftSumSuc n m of
  --   refl₀    -> refl (lem-commutativity n m)
  --   refl sub -> refl (lem-commutativity n m)

-- _==?_ : (n : ℕ) → (m : ℕ) → n ≡ m
-- zero    ==? zero    = refl₀
-- (suc n) ==? (suc m) = refl (n == m)


