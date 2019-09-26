module HelloAgda where

data Bool : Set where
  true  : Bool
  false : Bool

-- input with \bn
data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}
-- {-# BUILTIN ZERO zero #-}
-- {-# BUILTIN SUC succ #-}


-- identity container
data Id (A : Set) : Set where
  pack : A -> Id A

-- empty type, false proposition
-- input with \bot
data ⊥ : Set where

-- polymorphic function, type variable is introduced explicitly
-- \_0 to get subscript
id₀ : (A : Set) -> A -> A
id₀ _ x = x

not : Bool -> Bool
not true  = false
not false = true

-- introduce type variable through explicit argument
id : {A : Set} -> A -> A
id x = x

-- named implicit arguments
const₀ : {A : Set} {B : Set} -> A -> B -> A
const₀ { B = _ } a b = a

constᵢ : ℕ -> ℕ -> ℕ
constᵢ = const₀ {A = ℕ} {B = ℕ}

-- underscore usage

-- 2 guess the type
unpack₀ : {A : _} -> Id A -> A
unpack₀ (pack x) = x

-- same as
unpack₁ : ∀ {A} -> Id A -> A
unpack₁ (pack x) = x

-- signature desugaring
-- ∀ {A} -> Id A -> A
-- <=>
-- {A : _} -> (_ : Id A) -> (_ : A)
-- ^type var       ^type name    ^type name


_==_ : ℕ -> ℕ -> Bool
zero   == zero   = true
zero   == succ _ = false
succ _ == zero   = false
succ n == succ m = n == m

_<_ : ℕ -> ℕ -> Bool
_      < zero   = false
zero   < succ _ = true
succ n < succ m = n < m

-- _+_ : ℕ -> ℕ -> ℕ
-- zero   + m = m
-- succ n + m = succ (n + m)
--
-- _*_ : ℕ -> ℕ -> ℕ
-- zero   * _    = zero
-- _      * zero = zero
-- succ n * m    = m + (n * m)

foldℕ : {A : Set} -> (ℕ -> A -> A) -> A -> (n : ℕ) -> A
foldℕ _ z zero     = z
foldℕ f z (succ n) = f n (foldℕ f z n)

_+_ : ℕ -> ℕ -> ℕ
n + m = foldℕ (\_ (x : ℕ) -> succ x) m n

_*_ : ℕ -> ℕ -> ℕ
n * m = foldℕ (\_ (x : ℕ) -> m + x) 0 n

-- data ℕ₁ : Set where
--   one  : ℕ₁
--   succ : ℕ₁ -> ℕ₁
--
-- toℕ₁ : ℕ -> ℕ₁
-- toℕ₁ zero =



-- gcd : N -> N -> N
-- gcd zero zero

infixl 20 _==_
infixl 20 _<_
infixl 40 _+_
infixl 60 _*_


_$_ : {A : Set} {B : Set} -> (A -> B) -> A -> B
f $ x = f x

_◦_ : {A : Set} {B : Set} {C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f ◦ g = \x -> f $ g x

infixl 30 _$_
infixl 35 _◦_

-- succ ◦ succ $ 10

-- input with \buw
-- ◦

-- _!_ : {n : ℕ} {A : Set} -> ℕ -> Vec A n -> A
-- zero

-- 2 + 3 * 10 == 32

-- Vec A is a family of types indexed by natural numbers
-- Vec A n for following declaration is parameterized by A and indexed by n
data Vec (A : Set) : (n : ℕ) -> Set where
  []   : Vec A zero
  _::_ : {n : ℕ} -> A -> Vec A n -> Vec A (succ n)

_++_ : {A : Set} {n m : ℕ} -> Vec A n -> Vec A m -> Vec A (n + m)
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- Dot patterns
-- dot patterns indicate that argument value is deduced by type checking rather
-- than being pattern-matched
-- arguments should be dotted if there's unique type-correct value for the argument

data Vec₀ (A : Set) : (n : ℕ) -> Set where
  nil  : Vec₀ A zero
  cons : (n : ℕ) -> A -> Vec₀ A n -> Vec₀ A (succ n)

vmap : {A B : Set} -> (n : ℕ) -> (A -> B) -> Vec₀ A n -> Vec₀ B n
vmap .zero     _ nil           = nil
vmap .(succ n) f (cons n x xs) = cons n (f x) (vmap n f xs)


