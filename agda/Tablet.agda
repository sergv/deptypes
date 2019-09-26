-- types are values
-- everything is a value <=> everything is a type!

module Tablet where -- mandatory declaration

-- Set - type of all datatypes.
-- Since every value has a type and every type is identified by a value (isomorphism?),
-- every type also has type (actually it's a bit more complicated: types can be populated,
-- i.e. there may exist values of the given type, or not populated, but type itself is always
-- a value of type "one level above" than it currently is. At the very bottom there are types
-- of "plain" values (unsure: posibly they are trivial/atomic types?)).
-- So plain types are of type Set, Set is of type Set\_1 which is of type Set\_2 and so on.


data N : Set where
  zero : N
  suc  : N → N

-- polymorphic functions take type and, usually, then operate on
-- values of that type

id : (A : Set) → A → A
id _ x = x

_comp_ : {A B C : Set} → (B → C) → (A → B) → A → C
f comp g = \x → f (g x)

-- NB difficulties arise when writing higher-order functions over dependent functions
-- since then you need to manually keep track of where each type originates from

-- Shorthands:
-- (a : A)(b : B) → C = (a : A) → (b : B) → C
-- (a b : A) → B = (a : A) → (b : A) → B
-- \forall {A} → A → B = {A : _} → A → B

-- Lambdas:
id2 : (A : Set) → A → A
id2 = \A x → x

-- Implicit arguments:
id3 : {A : Set} → A → A
id3 {A} x = x -- can refer to implicit args by {...}

-- also could ask typechecker to infer required arg:
f : N → N
f x = id _ x

-- No search for implicit arguments will be performed,
-- single unification must resolve it.


data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

maybe : ∀ {A B : Set} → (A → B) → B → Maybe A → B
maybe _ def nothing  = def
maybe f _   (just x) = f x

_<$>_ : ∀ {A B} → (A → B) → Maybe A → Maybe B
_ <$> nothing  = nothing
f <$> (just x) = just (f x)

_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x

infixr 20 _$_

-- _o_ : {A B C : Set} → (B → C) → (A → B) → A → C
_o_ : {A : Set}{B : A → Set}{C : (x : A) → B x → Set} →
      ({x : A} → (y : B x) → C x y) →
      (f : (x : A) → B x) →
      (x : A) →
      C x (f x)
(f o g) x = f (g x)

infixr 15 _o_

-- Sample datatype

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat
  -- suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}

even? : Nat → Bool
even? zero          = true
even? (suc zero)    = false
even? (suc (suc n)) = even? n

_+_ : Nat → Nat → Nat
zero    + m = m
(suc n) + m = suc (n + m)

-- Vec A is family of types indexed by Nat.
-- Vec is parameterized by A and indexed by Nat
-- When defining constructors we can refer to parameters, but not indices.
-- Parameters are semantically equivalent to universally quantified indices.
-- Recursive types are called inductive types in Agda to imply finiteness
-- of these data structures and facilitate inductive reasoning.
-- Parameters are chosen outside for the whole type and they parameterize
-- type uniformly in all recursive occurences (i.e. in general all recursive
-- occurrences of type being defined are applied to the same parameterts, but
-- this is not mandatory).
-- Indexes, on the other hand, are chosen at every constructor application.
data Vec (A : Set) : Nat → Set where
  []   : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 60 _::_

-- Dot patterns:
-- If there's unique type-correct value for argument then it should be dotted.
-- Arbitrary terms can be dotted, not just patterns.

vmap : {A B : Set}{n : Nat} → (A → B) → Vec A n → Vec B n
vmap _ []        = []
vmap f (x :: xs) = f x :: vmap f xs

-- contrast with vectors with explicit length

data Vec2 (A : Set) : Nat → Set where
  nilV  : Vec2 A zero
  consV : (n : Nat) → A → Vec2 A n → Vec2 A (suc n)

vmap2 : {A B : Set} → (n : Nat) → (A → B) → Vec2 A n → Vec2 B n
vmap2 .zero    _ nilV           = nilV
vmap2 .(suc n) f (consV n x xs) = consV n (f x) (vmap2 n f xs)

-- can put dot in another place (but it seems it must be put somewhere)

vmap3 : {A B : Set} → (n : Nat) → (A → B) → Vec2 A n → Vec2 B n
vmap3 zero    _ nilV            = nilV
vmap3 (suc n) f (consV .n x xs) = consV n (f x) (vmap2 n f xs)

-- could've tried it with vmap on Vec:

-- invalid left-hand side in definition
--vmap' : {A B : Set}{n : Nat} → (A → B) → Vec A n → Vec B n
--vmap' {n = .zero}    _ []                = []
--vmap' {n = .(suc n)} f (x :: xs {n = n}) = f x :: vmap' f xs -- unsure how to refer to n parameter of ::



-- Case in function definition can be omitted if there's no type-correct way
-- of writing it.

-- Checking type inhabitation is undecidable.

-- Absurd pattern, (), is used when there're no possible constructor arguments to put in

-- type of numbers less than n:
data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

-- example of absurd pattern since Fin zero is impossible value
magic : Fin zero → Nat
magic () -- no valid constructors to patternmatch on

{-
-- safe indexing in vector
_!_ : {A : Set}{n : Nat} → Vec A n → Fin n → A
[]        ! () -- impossible case
(x :: _)  ! fzero    = x
(x :: xs) ! (fsuc k) = xs ! k
-}

-- NB it would be terrific to have polymorptic types with constraints
-- in order to automatically convert Nat to Fin
-- conv : (n : Nat) → Fin m, n < m

-- Programs as proofs:

-- uninhabited datatype
data False : Set where

-- record with no fields and with single value - the empty record
data True : Set where
  tt : True
-- record True : Set where

isTrue : Bool → Set
isTrue true  = True
isTrue false = False

isFalse : Bool → Set
isFalse x = isTrue (not x)

¬ : Set → Set
¬ x = x → False

-- removeDoubleNot : {x : Set} → ¬ (¬ x) → x
-- removeDoubleNot {z} prop = z

introduceDoubleNot : {x : Set} → x → ¬ (¬ x)
introduceDoubleNot prop = \f → f prop

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map _ []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 30 _++_

_<<_ : Nat → Nat → Bool
zero    << zero    = false
zero    << (suc _) = true
(suc _) << zero    = false
(suc n) << (suc m) = n << m

length : {A : Set} → List A → Nat
length []        = zero
length (_ :: xs) = suc (length xs)

-- safe indexing into plain list
_!!_given_ : {A : Set} → (xs : List A) → (n : Nat) → isTrue (n << length xs) → A
[]        !! zero    given ()
[]        !! (suc _) given ()
(x :: _)  !! zero    given p = x
(_ :: xs) !! (suc n) given p = xs !! n given p

testList : List Nat
testList = 0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: 10 :: []

-- False just has no value, so when your function accepts it there's no way
-- to return anything because function cannot pattern-match on False and
-- must use absurd pattern, (), and omit right-hand side in that case.
-- So there's no way to construct proof of implication "False ==> x".

-- correspondence between types, logic and arithmetic constructs
-- Type         | Logic       | Arithmetic
-- -------------+-------------+---------------
-- function     | implication | exponentiation (for finite domains & codomains)
-- product type | conjunction | multiplication
-- sum type     | disjunction | addition
-- unit type    | true        | 1
-- empty type   | false       | 0
-- A → False    | negation    | ?

-- Conjunction has two values of types P and Q that denote some propositions.
-- If we have values of type P and of type Q then we have proofs of those propositions
-- and therefore can construct proof of conjunction of those propositions.

data _/\_ (A : Set) (B : Set) : Set where
  conj-intro : A → B → A /\ B

data _\/_ (A : Set) (B : Set) : Set where
  disj-left  : A → A \/ B
  disj-right : B → A \/ B

-- data _\/2_ : (A : Set) → (B : Set) → Set1 where
--   disj2-left  : {A B : Set} → A → A \/2 B
--   disj2-right : {A B : Set} → B → A \/2 B

-- Bijection

_<=>_ : {A B : Set} → (A → B) → (B → A) → (A → B) /\ (B → A)
p <=> q = conj-intro p q


-- false values - valuess for which there exists no proof
-- negation of A is encoded as type A → False

-- not : Set → Set
-- not A = A → False

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infixr 30 _≡_

eq-ind-base : zero ≡ zero
eq-ind-base = refl {Nat}

eq-nat-ind : {n m : Nat} → n ≡ m → (suc n) ≡ (suc m)
eq-nat-ind refl = refl {Nat}

data _eq'_ {A : Set} (x : A) : A → Set where
  refl' : x eq' x

eq-ind-base' : zero eq' zero
eq-ind-base' = refl' {Nat}

eq-nat-ind' : {n m : Nat} → n eq' m → (suc n) eq' (suc m)
eq-nat-ind' refl' = refl' {Nat}


-- Dependent patternmatching is powerful and can refine whole computation
-- context. I.e. it can refine type of function the patternmatching occurs in.
-- When "with" construct matches expression "e", all occurrences of "e", or
-- anything dependent on "e" are
-- refined, i.e. occurencu=

min : Nat → Nat → Nat
min x y with x << y
min x y | true  = x
min x y | false = y

-- since matching x < y result does not rofine types, we can rewrite to

min' : Nat → Nat → Nat
min' x y with x << y
... | true  = x
... | false = y


filter : {A : Set} → (A → Bool) → List A → List A
filter _ [] = []
filter f (x :: xs) with f x
... | true  = x :: filter f xs
... | false = filter f xs

data _=/=_ : Nat → Nat → Set where
  neq-lt  : {m : Nat} → zero    =/= (suc m)
  neq-gt  : {n : Nat} → (suc n) =/= zero
  neq-ind : {n m : Nat} → n =/= m → (suc n) =/= (suc m)

neq-implies-specific-inequality : {n m : Nat} → n =/= m → (isTrue (n << m)) \/ (isTrue (m << n))
neq-implies-specific-inequality neq-lt         = disj-left tt
neq-implies-specific-inequality neq-gt         = disj-right tt
neq-implies-specific-inequality (neq-ind step) = neq-implies-specific-inequality step

-- filter-reduces-size-proof : {A : Set} → (A → Bool) → List A → length

-- todo: print out unresolved metas since it's impossible to
-- figure out what's the problem

data _sublistOf_ {A : Set} : List A → List A → Set where
  stop : [] sublistOf []
  drop : {xs ys : List A} → (y : A) → xs sublistOf ys → xs sublistOf (y :: ys)
  take : {xs ys : List A} → (y : A) → xs sublistOf ys → (y :: xs) sublistOf (y :: ys)

lem-filter : {A : Set} → (p : A → Bool) → (xs : List A) → (filter p xs) sublistOf xs
lem-filter _ [] = stop
lem-filter p (x :: xs) with p x
lem-filter p (x :: xs) | true  = take x (lem-filter p xs)
lem-filter p (x :: xs) | false = drop x (lem-filter p xs)

-- plus-zero-is-identity : (n : Nat) → (n + zero) eq n
-- plus-zero-is-identity zero = refl
-- plus-zero-is-identity (suc n) with plus-zero-is-identity n
-- plus-zero-is-identity (suc n) | refl = refl

-- correct implementation of n + 0 ≡ n

-- The trick is to move (n + zero) into with block so
-- it will be abstracted away from expression and goals into some variable, say m.
-- There's no way to unify n with (n + zero) directly, but there's a way to unify
-- n with m = (n + zero).
lem-plus-zero : (n : Nat) → (n + zero) ≡ n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
lem-plus-zero (suc n) | .n | refl = refl


-- Records

record Point : Set where
  field x : Nat
        y : Nat

origin : Point
origin = record{ x = zero; y = zero }

-- Exercises 2.9

Matrix : Set → Nat → Nat → Set
Matrix A n m = Vec (Vec A m) n

-- 2.1

pure : {A : Set}{n : Nat} → A → Vec A n
pure {n = zero}  _ = []
pure {n = suc n} x = x :: pure x

infixl 90 _<*>_

_<*>_ : {A B : Set}{n : Nat} → Vec (A → B) n → Vec A n → Vec B n
[]        <*> []        = []
(f :: fs) <*> (x :: xs) = f x :: (fs <*> xs)

transpose : {A : Set}{n m : Nat} → Matrix A n m → Matrix A m n
transpose []          = pure []
transpose (xs :: xss) = pure _::_ <*> xs <*> transpose xss

matrix : Matrix Nat 3 4
matrix = xs
      :: xs
      :: xs
      :: []
  where
  xs = 4 :: 3 :: 2 :: 1 :: []

-- 2.3

sublistOf-refl : {A : Set}{xs : List A} → xs sublistOf xs
sublistOf-refl {xs = []}      = stop
sublistOf-refl {xs = x :: xs} = take x sublistOf-refl

sublistOf-trans : {A : Set}{xs ys zs : List A} →
                  xs sublistOf ys → ys sublistOf zs → xs sublistOf zs
-- sublistOf-trans stop stop = stop
sublistOf-trans stop        stop         = stop
sublistOf-trans stop        (drop z p2)  = drop z p2
-- sublistOf-trans stop        (take ys)    = ? -- Invalid case, stop states that
                                                -- we reached end of xs and ys,
                                                -- so ys cannot non-empty in
                                                -- second proof object,
                                                -- ys sublitsOf zs.
sublistOf-trans (drop y p1) (drop z p2)  = drop z $ sublistOf-trans (drop y p1) p2
sublistOf-trans (drop y p1) (take .y p2) = drop y $ sublistOf-trans p1 p2
sublistOf-trans (take y p1) (drop z p2)  = drop z $ sublistOf-trans (take y p1) p2
sublistOf-trans (take y p1) (take .y p2) = take y $ sublistOf-trans p1 p2
-- -- Once we matched on first drop we're refined ys into (cons y ys) in both
-- -- arguments.
-- sublistOf-trans (drop {xs = xs}          {ys = ys} y p1)
--                 (drop {xs = .(cons y ys)}{ys = zs} z p2) = drop z $ sublistOf-trans (drop y p1) p2

data SubList {A : Set} : List A → Set where
  [] : SubList []
  _::_ : {xs : List A} → (x : A) → SubList xs → SubList (x :: xs)
  skip : {xs : List A}{x : A} → SubList xs → SubList (x :: xs)

forget : {A : Set}{xs : List A} → SubList xs → List A
forget []        = []
forget (x :: xs) = x :: forget xs
forget (skip xs) = forget xs

lem-forget : {A : Set}{xs : List A} → (zs : SubList xs) → (forget zs) sublistOf xs
lem-forget []                = stop
lem-forget (x :: xs)         = take x $ lem-forget xs
lem-forget (skip {x = x} xs) = drop x $ lem-forget xs

filter' : {A : Set} → (A → Bool) → (xs : List A) → SubList xs
filter' _ [] = []
filter' f (x :: xs) with f x
... | true  = x :: filter' f xs
... | false = skip $ filter' f xs

complement : {A : Set}{xs : List A} → SubList xs → SubList xs
complement []                = []
complement (x :: xs)         = skip {x = x} $ complement xs
complement (skip {x = x} xs) = x :: complement xs

sublists : {A : Set} → (xs : List A) → List (SubList xs)
sublists []        = [] :: []
sublists (x :: xs) = map (_::_ x) xss ++ map skip xss
  where
    xss = sublists xs

-- try forbidding addition of 0

_≠0 : Nat → Set
zero    ≠0 = False
(suc _) ≠0 = True

nzplus : (n : Nat) → {nz : n ≠0} → (m : Nat) → {mz : m ≠0} → Nat
nzplus zero    {} zero    {}
nzplus zero    {} (suc _)
nzplus (suc _)    zero    {}
nzplus (suc n)    (suc m)    = suc n + suc m

--testNzPlus : Nat
--testNzPlus = nzplus 9 4 -- nzplus 0 1 is forbidden

{- -- Also prevents addition to 0, but gives
-- uninformative "unresolved metas" error in the repl.
nzplus' : (n : Nat) → {nz : n ≠0} → (m : Nat) → Nat
nzplus' zero    {()} _
nzplus' (suc n)      m      = suc n + m

testNzPlus' : Nat
testNzPlus' = nzplus' 0 {_} 9
-}

satisfies : {A : Set} → (A → Bool) → A → Set
-- satisfies p x with p x
-- satisfies p x | true  = True
-- satisfies p x | false = False
satisfies p x = isTrue (p x)

data All {A : Set} (p : A → Bool) : List A → Set where
  all[]   : All p []
  _all::_ : {x : A}{xs : List A} → satisfies p x → All p xs → All p (x :: xs)

data Find {A : Set} (p : A → Bool) : List A → Set where
  found     : (xs : List A) → (y : A) → (zs : List A) → satisfies p y → Find p (xs ++ y :: zs)
  not-found : {xs : List A} → All (not o p) xs → Find p xs

data Inspect {A : Set} (x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} → (x : A) → Inspect x
inspect x = it x refl

-- data _==1_ {A : Set1} (x : A) : A → Set1 where
--   refl1 : x ==1 x
--
-- data Inspect1 {A : Set1} (x : A) : Set1 where
--   it : (y : A) → x ==1 y → Inspect1 x
--
-- inspect1 : {A : Set1} → (x : A) → Inspect1 x
-- inspect1 x = it x refl1

trueIsTrue : {x : Bool} → x ≡ true → isTrue x
trueIsTrue refl = tt

satisfiesTrue : ∀ {A : Set}{p : A → Bool}{x : A} → p x ≡ true → satisfies p x
satisfiesTrue {_} {p} {x} prf = trueIsTrue prf

{-
trueIsTrue1 : {x : Set} → x ==1 True → isTrue x
trueIsTrue1 refl1 = tt
-}

falseIsFalse : {x : Bool} → x ≡ false → isFalse x
falseIsFalse refl = tt

cong : {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

nat-eq : (n m : Nat) → Maybe (n ≡ m)
nat-eq zero    zero    = just refl
nat-eq zero    (suc _) = nothing
nat-eq (suc _) zero    = nothing
nat-eq (suc n) (suc m) with nat-eq n m
nat-eq (suc n) (suc m)  | nothing   = nothing
nat-eq (suc n) (suc .n) | just refl = just refl

{-
filter-lem : {A : Set} → (p : A → Bool) → (xs : List A) → All p (filter p xs)
filter-lem _ []        = all[]
filter-lem p (x :: xs) with inspect (p x)
-- filter-lem p (x :: xs) | it true  prf = {!!} all:: filter-lem p xs
filter-lem p (x :: xs) | it true  prf with p x
filter-lem p (x :: xs) | it true  prf | true = trueIsTrue prf all:: filter-lem p xs
filter-lem p (x :: xs) | it true ()   | false

-- filter-lem p (x :: xs) | it true  prf with p x
-- filter-lem p (x :: xs) | it true  refl | .true = (satisfiesTrue {_} {p} {x} {!!}) all:: filter-lem p xs
filter-lem p (x :: xs) | it false prf = {!!} -- filter-lem p xs
-}
--filter-lem p (x :: xs) with p x | inspect (p x) | satisfies p x | isTrue (p x)
--filter-lem p (x :: xs) | .true  | it true  refl | foo | bar = {!bar all:: filter-lem p xs!}
--filter-lem p (x :: xs) | .false | it false refl | foo | bar = {!!} -- filter-lem p xs

{-
-- filter-lem p (x :: xs) with inspect (p x)
-- filter-lem p (x :: xs) | it true  prf = (trueIsTrue prf) all:: (filter-lem p xs)
-- filter-lem p (x :: xs) | it false prf = {!!} -- filter-lem p xs

{-
-- filter-lem p (x :: xs) = filter-lem p xs
filter-lem p (x :: xs) with (p x)
-- filter-lem p (x :: xs) | it true  prf = {!!} -- all:: (filter-lem p xs)
filter-lem p (x :: xs) | true  with inspect (p x)
filter-lem p (x :: xs) | .true  | it true  refl = {!!} all:: (filter-lem p xs)
--filter-lem p (x :: xs) | true  | it false prf = {!!}
filter-lem p (x :: xs) | false with inspect (p x)
filter-lem p (x :: xs) | .false | it false prf = {!!} -- filter-lem p xs
--filter-lem p (x :: xs) | false | it true prf = {!!} -- filter-lem p xs
-}

-- filter-lem p (x :: xs) with inspect (p x)
-- -- filter-lem p (x :: xs) | it true  prf = {!!} -- all:: (filter-lem p xs)
-- filter-lem p (x :: xs) | it true  prf with p x
-- filter-lem p (x :: xs) | it true  refl | .true = trueIsTrue refl all:: (filter-lem p xs)
-- filter-lem p (x :: xs) | it false prf = {!!} -- filter-lem p xs

filter-lem p (x :: xs) with (p x) | inspect (p x)
filter-lem p (x :: xs) | .true  | it true  refl with inspect1 (isTrue (p x))
filter-lem p (x :: xs) | .true
                       | it true refl
                       | it True prf =
                         True all:: (filter-lem p xs)
filter-lem p (x :: xs) | .false | it false refl  = filter-lem p xs
-}

{-
find : {A : Set} → (p : A → Bool) → (xs : List A) → Find p xs
find _ [] = not-found all[]
find p (x :: xs) with inspect (p x)
find p (x :: xs) | it true prf = found [] x xs (trueIsTrue prf)
find p (x :: xs) | it false prf with find p xs
find p (x :: .(xs ++ y :: zs))
                 | it false _
                 | found xs y zs prf' = found (x :: xs) y zs prf'
find p (x :: _)
                 | it false prf
                 | not-found prfs     = not-found (falseIsFalse prf all:: prfs)

data Find' {A : Set} (p : A → Bool) : List A → Set where
  found     : (xs : List A) → (y : A) → (zs : List A) → satisfies p y → Find p (xs ++ y :: zs)
  not-found : {xs : List A} → All (satisfies (not o p)) xs → Find p xs


find : {A : Set} → (p : A → Bool) → (xs : List A) → Find p xs
find _ [] = not-found all[]
find p (x :: xs) with inspect (p x)
find p (x :: xs) | it true prf = found [] x xs (trueIsTrue prf)
find p (x :: xs) | it false prf with find p xs
find p (x :: .(xs ++ y :: zs))
                 | it false _
                 | found xs y zs prf' = found (x :: xs) y zs prf'
find p (x :: _)
                 | it false prf
                 | not-found prfs     = not-found (falseIsFalse prf all:: prfs)
-}

-- Type inference

data _∈_ {A : Set} (x : A) : List A → Set where
  hd : {xs : List A} → x ∈ (x :: xs)
  tl : {x' : A}{xs : List A} → x ∈ xs → x ∈ (x' :: xs)

index : ∀ {A : Set}{x : A}{xs} → x ∈ xs → Nat
index hd       = zero
index (tl prf) = suc $ index prf

lastOccurence : ∀ {A} →
                ((a : A) → (b : A) → Maybe (a ≡ b)) →
                (x : A) →
                (xs : List A) →
                Maybe (x ∈ xs)
lastOccurence _ x [] = nothing
lastOccurence eq x (y :: ys) with lastOccurence eq x ys | eq x y
lastOccurence eq x (.x :: ys) | nothing  | just refl = just hd
lastOccurence eq x (y :: ys)  | nothing  | nothing    = nothing
lastOccurence eq x (y :: ys)  | just prf | _    = just $ tl prf

-- view on natural numbers into a given list
data Lookup {A : Set} (xs : List A) : Nat → Set where
  inside  : ∀ {x} → (prf : x ∈ xs) → Lookup xs (index prf)
  outside : (m : Nat) → Lookup xs (length xs + m)

_!_ : ∀ {A : Set} → (xs : List A) → (n : Nat) → Lookup xs n
[]        ! n    = outside n
(x :: _)  ! zero = inside hd
(x :: xs) ! (suc n) with xs ! n
(x :: xs) ! (suc .(index prf))     | inside prf = inside (tl prf)
(x :: xs) ! (suc .(length xs + m)) | outside m  = outside m

infixl 50 _!_

data Type : Set where
  *   : Type
  _⇒_ : Type → Type → Type

sampleType : Type
sampleType = (* ⇒ *) ⇒ * ⇒ *

infixr 30 _⇒_


data Different? : Type → Type → Set where
  atom≠func : ∀ {a b c}                                     → Different? a       (b ⇒ c)
  func≠atom : ∀ {a b c}                                     → Different? (a ⇒ b) c
  arg≠arg   : ∀ {a b c}                    → Different? a b → Different? (a ⇒ c) (b ⇒ c)
  res≠res   : ∀ {a b c}                    → Different? b c → Different? (a ⇒ b) (a ⇒ c)
  func≠func : ∀ {a b c d} → Different? a c → Different? b d → Different? (a ⇒ b) (c ⇒ d)


data Equal? : Type → Type → Set where
  same      : ∀ {τ}   → Equal? τ τ
  different : ∀ {τ σ} → Different? τ σ → Equal? τ σ

_≟_ : (t : Type) → (t' : Type) → Equal? t t'
*       ≟ *        = same
*       ≟ (_ ⇒ _) = different atom≠func
(_ ⇒ _) ≟ *        = different func≠atom
(a ⇒ b) ≟ (c ⇒ d) with a ≟ c | b ≟ d
(a ⇒ b) ≟ (.a ⇒ .b) | same          | same           = same
(a ⇒ b) ≟ (.a ⇒ d)  | same          | different prf  = different (res≠res prf)
(a ⇒ b) ≟ (c ⇒ .b)  | different prf | same           = different (arg≠arg prf)
(a ⇒ b) ≟ (c ⇒ d)   | different prf | different prf' = different (func≠func prf prf')

-- raw lambda terms

data Raw : Set where
  var : Nat → Raw
  _#_ : Raw → Raw → Raw
  lam : Type → Raw → Raw

infixl 80 _#_

Cxt : Set
Cxt = List Type

-- This type determines correspondence between Raw terms and their types.
data Term (Γ : Cxt) : Type → Set where
  var : ∀ {τ}   → τ ∈ Γ → Term Γ τ
  _#_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ {τ}   → (σ : Type) → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)

erase : ∀ {Γ τ} → Term Γ τ → Raw
erase (var prf)   = var $ index prf
erase (f # x)     = erase f # erase x
erase (lam arg x) = lam arg $ erase x

-- Type inference view. Since we're constructing inferred type, it is not a
-- parameter of the view but an index.

data Infer (Γ : Cxt) : Raw → Set where
  ok            : (τ : Type) → (t : Term Γ τ) → Infer Γ (erase t)
  bad           : ∀ {e}      → Infer Γ e
  type-mismatch : ∀ {e σ τ}  → Different? σ τ → Infer Γ e
  unbound-var   : ∀ {e}      → (n : Nat)  → Infer Γ e
  invalid-app   : ∀ {e Γ'}   → Term Γ' * → Infer Γ e
  -- invalid-app   : ∀ {τ α β}   → (t : Term Γ τ) → Different? τ (α ⇒ β) → Infer Γ (erase t)

infer : (Γ : Cxt) → (e : Raw) → Infer Γ e
infer Γ (var x) with Γ ! x
infer Γ (var .(index prf))    | inside {t} prf = ok t (var prf)
infer Γ (var .(length Γ + m)) | outside m      = unbound-var (length Γ + m)
infer Γ (f # x) with infer Γ f
infer Γ (f # x)                   | bad               = bad
infer Γ (f # x)                   | type-mismatch d   = type-mismatch d
infer Γ (f # x)                   | unbound-var n     = unbound-var n
infer Γ (f # x)                   | invalid-app t     = invalid-app t
infer Γ (.(erase f) # x)          | ok τ f with infer Γ x
infer Γ (.(erase f) # x)          | ok τ f       | bad             = bad
infer Γ (.(erase f) # x)          | ok τ f       | type-mismatch d = type-mismatch d
infer Γ (.(erase f) # x)          | ok τ f       | unbound-var n   = unbound-var n
infer Γ (.(erase f) # x)          | ok τ f       | invalid-app t   = invalid-app t
infer Γ (.(erase f) # .(erase x)) | ok * f       | ok ξ x          = invalid-app f
infer Γ (.(erase f) # .(erase x)) | ok (σ ⇒ τ) f | ok ξ x with σ ≟ ξ
infer Γ (.(erase f) # .(erase x)) | ok (σ ⇒ τ) f | ok .σ x | same        = ok τ (f # x)
infer Γ (.(erase f) # .(erase x)) | ok (σ ⇒ τ) f | ok ξ x  | different d = type-mismatch d
infer Γ (lam σ body) with infer (σ :: Γ) body
infer Γ (lam σ .(erase t)) | ok τ t          = ok (σ ⇒ τ) (lam σ t)
infer Γ (lam σ body)       | bad             = bad
infer Γ (lam σ body)       | type-mismatch x = type-mismatch x
infer Γ (lam σ body)       | unbound-var n   = unbound-var n
infer Γ (lam σ body)       | invalid-app x   = invalid-app x

-- infer [] (lam (* ‌⇒ *) (lam * (var 1 # var 0)))

-- GCD

-- data _≤_ : Nat → Nat → Set where
--   ≤-base : ∀ {n} → zero ≤ n
--   ≤-step : ∀ {n m} → n ≤ m → (suc n) ≤ (suc m)
--
-- _le_ : (n : Nat) → (m : Nat) → Maybe (n ≤ m)
-- zero    le _       = just ≤-base
-- (suc _) le zero    = nothing
-- (suc n) le (suc m) = ≤-step <$> (n le m)
--
-- sub : (n : Nat) → (m : Nat) → m ≤ n → Nat
-- sub n       zero    ≤-base       = n
-- sub zero    (suc _) ()
-- sub (suc n) (suc m) (≤-step prf) = sub n m prf
--
-- 0≠_ : Nat → Bool
-- 0≠ zero    = false
-- 0≠ (suc _) = true
--
-- data _×_ (A B : Set) : Set where
--   _,_ : A → B → A × B
--
-- {-
-- -- fails termination check
-- mod : (n : Nat) → (m : Nat) → isTrue (0≠ m) → Nat -- × (isTrue (k ≤ m))
-- mod _    zero ()
-- mod zero m    _ = zero -- , tt
-- mod n    (suc m) _ with (suc m) le n
-- mod n    (suc m) tt | just prf = mod (sub n (suc m) prf) (suc m) tt
-- mod n    (suc m) _  | nothing  = n
-- -}
--
-- -- yay, termination is guaranteed ^_^
-- mod : (n : Nat) → (m : Nat) → isTrue (0≠ m) → Nat -- × (isTrue (k ≤ m))
-- mod _ 0 ()
-- mod n (suc k) prf = go n m
--   where
--     m : Nat
--     m = suc k
--     go : Nat → Nat → Nat
--     go 0       _           = 0
--     -- fails termination check
--     -- go n'       0       = go n' m
--     go (suc n) 0 with (suc n) le m
--     go (suc n) 0 | just _  = suc n
--     go (suc n) 0 | nothing = go n k
--     go (suc n) (suc j) = go n j

Rel : Set -> Set₁
Rel A = A → A → Set

module WellFounded {A : Set} (_⊏_ : Rel A) where
  data Accessible (x : A) : Set where
    acc : ((y : A) → y ⊏ x → Accessible y) → Accessible x

  Well-founded : Set
  Well-founded = (x : A) → Accessible x

open WellFounded

data _<_ (m : Nat) : Nat → Set where
  <-base : m < suc m
  <-step : ∀ {n} → m < n → m < (suc n)

data Ordering (m : Nat) : Nat → Set where
  lt : ∀ {n} → m < n → Ordering m n
  eq :                 Ordering m m
  gt : ∀ {n} → n < m → Ordering m n

relax-< : ∀ {m n} → m < n → suc m < suc n
relax-< <-base       = <-base
relax-< (<-step prf) = <-step (relax-< prf)

constrain-<-left : ∀ {m n} → (suc m) < n → m < n
constrain-<-left <-base       = <-step <-base
constrain-<-left (<-step prf) = <-step (constrain-<-left prf)

relax-<-right : ∀ {m n} → m < n → m < (suc n)
relax-<-right <-base       = <-step <-base
relax-<-right (<-step prf) = <-step (relax-<-right prf)

constrain-< : ∀ {m n} → suc m < suc n → m < n
constrain-< <-base       = <-base
constrain-< (<-step prf) = constrain-<-left prf

<-trans : ∀ {a b c} → a < b → b < c → a < c
<-trans                           <-base           <-base            = <-step <-base
<-trans                           (<-step prf)     <-base            = <-step (<-step prf)
<-trans {a} {.(suc a)} {.(suc n)} <-base           (<-step {n} prf)  = <-step (<-trans <-base prf)
<-trans {a} {.(suc b)} {.(suc c)} (<-step {b} prf) (<-step {c} prf') = <-step (<-trans prf (constrain-<-left prf'))

_cmp_ : (m : Nat) → (n : Nat) → Ordering m n
0      cmp 0 = eq
0      cmp suc n with zero cmp n
0      cmp suc n  | lt prf = lt (<-step prf)
0      cmp suc .0 | eq     = lt <-base
0      cmp suc n  | gt ()
suc m  cmp 0 with m cmp 0
suc m  cmp 0 | lt ()
suc .0 cmp 0 | eq     = gt <-base
suc m  cmp 0 | gt prf = gt (<-step prf)
suc m  cmp suc n with m cmp n
suc m  cmp suc n  | lt prf = lt (relax-< prf)
suc m  cmp suc .m | eq     = eq
suc m  cmp suc n  | gt prf = gt (relax-< prf)

<-wf : Well-founded _<_
<-wf n = acc (aux n)
  where
    aux : (n : Nat) → (m : Nat) → m < n → Accessible _<_ m
    aux .(suc m) m <-base           = <-wf m
    aux (suc .n) m (<-step {n} prf) = aux n m prf

data Σ (A : Set)(B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

syntax Σ T (\v → body) = ∃ v ∈ T , body

data _∧_ (A B : Set) : Set where
  ∧-intro : A → B → A ∧ B

infixr 10 _∧_

_≤_ : (m : Nat) → (n : Nat) → Set
m ≤ n = m < suc n

0≤anything : ∀ n → 0 ≤ n
0≤anything zero    = <-base
0≤anything (suc n) = <-step (0≤anything n)

-- _≡_ is bad choice for gcd, _+_==_ turned out to be better
-- -- +0-id-right : ∀ n → (n + 0) ≡ n
-- +0-id-right : ∀ n → n ≡ (n + 0)
-- +0-id-right zero    = refl
-- +0-id-right (suc n) = cong suc (+0-id-right n)
--
-- +0-id-left : ∀ n → n ≡ (0 + n)
-- +0-id-left zero    = refl
-- +0-id-left (suc n) = cong suc (+0-id-left n)
--
-- ≡-move-+1 : ∀ m → suc (m + 0) ≡ (m + 1)
-- ≡-move-+1 zero    = refl
-- ≡-move-+1 (suc m) = cong suc (≡-move-+1 m)
--
-- ≡-relax-suc : ∀ (n m k : Nat) → n ≡ suc (m + k) → _≡_ {Nat} (suc n) (suc (m + suc k))
-- ≡-relax-suc .(suc 0)               0       0       refl = refl
-- ≡-relax-suc .(suc (suc k))         0       (suc k) refl = refl
-- ≡-relax-suc .(suc (suc m + 0))     (suc m) 0       refl = cong suc (cong suc (≡-move-+1 m))
-- ≡-relax-suc .(suc (suc m + suc k)) (suc m) (suc k) refl = cong suc (≡-relax-suc _ m (suc k) refl)

data _+_==_ : Nat → Nat → Nat → Set where
  +-base : ∀ n                    → 0 + n == n
  +-step : ∀ {m n k} → m + n == k → (suc m) + n == (suc k)

identity-+0 : ∀ n → n + 0 == n
identity-+0 zero    = +-base zero
identity-+0 (suc n) = +-step (identity-+0 n)

+1-right : ∀ {m n k} → m + n == k → m + (suc n) == (suc k)
+1-right {.0}       {n}  {.n}       (+-base .n)              = +-base (suc n)
+1-right {.(suc m)} {.n} {.(suc k)} (+-step {m} {n} {k} prf) = +-step (+1-right prf)

+-comm : ∀ {m n k : Nat} → m + n == k → n + m == k
+-comm {.0}       {0}       {.0}       (+-base .0)               = +-base zero
+-comm {.0}       {(suc n)} {.(suc n)} (+-base .(suc n))         = +-step (identity-+0 n)
+-comm {.(suc m)} {n}       {.(suc k)} (+-step {m} {.n} {k} prf) = +1-right (+-comm prf)

-- Ideally, (m < n) proof should have type (m <= n) as subtraction allows
-- non-strictness here.
-- _-_given_ : (n : Nat) → (m : Nat) → m ≤ n → ∃ k ∈ Nat , (k ≤ n ∧ (k + m) ≡ n)
_-_given_ : (n : Nat) → (m : Nat) → m ≤ n → ∃ k ∈ Nat , (k ≤ n ∧ m + k == n)
0     - .0       given <-base     = 0     , ∧-intro <-base (+-base zero)
zero  - m        given <-step ()
suc n - .(suc n) given <-base     = 0     , ∧-intro (0≤anything (suc n)) (+-comm (+-base (suc n)))
suc n - 0        given <-step prf = suc n , ∧-intro <-base (+-base (suc n))
suc n - suc m    given <-step prf with n - (suc m) given prf
... | k , ∧-intro prf' prf'' = suc k , ∧-intro (relax-< prf') (+1-right prf'')

-- It turns out that this proof is not needed for gcd
data NonZero : Nat → Set where
  nz : ∀ n → NonZero (suc n)

subtraction-lem' : ∀ (n m : Nat) → m < n → (k : Nat) → m + k == n → NonZero k
subtraction-lem' .1       .0       <-base         .1 (+-base .1)              = nz zero
subtraction-lem' .(suc n) .0       (<-step {n} p) ._ (+-base .(suc n))        = nz n
subtraction-lem' .(suc n) .(suc m) p              .k (+-step {m} {k} {n} prf) = subtraction-lem' n m (constrain-< p) k prf

subtraction-lem'' : ∀ (n m k : Nat) → m < n → k + m == n → NonZero k
subtraction-lem'' zero    .0       .0 ()             (+-base .0)
subtraction-lem'' (suc n) .(suc n) .0 (<-step ltprf) (+-base .(suc n)) = subtraction-lem'' n n 0 (constrain-<-left ltprf) (+-base n)
subtraction-lem'' .(suc n) .m .(suc k) ltprf (+-step {k} {m} {n} prf) = nz k

-- 5 - 3 given (<-step (<-step <-base))

{-
-- termination check fails for this as there's no use of Accessible
gcd : (a : Nat) → (b : Nat) → b ≤ a → Nat
gcd 0       0       <-base = 0
gcd 0       (suc _) (<-step ())
gcd a       0       _   = a
gcd a b prf with a - b given prf
gcd a b prf | a' , ∧-intro a'<a _ with a' cmp b
gcd a b prf | a' , ∧-intro a'<a _ | lt a'<b = gcd b a' (<-step a'<b)
gcd a b prf | .b , ∧-intro a'<a _ | eq      = b
gcd a b prf | a' , ∧-intro a'<a _ | gt b<a' = gcd a' b (<-step b<a')
-}

+-transfer : ∀ {a b c : Nat} → a + suc (suc b) == c → suc a + suc b == c
+-transfer {.0}       {b} {.(suc (suc b))} (+-base .(suc (suc b)))               = +-step (+-base (suc b))
+-transfer {.(suc a)} {b} {.(suc c)}       (+-step {a} {.(suc (suc b))} {c} prf) = +-step (+-transfer prf)

+-impossible : ∀ {A : Set}{a b : Nat} → b + suc a == a → A
+-impossible {_} {a}     {0}     ()
+-impossible {_} {0}     {suc b} ()
+-impossible {_} {suc a} {suc b} (+-step prf) = +-impossible (+-transfer prf)

gcd : (a : Nat) → (b : Nat) → b ≤ a → Accessible _<_ a → Accessible _<_ b → Nat
gcd 0  0       <-base      _ _ = 0
gcd 0  (suc _) (<-step ()) _ _
gcd a  0       _           _ _ = a
gcd .b      b       <-base       _       _ = b
gcd (suc a) (suc b) (<-step b≤a) (acc f) (acc g) with (suc a) - (suc b) given (<-step b≤a)
gcd (suc a) (suc b) (<-step b≤a) (acc f) (acc g) | .(suc a) , ∧-intro <-base (+-step r) = +-impossible r -- impossible case
gcd (suc a) (suc b) (<-step b≤a) (acc f) (acc g) | a'       , ∧-intro (<-step a'≤a) _ with a' cmp (suc b)
gcd (suc a) (suc b) (<-step b≤a) (acc f) (acc g) | a'       , ∧-intro (<-step a'≤a) _ | lt a'<b = gcd (suc b) a' (<-step a'<b) (f (suc b) b≤a) (g a' a'<b)
gcd (suc a) (suc b) (<-step b≤a) (acc f) (acc g) | .(suc b) , ∧-intro (<-step a'≤a) _ | eq      = suc b
gcd (suc a) (suc b) (<-step b≤a) (acc f) (acc g) | a'       , ∧-intro (<-step a'≤a) x | gt b<a' = gcd a' (suc b) (<-step b<a') (f a' a'≤a) (f (suc b) b≤a)

gcd' : Nat → Nat → Nat
gcd' a b with a cmp b
gcd' a b  | lt a<b = gcd b a (relax-<-right a<b) (<-wf b) (<-wf a)
gcd' a .a | eq     = a
gcd' a b  | gt b<a = gcd a b (relax-<-right b<a) (<-wf a) (<-wf b)
