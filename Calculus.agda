module Calculus where

data _≡_ {A : Set} (x : A) : A → Set where
  refl≡ : x ≡ x

infixr 30 _≡_

symm≡ : {A : Set} {x y : A} → x ≡ y -> y ≡ x
symm≡ refl≡ = refl≡

cong≡ : (A → B)

--apply≡ : {A : Set} → (x : A) ⇛ x ≡ y → y
--apply≡ = {!test!}

infixr 50 _+_
infixr 70 _×_

Bool : Set₁
Bool = Set

data True : Set where
  true : True

postulate
  ℝ    : Set

  _+_  : ℝ → ℝ → ℝ
  +-id : ℝ
  -_   : ℝ → ℝ

  _×_  : ℝ → ℝ → ℝ
  ×-id : ℝ
  _⁻¹  : ℝ → ℝ

  +-assoc : {x y z : ℝ} → (x + y) + z ≡ x + (y + z)
  +-ident : {x     : ℝ} → x + +-id ≡ x
  +-comm  : {x y   : ℝ} → x + y ≡ y + x

  ×-assoc : {x y z : ℝ} → (x + y) + z ≡ x + (y + z)
  ×-comm  : {x y   : ℝ} → x + y ≡ y + x
  ×-ident : {x     : ℝ} → x × ×-id ≡ x

  ×-dist  : {x y z : ℝ} → x × (y + z) ≡ x × y + x × z
  
  ℙ       : Set
  _∈ℙ     : ℝ → Bool
  +ℙ      : {x y   : ℝ} → x ∈ℙ → y ∈ℙ → (x + y) ∈ℙ
  ×ℙ      : {x y   : ℝ} → x ∈ℙ → y ∈ℙ → (x × y) ∈ℙ

×-by-neg : {x y : ℝ} → ((- x) × y) ≡ (- (x × y))
×-by-neg = {!proof!}
