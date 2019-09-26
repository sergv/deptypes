
module Compilers where

open import Tablet

data Var : Set where
  var : Nat → Var

data Configuration : Set where
  []     : Configuration
  _:=_∈_ : Var → Nat → Configuration → Configuration

data Expr (V : Set) : Set where
  lit   : Nat → Expr V
  var   : V → Expr V
  _add_ : Expr V → Expr V → Expr V
  _mul_ : Expr V → Expr V → Expr V
  ≡0    : Expr V → Expr V
  _==_  : Expr V → Expr V → Expr V
  _<<<_ : Expr V → Expr V → Expr V
  _||_  : Expr V → Expr V → Expr V
  _&&_  : Expr V → Expr V → Expr V

RawExpr : Set
RawExpr = Expr Var

data Statement : Set where
  skip          : Statement
  _seq_         : Statement → Statement → Statement
  _:=_          : Var → Nat → Statement
  if_then_else_ : Statement → Statement → Statement → Statement

--eval :

data Big-step : Statement → Configuration → Configuration → Set where
  sem-skip : ∀ {C} → Big-step skip C C
  sem-seq  : ∀ {C C' C'' s s'}  →
             Big-step s  C  C'  →
             Big-step s' C' C'' →
             Big-step (s seq s') C C''
  sem-:=   : ∀ {v x C} →
             Big-step (v := x) C (v := x ∈ C)

seq-assoc : ∀ {C C' s s' s''}                  →
            Big-step (s seq (s' seq s'')) C C' →
            Big-step ((s seq s') seq s'') C C'
seq-assoc (sem-seq sem (sem-seq sem' sem'')) = sem-seq (sem-seq sem sem') sem''




{-

_==-sem_ : {C : Configuration} →
           {s s' : Semantics} →
           {f g : Configuration → Configuration} →
           Big-step-semantics s f →
           Big-step-semantics s' g →
           Maybe (f C == g C)
sem-skip ==-sem sem-skip = just refl
sem-skip ==-sem _ = nothing
_ ==-sem sem-skip

-}
