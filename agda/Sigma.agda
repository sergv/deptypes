module Sigma where

-- Dependent pair in Agda

data Sigma (A : Set) (P : A -> Set) : Set where
  MkSigma : (x : A) -> (y : P x) -> Sigma A P




 