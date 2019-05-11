module Type where

-- Types in the internal language

infixr 5 _⇒_

data Ty : Set where
  𝕓    : Ty
  𝟙    : Ty
  𝟘    : Ty
  _⇒_  : (a b : Ty) → Ty  
  _*_  : (a b : Ty) → Ty
  _+_  : (a b : Ty) → Ty
