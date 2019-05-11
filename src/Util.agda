module Util where

open import Type
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂) public

base : Ty → Set
base 𝕓 = ⊤
base _ = ⊥

notFun : Ty → Set
notFun 𝟘       = ⊤
notFun 𝟙       = ⊤
notFun 𝕓       = ⊤
notFun (_ ⇒ _) = ⊥
notFun (a * b) = notFun a × notFun b
notFun (a + b) = notFun a × notFun b

-- allows "uncurried" functions
-- i.e,, input and output of function are not functions
-- strict subformulas (?) must not be functions
notFun' : Ty → Set
notFun' 𝟘       = ⊤
notFun' 𝟙       = ⊤
notFun' 𝕓       = ⊤
notFun' (a ⇒ b) = notFun a × notFun b
notFun' (a * b) = notFun' a × notFun' b
notFun' (a + b) = notFun' a × notFun' b

  
