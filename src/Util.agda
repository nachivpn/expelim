module Util where

open import Type
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂) public
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

base : Ty → Set
base 𝕓 = ⊤
base _ = ⊥

firstOrd : Ty → Set
firstOrd 𝟘       = ⊤
firstOrd 𝟙       = ⊤
firstOrd 𝕓       = ⊤
firstOrd (_ ⇒ _) = ⊥
firstOrd (a * b) = firstOrd a × firstOrd b
firstOrd (a + b) = firstOrd a × firstOrd b

-- allows "uncurried" functions
-- i.e,, input and output of function are not functions
-- strict subformulas (?) must not be functions
firstOrd' : Ty → Set
firstOrd' 𝟘       = ⊤
firstOrd' 𝟙       = ⊤
firstOrd' 𝕓       = ⊤
firstOrd' (a ⇒ b) = firstOrd a × firstOrd b
firstOrd' (a * b) = firstOrd' a × firstOrd' b
firstOrd' (a + b) = firstOrd' a × firstOrd' b

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y u v p q}
  → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl
