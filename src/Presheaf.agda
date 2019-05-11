module Presheaf where

open import Type
open import Util
open import Sel

open import Function using (_∘_)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

record 𝒫 : Set₁ where
  field
    In : Ty → Set 
    lift : ∀ {j i} (s : Sel j i) → (In i → In j)

open 𝒫


-- terminal presheaf
𝟙' : 𝒫
In   𝟙' _   = ⊤
lift 𝟙' _ _ = tt

-- initial presheaf
𝟘' : 𝒫
In   𝟘' _    = ⊥
lift 𝟘' _ ()

-- presheaf product
_×'_ : 𝒫 → 𝒫 → 𝒫
(P ×' Q) .In T = P .In T × Q .In T
(P ×' Q) .lift s = P .lift s ⊗ Q .lift s
  where
  _⊗_ : ∀{A B C D : Set} → (A → C) → (B → D) → (A × B → C × D)
  f ⊗ g = λ x → f (proj₁ x) , g (proj₂ x)

-- presheaf exponential
_⇒'_ : 𝒫 → 𝒫 → 𝒫
(P ⇒' Q) .In T      = ∀ {S} → Sel S T → P .In S → Q .In S
(P ⇒' Q) .lift s f s' = f (s ∙ s')

-- presheaf coproduct
_+'_ : 𝒫 → 𝒫 → 𝒫
(P +' Q) .In T          = P .In T ⊎ Q .In T
(P +' Q) .lift s (inj₁ x) = inj₁ (P .lift s x)
(P +' Q) .lift s (inj₂ y) = inj₂ (Q .lift s y)

-- natural transformation between two presheafs
_→̇_ : (P Q : 𝒫) → Set
_→̇_ P Q = ∀ {i} → (P .In i → Q .In i)

-- naturality law of natural transformations
natural : (P Q : 𝒫) → (P →̇ Q) → Set
natural P Q η = ∀{X Y : Ty} -- objects in OPE
    → (s : Sel X Y)           -- morphism in OPE
    → η {X} ∘ (lift P s) ≡ (lift Q s) ∘ η {Y} -- order of applying η doesn't matter
