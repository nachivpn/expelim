
module Main where


open import Util
open import Data.Product
  using (∃)
open import Type
  using (Ty)
open import BCC
  using (BCC ; distrf ; _≈_ ; cong-pair ; cong-∘ ; cong-match ; ≡→≈)
open import DBC
  using (DBC ; qD ; qNeD ; neutralSafe ; embSelD)
open import Sel
  using (Sel ; embSel)
open import NBE
  using (Nf ; Ne ; q ; qNe ; liftBCC ; norm)
open import Correct
  using (correctNorm)

open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (refl to ≡-refl ; sym to ≡-sym ; cong to ≡-cong ; cong₂ to ≡-cong₂ ; trans to ≡-trans)

open BCC.BCC
open DBC.DBC
open Sel.Sel
open Nf
open Ne
open _≈_

-- embed DBC terms into BCC terms
embD : {a b : Ty} →  DBC a b → BCC a b
embD id = id
embD (t ∘ u) = embD t ∘ embD u
embD π₁ = π₁
embD π₂ = π₂
embD < t , u > = < embD t , embD u >
embD init = init
embD unit = unit
embD injl = injl
embD injr = injr
embD [ t , u ] = [ embD t , embD u ]
embD distr = distrf

-- equivalence between BCC and DBC terms
_≋_ : {a b : Ty} → BCC a b → DBC a b → Set
_≋_ t u = t ≈ embD u

-- embedding a selection to BCC is equivalent to embedding it via DBC
-- or, equivalently, the following diagram commutes
--
--            Sel
--          .     .
-- (embSel) .  ↻   . (embSelD)
--          .        .
--          🡓         🡖
--         BCC 🡐 ∙ ∙ ∙ DBC
--              (embD)
--
embSel≣embSelD : {a b : Ty}
  → (s : Sel a b) → embSel s ≡ embD (embSelD s)
embSel≣embSelD end𝟙 = ≡-refl
embSel≣embSelD end𝕓 = ≡-refl
embSel≣embSelD end𝟘 = ≡-refl
embSel≣embSelD end⇒ = ≡-refl
embSel≣embSelD end+ = ≡-refl
embSel≣embSelD (drop s) = ≡-cong (_∘ π₁) (embSel≣embSelD s)
embSel≣embSelD (keep s) = ≡-cong (λ f → < (f ∘ π₁) , π₂ >) (embSel≣embSelD s)


-- quoting a neutral to BCC is equivalent to (the embedding of) quoting it to DBCC
-- or, equivalently, the following diagram commutes
--
--         Ne
--       .     .
-- (qNe) .  ↻   . (qNeD)
--       .        .
--       🡓         🡖
--     BCC 🡐 ∙ ∙ ∙ DBC
--          (embD)
--
qNe≣qNeD : {a b : Ty} → (p : firstOrd a)
  → (n : Ne a b) → qNe n ≡ embD (qNeD p n)
qNe≣qNeD p (sel s) = embSel≣embSelD s
qNe≣qNeD p (fst n) = ≡-cong (π₁ ∘_) (qNe≣qNeD p n)
qNe≣qNeD p (snd n) = ≡-cong (π₂ ∘_) (qNe≣qNeD p n)
qNe≣qNeD p (app n x) with neutralSafe p n
qNe≣qNeD p (app n x) | ()

-- quoting a neutral to DBC is equivalent to (the embedding of) quoting it to BCC
-- or, equivalently, the following diagram commutes
--
--         Nf
--       .     .
--   (q) .  ↻   . (qD)
--       .        .
--       🡓         🡖
--     BCC 🡐 ∙ ∙ ∙ DBC
--          (embD)
--
q≣qD : {a b : Ty} → (pa : firstOrd a) (pb : firstOrd b)
  → (n : Nf a b) → q n ≡ embD (qD pa pb n)
q≣qD pa pb unit         = ≡-refl
q≣qD pa pb (ne-𝕓 x)     = qNe≣qNeD pa x
q≣qD pa pb (ne-⊥ x)     = ≡-cong (init ∘_) (qNe≣qNeD pa x)
q≣qD pa pb (injl n)     = ≡-cong (injl ∘_) (q≣qD pa (proj₁ pb) n)
q≣qD pa pb (injr n)     = ≡-cong (injr ∘_) (q≣qD pa (proj₂ pb) n)
q≣qD pa pb (pair m n)   = ≡-cong₂ <_,_> (q≣qD pa (proj₁ pb) m) (q≣qD pa (proj₂ pb) n)
q≣qD pa pb (case s m n) = ≡-cong₂ _∘_
  (≡-cong₂ _∘_
    (≡-cong₂ [_,_]
      (q≣qD (pa , proj₁ (neutralSafe pa s)) pb m)
      (q≣qD (pa , proj₂ (neutralSafe pa s)) pb n))
    ≡-refl)
  (≡-cong₂ <_,_> ≡-refl (qNe≣qNeD pa s))

-----------------
-- Main theorem
-----------------

-- Exponential Elimination theorem (statement):
-- For every BCC term between first order types,
-- there exists an equivalent DBC term---which
-- does not contain exponentials by construction.

ExpElimThm : Set
ExpElimThm = {a b : Ty}
  → firstOrd a → firstOrd b
  → ∀ (t : BCC a b) → ∃ (λ t' → t ≋ t')

-- Exponential Elimination theorem (proof)
main : ExpElimThm
main pa pb t = let n = (norm t) ; t' = (qD pa pb n)
  in t' , trans (correctNorm t) (≡→≈ (q≣qD pa pb n))

-- ∎

-- utlity over main

expElim-pres-≈ : {a b : Ty}
  → {fa : firstOrd a} → {fb : firstOrd b}
  → (t : BCC a b)
  → t ≋ qD fa fb (norm t)
expElim-pres-≈ t = proj₂ (main _ _ t)
