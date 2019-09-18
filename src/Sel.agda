module Sel where

open import Type
open import Util
open import BCC

--  Selections are the combinator-equivalent of variables
-- `Sel i j` to be read as a selection of j from i (or j ⊑ i)

data Sel : Ty → Ty → Set where
  end𝟙  : Sel 𝟙 𝟙
  end𝕓  : Sel 𝕓 𝕓
  end𝟘  : Sel 𝟘 𝟘
  end⇒  : ∀ {a b}   → Sel (a ⇒ b) (a ⇒ b)
  end+  : ∀ {a b}   → Sel (a + b) (a + b)
  drop  : ∀ {a b c} → Sel a b → Sel (a * c) b
  keep  : ∀ {a b c} → Sel a b → Sel (a * c) (b * c)

-- the identity selection for each type
iden : ∀ {a} → Sel a a
iden {𝕓}      = end𝕓
iden {𝟙}      = end𝟙
iden {𝟘}      = end𝟘
iden {a ⇒ a₁} = end⇒
iden {a * a₁} = keep iden
iden {a + a₁} = end+

-- selections compose
_∙_ : ∀ {a b c} → Sel b c → Sel a b → Sel a c
f      ∙ end𝟙   = f
f      ∙ end𝕓   = f
f      ∙ end𝟘   = f
f      ∙ end⇒   = f
f      ∙ end+   = f
f      ∙ drop g = drop (f ∙ g)
drop f ∙ keep g = drop (f ∙ g)
keep f ∙ keep g = keep (f ∙ g)

-- selections can be embedded into terms
embSel : ∀ {a b} → Sel a b → BCC a b
embSel end𝟙     = id
embSel end𝕓     = id
embSel end𝟘     = id
embSel end⇒     = id
embSel end+     = id
embSel (drop e) = embSel e ∘ π₁
embSel (keep e) = < embSel e ∘ π₁ , π₂ >

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong)

-- Category of Selections

private

  ⊑-idl : ∀ {a b} {s : Sel a b} → iden ∙ s ≡ s
  ⊑-idl {s = end𝟙}   = refl
  ⊑-idl {s = end𝕓}   = refl
  ⊑-idl {s = end𝟘}   = refl
  ⊑-idl {s = end⇒}   = refl
  ⊑-idl {s = end+}   = refl
  ⊑-idl {s = drop s} = cong drop ⊑-idl
  ⊑-idl {s = keep s} = cong keep ⊑-idl

  ⊑-idr : ∀ {a b} {s : Sel a b} → s ∙ iden ≡ s
  ⊑-idr {s = end𝟙}   = refl
  ⊑-idr {s = end𝕓}   = refl
  ⊑-idr {s = end𝟘}   = refl
  ⊑-idr {s = end⇒}   = refl
  ⊑-idr {s = end+}   = refl
  ⊑-idr {s = drop s} = cong drop ⊑-idr
  ⊑-idr {s = keep s} = cong keep ⊑-idr

  ⊑-assoc :  ∀ {a b c d} {x : Sel c d} {y : Sel b c} {z : Sel a b}
    → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
  ⊑-assoc {x = x}      {y}      {end𝟙}  = refl
  ⊑-assoc {x = x}      {y}      {end𝕓}  = refl
  ⊑-assoc {x = x}      {y}      {end𝟘}  = refl
  ⊑-assoc {x = x}      {y}      {end⇒}  = refl
  ⊑-assoc {x = x}      {y}      {end+}  = refl
  ⊑-assoc {x = x}      {y}      {drop z} = cong drop (⊑-assoc {z = z})
  ⊑-assoc {x = x}      {drop y} {keep z} = cong drop (⊑-assoc {z = z})
  ⊑-assoc {x = drop x} {keep y} {keep z} = cong drop (⊑-assoc {z = z})
  ⊑-assoc {x = keep x} {keep y} {keep z} = cong keep (⊑-assoc {z = z})

-- identity is unique

uniq-iden : ∀ {a b} → keep iden ≡ iden {a * b}
uniq-iden = refl
