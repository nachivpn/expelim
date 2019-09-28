------------------------------------------------------------------------
-- Correctness lemmas
------------------------------------------------------------------------

module Lemma where

open import Sel
open import BCC
open import NBE
open import Type


------------------------------------------------------------------------
-- `embSel` is a functor

-- embSel preserves identity

embdId : ∀ {a} → embSel (iden {a}) ≈ id {a}
embdId {𝕓}     = refl
embdId {𝟙}     = refl
embdId {𝟘}     = refl
embdId {a ⇒ b} = refl
embdId {a * b} = trans
  (cong-pair (trans (congr embdId) idl) refl)
  (uniq-pair idr idr)
embdId {a + b} = refl

-- embSel preserves composition

emb-pres-∘ : ∀ {a b c} {x : Sel b a} {y : Sel c b}  →
           embSel (x ∙ y) ≈ embSel x ∘ embSel y
emb-pres-∘ {x = x}      {end𝟙}   = sym idr
emb-pres-∘ {x = x}      {end𝕓}   = sym idr
emb-pres-∘ {x = x}      {end𝟘}   = sym idr
emb-pres-∘ {x = x}      {end⇒}   = sym idr
emb-pres-∘ {x = x}      {end+}   = sym idr
emb-pres-∘ {x = x}      {drop y} = trans (congr emb-pres-∘) (sym assoc)
emb-pres-∘ {x = drop x} {keep y} = sym
  (trans
    (sym assoc)
    (trans
      (congl π₁-pair)
      (trans assoc (congr (sym emb-pres-∘)))))
emb-pres-∘ {x = keep x} {keep y} = sym
  (trans
    comp-pair
    (cong-pair
      (trans
        (sym assoc)
        (trans
          (congl π₁-pair)
          (trans assoc (congr (sym emb-pres-∘)))))
      π₂-pair))

------------------------------------------------------------------------
-- `liftBCC` is a functor

-- liftBCC preserves identity

bcc-pres-id : ∀ {a b} {t : BCC a b} → liftBCC iden t ≈ t
bcc-pres-id {𝕓}     = idr
bcc-pres-id {𝟙}     = idr
bcc-pres-id {𝟘}     = idr
bcc-pres-id {a ⇒ b} = idr
bcc-pres-id {a * b} = trans
  (congl (sym (trans
    η*
    (cong-pair (trans idr (sym (trans (congr embdId) idl))) idr))))
  idr
bcc-pres-id {a + a₁} = idr

-- liftBCC preserves composition

bcc-pres-∘ : ∀ {a b c d} {x : Sel b a} {y : Sel c b} {t : BCC a d} →
  liftBCC (x ∙ y) t ≈ liftBCC y (liftBCC x t)
bcc-pres-∘ {x = x} {y = y} {t = t} = trans (congl emb-pres-∘) assoc

------------------------------------------------------------------------
-- `q` and `qₓ` are natural transformations

mutual

  -- naturality law of quotation of neutral forms

  nat-qNe : ∀{a b c}
      → (τ : Sel c a)
      → (n : Ne a b)
      → liftBCC τ (qNe n) ≈ qNe (liftNe τ n)
  nat-qNe τ (sel x) = sym emb-pres-∘
  nat-qNe τ (fst x) = trans (sym assoc) (congl (nat-qNe τ x))
  nat-qNe τ (snd x) = trans (sym assoc) (congl (nat-qNe τ x))
  nat-qNe τ (app x n) =
    trans
      (sym assoc)
      (congl (trans comp-pair (cong-pair (nat-qNe τ x) (nat-q τ n))))

  -- naturality law of quotation of normal forms

  nat-q : ∀{a b c}
      → (τ : Sel c a)
      → (n : Nf a b)
      → liftBCC τ (q n) ≈ q (liftNf τ n)
  nat-q τ unit          = sym uniq-unit
  nat-q τ (ne-𝕓 x)      = nat-qNe τ x
  nat-q τ (ne-⊥ x)      = trans (sym assoc) (congl (nat-qNe τ x))
  nat-q τ (injl v)      = trans (sym assoc) (congl (nat-q τ v))
  nat-q τ (injr v)      = trans (sym assoc) (congl (nat-q τ v))
  nat-q τ (pair v v₁)   = trans comp-pair (cong-pair (nat-q τ v) (nat-q τ v₁))
  nat-q τ (abs v)       =
    trans
      comp-curry
      (cong-curry (trans (congl (cong-pair refl idl)) (nat-q (keep τ) v)))
  nat-q τ (case x m n) =
    trans
      post-comp-caseM
      (cong-caseM
        (nat-qNe τ x)
        (trans (congl (cong-pair refl idl)) (nat-q (keep τ) m))
        (trans (congl (cong-pair refl idl)) (nat-q (keep τ) n)))
