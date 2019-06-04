module Lemma where

open import Sel
open import BCC
open import NBE
open import Type

-- embToBCC is a functor (map) which maps embeddings to BCC terms
-- it preserves identity
embdId : ∀ {a} → embToBCC (iden {a}) ≈ id {a} 
embdId {𝕓}     = refl
embdId {𝟙}     = refl
embdId {𝟘}     = refl
embdId {a ⇒ b} = refl
embdId {a * b} = trans
  (cong-pair (trans (congr embdId) idl) refl)
  (uniq-pair idr idr)
embdId {a + b} = refl

-- embToBCC preserves composition
emb-pres-∘ : ∀ {a b c} {x : Sel b a} {y : Sel c b}  →
           embToBCC (x ∙ y) ≈ embToBCC x ∘ embToBCC y
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

-- Recall that wkBCC is the fmap of the BCC presheaf
-- wkBCC preserves identity in OPE as identity function
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

-- wkBCC preserves composition in OPE to function composition
bcc-pres-∘ : ∀ {a b c d} {x : Sel b a} {y : Sel c b} {t : BCC a d} →
  liftBCC (x ∙ y) t ≈ liftBCC y (liftBCC x t)
bcc-pres-∘ {x = x} {y = y} {t = t} = trans (congl emb-pres-∘) assoc

-- naturality law of quotations
mutual

  nat-qₓ : ∀{a b c}  
      → (τ : Sel c a)
      → (n : Ne a b)
      → liftBCC τ (qₓ n) ≈ qₓ (liftNe τ n)
  nat-qₓ τ (sel x) = sym bcc-pres-∘
  nat-qₓ τ (fst x) = trans (sym assoc) (congl (nat-qₓ τ x))
  nat-qₓ τ (snd x) = trans (sym assoc) (congl (nat-qₓ τ x))
  nat-qₓ τ (app x n) =
    trans
      (sym assoc)
      (congl (trans comp-pair (cong-pair (nat-qₓ τ x) (nat-q τ n))))

  -- naturality law of quotation of normal forms
  nat-q : ∀{a b c}  
      → (τ : Sel c a)
      → (n : Nf a b)
      → liftBCC τ (q n) ≈ q (liftNf τ n)
  nat-q τ unit          = sym uniq-unit
  nat-q τ (ne-𝕓 x)      = nat-qₓ τ x
  nat-q τ (ne-⊥ x)      = trans (sym assoc) (congl (nat-qₓ τ x))
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
        (nat-qₓ τ x)
        (trans (congl (cong-pair refl idl)) (nat-q (keep τ) m))
        (trans (congl (cong-pair refl idl)) (nat-q (keep τ) n)))

-- also provable by uniq-iden
keepIdenIsIden : ∀{a b c} {f : BCC (a * b) c} → f ≈ f ∘ liftBCC (keep iden) id
keepIdenIsIden = sym
  (trans
    assoc
    (trans (cong-∘ idr (trans (cong-pair (trans (congr embdId) idl) refl)
      (trans (cong-pair (sym idr) (sym idr)) (sym η*)))) idr))
