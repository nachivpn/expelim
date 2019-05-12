module Lemma where

open import Sel
open import BCC
open import NBE
open import Type

-- embToBCC is a functor (map) which maps embeddings to BCC terms
-- it preserves identity
embdId : ∀ {a} → embToBCC (iden {a}) ≈ id {a} 
embdId {𝕓}     = eq-refl
embdId {𝟙}     = eq-refl
embdId {𝟘}     = eq-refl
embdId {a ⇒ b} = eq-refl
embdId {a * b} = eq-trans
  (cong-pair (eq-trans (congr embdId) idl) eq-refl)
  (uniq-pair idr idr)
embdId {a + b} = eq-refl

-- embToBCC preserves composition
emb-pres-∘ : ∀ {a b c} {x : Sel b a} {y : Sel c b}  →
           embToBCC (x ∙ y) ≈ embToBCC x ∘ embToBCC y
emb-pres-∘ {x = x}      {end𝟙}   = eq-sym idr
emb-pres-∘ {x = x}      {end𝕓}   = eq-sym idr
emb-pres-∘ {x = x}      {end𝟘}   = eq-sym idr
emb-pres-∘ {x = x}      {end⇒}   = eq-sym idr
emb-pres-∘ {x = x}      {end+}   = eq-sym idr
emb-pres-∘ {x = x}      {drop y} = eq-trans (congr emb-pres-∘) (eq-sym assoc)
emb-pres-∘ {x = drop x} {keep y} = eq-sym
  (eq-trans
    (eq-sym assoc)
    (eq-trans
      (congl π₁-pair)
      (eq-trans assoc (congr (eq-sym emb-pres-∘)))))
emb-pres-∘ {x = keep x} {keep y} = eq-sym
  (eq-trans
    comp-pair
    (cong-pair
      (eq-trans
        (eq-sym assoc)
        (eq-trans
          (congl π₁-pair)
          (eq-trans assoc (congr (eq-sym emb-pres-∘)))))
      π₂-pair))

-- Recall that wkBCC is the fmap of the BCC presheaf
-- wkBCC preserves identity in OPE as identity function
bcc-pres-id : ∀ {a b} {t : BCC a b} → liftBCC iden t ≈ t
bcc-pres-id {𝕓}     = idr
bcc-pres-id {𝟙}     = idr
bcc-pres-id {𝟘}     = idr
bcc-pres-id {a ⇒ b} = idr
bcc-pres-id {a * b} = eq-trans
  (congl (eq-sym (eq-trans
    η*
    (cong-pair (eq-trans idr (eq-sym (eq-trans (congr embdId) idl))) idr))))
  idr
bcc-pres-id {a + a₁} = idr

-- wkBCC preserves composition in OPE to function composition
bcc-pres-∘ : ∀ {a b c d} {x : Sel b a} {y : Sel c b} {t : BCC a d} →
  liftBCC (x ∙ y) t ≈ liftBCC y (liftBCC x t)
bcc-pres-∘ {x = x} {y = y} {t = t} = eq-trans (congl emb-pres-∘) assoc

-- naturality law of quotations
mutual

  nat-qₓ : ∀{a b c}  
      → (τ : Sel c a)
      → (n : Ne a b)
      → liftBCC τ (qₓ n) ≈ qₓ (liftNe τ n)
  nat-qₓ τ (sel x) = eq-sym bcc-pres-∘
  nat-qₓ τ (fst x) = eq-trans (eq-sym assoc) (congl (nat-qₓ τ x))
  nat-qₓ τ (snd x) = eq-trans (eq-sym assoc) (congl (nat-qₓ τ x))
  nat-qₓ τ (app x n) =
    eq-trans
      (eq-sym assoc)
      (congl (eq-trans comp-pair (cong-pair (nat-qₓ τ x) (nat-q τ n))))

  -- naturality law of quotation of normal forms
  nat-q : ∀{a b c}  
      → (τ : Sel c a)
      → (n : Nf a b)
      → liftBCC τ (q n) ≈ q (liftNf τ n)
  nat-q τ unit          = eq-sym uniq-unit
  nat-q τ (ne-𝕓 x)      = nat-qₓ τ x
  nat-q τ (ne-⊥ x)      = eq-trans (eq-sym assoc) (congl (nat-qₓ τ x))
  nat-q τ (injl v)      = eq-trans (eq-sym assoc) (congl (nat-q τ v))
  nat-q τ (injr v)      = eq-trans (eq-sym assoc) (congl (nat-q τ v))
  nat-q τ (pair v v₁)   = eq-trans comp-pair (cong-pair (nat-q τ v) (nat-q τ v₁))
  nat-q τ (abs v)       =
    eq-trans
      comp-curry
      (cong-curry (eq-trans (congl (cong-pair eq-refl idl)) (nat-q (keep τ) v)))
  nat-q τ (case x m n) =
    eq-trans
      post-comp-caseM
      (cong-caseM
        (nat-qₓ τ x)
        (eq-trans (congl (cong-pair eq-refl idl)) (nat-q (keep τ) m))
        (eq-trans (congl (cong-pair eq-refl idl)) (nat-q (keep τ) n)))

-- also provable by uniq-iden
keepIdenIsIden : ∀{a b c} {f : BCC (a * b) c} → f ≈ f ∘ liftBCC (keep iden) id
keepIdenIsIden = eq-sym
  (eq-trans
    assoc
    (eq-trans (cong-∘ idr (eq-trans (cong-pair (eq-trans (congr embdId) idl) eq-refl)
      (eq-trans (cong-pair (eq-sym idr) (eq-sym idr)) (eq-sym η*)))) idr))
