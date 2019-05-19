{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --allow-unsolved-metas #-}

module BCC where

open import Type
open import Util

infixr 4 _∘_
infixr 3 <_,_>

data BCC : (a b : Ty) → Set where

  -- Category morphisms
  id    : ∀ {a}     → BCC a a
  _∘_   : ∀ {a b c} → BCC b c → BCC a b → BCC a c

  -- Product morphisms
  π₁    : ∀ {a b}   → BCC (a * b) a
  π₂    : ∀ {a b}   → BCC (a * b) b
  <_,_> : ∀ {a b c} → BCC a b → BCC a c → BCC a (b * c)

  -- Initial morphism
  init  : ∀ {a}     → BCC 𝟘 a

  -- Terminal morphism
  unit  : ∀ {a}     → BCC a 𝟙

  -- co-product morphisms
  injl  : ∀ {a b}     → BCC a (a + b)
  injr  : ∀ {a b}     → BCC b (a + b)
  [_,_] : ∀ {a b c} → BCC a c → BCC b c → BCC (a + b) c

  -- Exponential morphisms
  curry : ∀ {a b c} → BCC (c * a) b → BCC c (a ⇒ b)
  apply : ∀ {a b}  → BCC ((a ⇒ b) * a) b


_⊗_ : ∀{a b c d} → BCC a b → BCC c d → BCC (a * c) (b * d)
f ⊗ g = < (f ∘ π₁) , (g ∘ π₂) >

uncurry : ∀{c a b} → BCC c (a ⇒ b) → BCC (c * a) b
uncurry f = apply ∘ (f ⊗ id)

η↑-exp : ∀ {A B C} → BCC A (B ⇒ C) → BCC A (B ⇒ C)
η↑-exp f = curry (uncurry f)

distrf : ∀ {a b c} → BCC (a * (b + c)) ((a * b) + (a * c))
distrf = apply ∘
    < [ curry (injl ∘ < π₂ , π₁ >)
    , curry (injr ∘ < π₂ , π₁ >) ] ∘ π₂
    , π₁ >

distrb : ∀ {a b c} → BCC ((a * b) + (a * c)) (a * (b + c))
distrb = [ < π₁ , injl ∘ π₂ > , < π₁ , injr ∘ π₂ > ]

copair : ∀ {a b c d} → BCC (a * b) d -> BCC (a * c) d -> BCC (a * (b + c)) d
copair f g = [ f , g ] ∘ distrf

caseM : ∀ {a b c d} → BCC a (b + c) → BCC (a * b) d -> BCC (a * c) d -> BCC a d
caseM x f g = copair f g ∘ < id , x >

infix 2 _≈_

data _≈_ : ∀ {a b} → (f g : BCC a b) → Set where
  idr  : ∀ {a b} {f : BCC a b}
    → (f ∘ id) ≈ f
  idl  : ∀ {a b} {f : BCC a b}
    → (id ∘ f) ≈ f
  assoc : ∀ {a b c d} {h : BCC a b} {g : BCC b c} {f : BCC c d}
    → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h    
  π₁-pair : ∀{a b c} {f : BCC c a} {g : BCC c b}
    → (π₁ ∘ < f , g >) ≈ f
  π₂-pair : ∀{a b c} {f : BCC c a} {g : BCC c b}
    → (π₂ ∘ < f , g >) ≈ g
  match-injl : ∀{a b c} {f : BCC a c} {g : BCC b c}
    → ([ f , g ] ∘ injl) ≈ f
  match-injr : ∀{a b c} {f : BCC a c} {g : BCC b c}
    → ([ f , g ] ∘ injr) ≈ g
  apply-curry : ∀ {a b c} {f : BCC (a * b) c}
    → (apply ∘ (curry f ⊗ id)) ≈ f
  uniq-init : ∀ {a} {f : BCC 𝟘 a}
    → init ≈ f
  uniq-unit : ∀ {a} {f : BCC a 𝟙}
    → unit ≈ f
  uniq-pair  : ∀ {a b z f g} {h : BCC z (a * b)}
    → (π₁ ∘ h) ≈ f
    → (π₂ ∘ h) ≈ g
    → < f , g > ≈ h
  uniq-curry : ∀ {a b c} {h : BCC a (b ⇒ c)} {f : BCC (a * b) c}
    → apply ∘ (h ⊗ id) ≈ f
    → curry f ≈ h
  uniq-match : ∀ {a b z f g} {h : BCC (a + b) z}
    → (h ∘ injl) ≈ f
    → (h ∘ injr) ≈ g
    → [ f , g ] ≈ h
  eq-refl  : ∀ {a b} {f : BCC a b}
    → f ≈ f
  eq-sym   : ∀ {a b} {f g : BCC a b}
    → f ≈ g → g ≈ f
  eq-trans : ∀ {a b} {f g h : BCC a b}
    → f ≈ g → g ≈ h → f ≈ h
  congl : ∀ {a b c} {x y : BCC a b} {f : BCC b c}
    → x ≈ y → f ∘ x ≈ f ∘ y
  congr : ∀ {a b c} {x y : BCC b c} {f : BCC a b}
    → x ≈ y → x ∘ f ≈ y ∘ f

-- distributivity laws hold in any BCC (and can be derived in _≈_)
postulate
  distrfnb : ∀{a b c} → distrb ∘ distrf ≈ id {a * (b + c)}
  --distrbnf : ∀{a b c} → distrf ∘ distrb ≈ id {(a * b) + (a * c)}

open import Relation.Binary using (Setoid; IsEquivalence) 
open Setoid renaming (_≈_ to _≈ₑ_)
open IsEquivalence

Hom : (a b : Ty) → Setoid _ _
Hom a b .Carrier = BCC a b
Hom a b ._≈ₑ_     = _≈_
Hom a b .isEquivalence .refl  = eq-refl
Hom a b .isEquivalence .sym   = eq-sym
Hom a b .isEquivalence .trans = eq-trans


import Relation.Binary.SetoidReasoning as SetoidR
open SetoidR


-- standard pair rules

comp-pair : ∀{a b c d} {h : BCC d c} {f : BCC c a} {g : BCC c b}
  → < f , g > ∘ h ≈ < (f ∘ h) , (g ∘ h) >
comp-pair = eq-sym
  (uniq-pair
    (eq-trans assoc (congr π₁-pair))
    (eq-trans assoc (congr π₂-pair)))

cong-pair : ∀{a b d} → {f f' : BCC a b} {g g' : BCC a d}
  → f ≈ f' → g ≈ g' → < f , g > ≈ < f' , g' >
cong-pair p q = uniq-pair
  (eq-trans π₁-pair (eq-sym p))
  (eq-trans π₂-pair (eq-sym q))

-- standard ∘ rules

cong-∘ : ∀{a b c} → {f f' : BCC a b} {g g' : BCC c a}
  → f ≈ f' → g ≈ g' → f ∘ g ≈ f' ∘ g'
cong-∘ p q = eq-trans (congr p) (congl q)

-- standard ⊗ rules

cong-⊗ : ∀{a b c d} → {f f' : BCC a b} {g g' : BCC c d}
  → f ≈ f' → g ≈ g' → f ⊗ g ≈ f' ⊗ g'
cong-⊗ p q = uniq-pair
  (eq-trans π₁-pair (eq-sym (congr p)))
  (eq-trans π₂-pair (eq-sym (congr q)))

comp-⊗ : ∀{a b c d} {h : BCC d c} {f : BCC c b}
  → (f ∘ h) ⊗ id {a} ≈ (f ⊗ id) ∘ (h ⊗ id)
comp-⊗ = eq-sym
  (eq-trans
    comp-pair
    (cong-pair
      (eq-trans
        (eq-sym assoc) (eq-trans (congl π₁-pair) assoc))
        (eq-trans (eq-sym assoc) (congl (eq-trans π₂-pair idl)))))

-- standard curry rules

cong-curry : ∀{a b c} → {f f' : BCC (a * b) c}
  → f ≈ f' → curry f ≈ curry f'
cong-curry p = uniq-curry (eq-trans apply-curry (eq-sym p))

comp-curry : ∀{a b c d} {h : BCC d c} {f : BCC (c * a) b}
  → curry f ∘ h ≈ curry (f ∘ (h ⊗ id))
comp-curry = eq-sym (uniq-curry
  (eq-trans
    (congl comp-⊗)
    (eq-trans assoc (congr apply-curry))))

-- standard match rules

cong-match : ∀ {a b c} {f f' : BCC a c} {g g' : BCC b c}
  → f ≈ f'
  → g ≈ g'
  → ([ f , g ]) ≈ ([ f' , g' ])
cong-match p q = uniq-match
  (eq-trans match-injl (eq-sym p))
  (eq-trans match-injr (eq-sym q))  

comp-match : ∀ {a b c d} {h : BCC c d} {f  : BCC a c} {g : BCC b c}
  → h ∘ [ f , g ] ≈ [ h ∘ f , h ∘ g ]
comp-match = eq-sym (uniq-match
  (eq-trans (eq-sym assoc) (congl match-injl))
  ((eq-trans (eq-sym assoc) (congl match-injr))))

-- beta reduction

β⇒  : ∀ {a b c} (f : BCC (c * a) b) (g : BCC c a)
  → apply ∘ < (curry f) , g > ≈ (f ∘ < id , g >)
β⇒ f g = eq-trans
  (eq-trans
    (congl
      (eq-sym (eq-trans
        comp-pair
        (cong-pair
          (eq-trans (eq-sym assoc) (eq-trans (congl π₁-pair) idr))
          (eq-trans (eq-sym assoc) (eq-trans idl π₂-pair))))))
    assoc)
  (congr apply-curry)

-- copair laws (useful intermediate step to prove special rules about case)

copair-injl : ∀{a b c d} {f : BCC (a * b) d} {g : BCC (a * c) d}
    → copair f g ∘ (id ⊗ injl) ≈  f
copair-injl = {!!} --doable

copair-injr : ∀{a b c d} {f : BCC (a * b) d} {g : BCC (a * c) d}
    → copair f g ∘ (id ⊗ injr) ≈ g
copair-injr = {!!} --doable

uniq-copair : ∀ {a b c d} {f : BCC (a * b) d} {g : BCC (a * c) d} {h : BCC (a * (b + c)) d}
    → f ≈ h ∘ (id ⊗ injl)
    → g ≈ h ∘ (id ⊗ injr)
    → copair f g ≈ h
uniq-copair p q = eq-trans
  (congr (eq-trans (cong-match p q) (eq-sym comp-match)))
  (eq-trans
    (eq-sym assoc)
    (eq-trans
      (congl (eq-trans
        (congr (cong-match (cong-pair idl eq-refl) (cong-pair idl eq-refl)))
        distrfnb))
      idr))

-- standard copair rules

cong-copair : ∀ {a b c d} {f f' : BCC (a * b) d} {g g' : BCC (a * c) d}
  → f ≈ f'
  → g ≈ g'
  → copair f g ≈ copair f' g'
cong-copair p q = uniq-copair
  (eq-trans p (eq-sym copair-injl))
  (eq-trans q (eq-sym copair-injr))  

comp-copair : ∀ {a b c d e} {f : BCC (a * b) d} {g : BCC (a * c) d} {h : BCC d e}
  → h ∘ copair f g ≈ copair (h ∘ f) (h ∘ g)
comp-copair = eq-sym (uniq-copair
  (eq-sym (eq-trans (eq-sym assoc) (congl copair-injl)))
  (eq-sym (eq-trans (eq-sym assoc) (congl copair-injr))))

-- standard case rules

cong-caseM : ∀ {a b c d}
  {x x' :  BCC a (b + c)} {f f' : BCC (a * b) d} {g g' : BCC (a * c) d}
  → x ≈ x'
  → f ≈ f'
  → g ≈ g'
  → caseM x f g ≈ caseM x' f' g'
cong-caseM p q r = cong-∘ (cong-copair q r) (cong-pair eq-refl p)

comp-caseM : ∀ {a b c d e} {h : BCC d e}
  {x :  BCC a (b + c)} {f  : BCC (a * b) d} {g : BCC (a * c) d}
  → h ∘ (caseM x f g) ≈ caseM x (h ∘ f) (h ∘ g)
comp-caseM = eq-trans assoc (congr comp-copair)

-- eta rules

η⇒ : ∀{a b c} → {f : BCC a (b ⇒ c)}
  → f ≈ curry (uncurry f)
η⇒ = eq-sym (uniq-curry eq-refl)

η* : ∀{a b c} → {f : BCC a (b * c)}
  → f ≈ < π₁ ∘ f , π₂ ∘ f >
η* = eq-sym (uniq-pair eq-refl eq-refl)

η+ : ∀{a b c} → {f : BCC a (b + c)}
  → f ≈ caseM f (injl ∘ π₂) (injr ∘ π₂)
η+ = eq-sym
  (eq-trans
    (congr
      (uniq-copair
        (eq-sym π₂-pair)
        (eq-sym π₂-pair)))
    π₂-pair)

-- special case rules

post-comp-caseM : ∀ {a b c d e} {h : BCC e a}
  {x :  BCC a (b + c)} {f  : BCC (a * b) d} {g : BCC (a * c) d}
  → (caseM x f g) ∘ h ≈ caseM (x ∘ h) (f ∘ h ⊗ id {b}) (g ∘ h ⊗ id)
post-comp-caseM {h = h} {x} = {!!}
-- KEY step:
-- < id , x > ∘ h 
-- == < h , x ∘ h >
-- == < h ∘ π₁ , π₂ >  ∘ < id , x ∘ h >
-- (by comp-pair {h = < id , x ∘ h >}  {f = h ∘ π₁} {g = π₂})


apply-case : ∀{a b c d e}
  {x : BCC a (b + c)} {y : BCC a d}
  {f : BCC (a * b) (d ⇒ e)} {g : BCC (a * c) (d ⇒ e)} 
  → apply ∘ < caseM x f g , y > ≈
    caseM x
      (apply ∘ < f , y ∘ π₁ >)
      (apply ∘ < g , y ∘ π₁ >)
apply-case = eq-sym (eq-trans (eq-sym comp-caseM) (congl (eq-trans η*
  (cong-pair
    (eq-trans comp-caseM (cong-caseM eq-refl π₁-pair π₁-pair))
    (eq-trans
      comp-caseM
      (eq-trans
        (cong-caseM eq-refl π₂-pair π₂-pair)
        (eq-trans
          (eq-sym comp-caseM)
          (eq-trans (congl useless-case) idr))))))))
  where
  useless-case : ∀{a b c} {x : BCC a (b + c)} → caseM x π₁ π₁ ≈ id {a}
  useless-case =
    eq-trans
      (congr
        (uniq-copair
          (eq-sym (eq-trans π₁-pair idl))
          (eq-sym (eq-trans π₁-pair idl))))
       π₁-pair



