{-# OPTIONS --postfix-projections #-}
------------------------------------------------------------------------
-- Term language of BCC combinators
--
-- Term syntax, typing, conversion rules and derived laws
------------------------------------------------------------------------

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

-- | Distribute * over +
distrf : ∀ {a b c} → BCC (a * (b + c)) ((a * b) + (a * c))
distrf = apply ∘
    < [ curry (injl ∘ < π₂ , π₁ >)
    , curry (injr ∘ < π₂ , π₁ >) ] ∘ π₂
    , π₁ >

-- | Distribute * over + (reverse)
distrb : ∀ {a b c} → BCC ((a * b) + (a * c)) (a * (b + c))
distrb = [ < π₁ , injl ∘ π₂ > , < π₁ , injr ∘ π₂ > ]

copair : ∀ {a b c d} → BCC (a * b) d -> BCC (a * c) d -> BCC (a * (b + c)) d
copair f g = [ f , g ] ∘ distrf

caseM : ∀ {a b c d} → BCC a (b + c) → BCC (a * b) d -> BCC (a * c) d -> BCC a d
caseM x f g = copair f g ∘ < id , x >

infix 2 _≈_

data _≈_ : ∀ {a b} → (f g : BCC a b) → Set where

  -- categorical laws
  
  idr  : ∀ {a b} {f : BCC a b}
    → (f ∘ id) ≈ f
  idl  : ∀ {a b} {f : BCC a b}
    → (id ∘ f) ≈ f
  assoc : ∀ {a b c d} {h : BCC a b} {g : BCC b c} {f : BCC c d}
    → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h

  -- elimination laws

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

  -- uniqueness laws
  
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
    
  -- _≈_ is an equivalence relation
  
  refl  : ∀ {a b} {f : BCC a b}
    → f ≈ f
  sym   : ∀ {a b} {f g : BCC a b}
    → f ≈ g → g ≈ f
  trans : ∀ {a b} {f g h : BCC a b}
    → f ≈ g → g ≈ h → f ≈ h

  -- congruence laws
  
  congl : ∀ {a b c} {x y : BCC a b} {f : BCC b c}
    → x ≈ y → f ∘ x ≈ f ∘ y
  congr : ∀ {a b c} {x y : BCC b c} {f : BCC a b}
    → x ≈ y → x ∘ f ≈ y ∘ f

-- Distributivity laws hold in any BCC 
-- Distributivity laws can be derived in _≈_, but the reasoning
-- is quite standard and boring, so we add it as a postulate here.
postulate
  distrfnb : ∀{a b c} → distrb ∘ distrf ≈ id {a * (b + c)}
  -- reverse also holds, but not needed here

-- boilerplate to use the setoid library for eq. reasoning
module SetoidUtil where

  open import Relation.Binary
    using (Setoid ; IsEquivalence) 

  open Setoid
    renaming (_≈_ to _≈ₑ_)
    using (Carrier ; isEquivalence)

  Hom : (a b : Ty) → Setoid _ _
  Hom a b .Carrier = BCC a b
  Hom a b ._≈ₑ_     = _≈_
  Hom a b .isEquivalence .IsEquivalence.refl  = refl
  Hom a b .isEquivalence .IsEquivalence.sym   = _≈_.sym
  Hom a b .isEquivalence .IsEquivalence.trans = _≈_.trans

  import Relation.Binary.SetoidReasoning as SetoidR
  open SetoidR public

open SetoidUtil 

-- standard pair rules

comp-pair : ∀{a b c d} {h : BCC d c} {f : BCC c a} {g : BCC c b}
  → < f , g > ∘ h ≈ < (f ∘ h) , (g ∘ h) >
comp-pair = sym
  (uniq-pair
    (trans assoc (congr π₁-pair))
    (trans assoc (congr π₂-pair)))

cong-pair : ∀{a b d} → {f f' : BCC a b} {g g' : BCC a d}
  → f ≈ f' → g ≈ g' → < f , g > ≈ < f' , g' >
cong-pair p q = uniq-pair
  (trans π₁-pair (sym p))
  (trans π₂-pair (sym q))

-- standard ∘ rules

cong-∘ : ∀{a b c} → {f f' : BCC a b} {g g' : BCC c a}
  → f ≈ f' → g ≈ g' → f ∘ g ≈ f' ∘ g'
cong-∘ p q = trans (congr p) (congl q)

-- standard ⊗ rules

cong-⊗ : ∀{a b c d} → {f f' : BCC a b} {g g' : BCC c d}
  → f ≈ f' → g ≈ g' → f ⊗ g ≈ f' ⊗ g'
cong-⊗ p q = uniq-pair
  (trans π₁-pair (sym (congr p)))
  (trans π₂-pair (sym (congr q)))

comp-⊗ : ∀{a b c d} {h : BCC d c} {f : BCC c b}
  → (f ∘ h) ⊗ id {a} ≈ (f ⊗ id) ∘ (h ⊗ id)
comp-⊗ = sym
  (trans
    comp-pair
    (cong-pair
      (trans
        (sym assoc) (trans (congl π₁-pair) assoc))
        (trans (sym assoc) (congl (trans π₂-pair idl)))))

-- standard curry rules

cong-curry : ∀{a b c} → {f f' : BCC (a * b) c}
  → f ≈ f' → curry f ≈ curry f'
cong-curry p = uniq-curry (trans apply-curry (sym p))

comp-curry : ∀{a b c d} {h : BCC d c} {f : BCC (c * a) b}
  → curry f ∘ h ≈ curry (f ∘ (h ⊗ id))
comp-curry = sym (uniq-curry
  (trans
    (congl comp-⊗)
    (trans assoc (congr apply-curry))))

-- standard match rules

cong-match : ∀ {a b c} {f f' : BCC a c} {g g' : BCC b c}
  → f ≈ f'
  → g ≈ g'
  → ([ f , g ]) ≈ ([ f' , g' ])
cong-match p q = uniq-match
  (trans match-injl (sym p))
  (trans match-injr (sym q))  

comp-match : ∀ {a b c d} {h : BCC c d} {f  : BCC a c} {g : BCC b c}
  → h ∘ [ f , g ] ≈ [ h ∘ f , h ∘ g ]
comp-match = sym (uniq-match
  (trans (sym assoc) (congl match-injl))
  ((trans (sym assoc) (congl match-injr))))

-- beta reduction (useful lemma)

β⇒  : ∀ {a b c} (f : BCC (c * a) b) (g : BCC c a)
  → apply ∘ < (curry f) , g > ≈ (f ∘ < id , g >)
β⇒ f g = trans
  (trans
    (congl
      (sym (trans
        comp-pair
        (cong-pair
          (trans (sym assoc) (trans (congl π₁-pair) idr))
          (trans (sym assoc) (trans idl π₂-pair))))))
    assoc)
  (congr apply-curry)

-- copair laws (useful intermediate step to prove special rules about case)

copair-injl : ∀{a b c d} {f : BCC (a * b) d} {g : BCC (a * c) d}
    → copair f g ∘ (id ⊗ injl) ≈  f
copair-injl {f = f} {g} = begin⟨ Hom _ _ ⟩
  copair f g ∘ (< id ∘ π₁ , injl ∘ π₂ >)
    ≈⟨ sym assoc ⟩
  [ f , g ] ∘ (distrf ∘ < id ∘ π₁ , injl ∘ π₂ >)
    ≈⟨ congl (trans
       (sym assoc)
       (congl (trans
         comp-pair
         (cong-pair
           (trans (sym assoc) (trans (congl π₂-pair) (trans assoc (congr match-injl))))
           (trans π₁-pair idl))))) ⟩
  [ f , g ] ∘ apply ∘ < curry (injl ∘ < π₂ , π₁ >) ∘ π₂ , π₁ >
      ≈⟨ congl (congl (cong-pair
         (trans
           comp-curry (cong-curry (trans (sym assoc)
           (congl (congl (cong-pair refl idl))))))
         refl)) ⟩
  [ f , g ] ∘ apply ∘ < curry (injl ∘ < π₂ , π₁ > ∘ < π₂ ∘ π₁ , π₂ >) , π₁ >
    ≈⟨ congl (congl (cong-pair (cong-curry
      (congl (trans comp-pair (cong-pair π₂-pair π₁-pair))))
      refl)) ⟩
  [ f , g ] ∘ apply ∘ < curry (injl ∘ < π₂ , π₂ ∘ π₁ >) , π₁ >
    ≈⟨ congl (trans (β⇒ _ _) (sym assoc)) ⟩
  [ f , g ] ∘ injl ∘ (< π₂ , π₂ ∘ π₁ > ∘ < id , π₁ >)
      ≈⟨ congl (congl (trans
          comp-pair
          (cong-pair π₂-pair (trans
            (sym assoc)
            (trans (congl π₁-pair) idr))))) ⟩
  [ f , g ] ∘ injl ∘ (< π₁ , π₂ >)
    ≈⟨ congl (trans (congl (uniq-pair idr idr)) idr) ⟩
  [ f , g ] ∘ injl
    ≈⟨ match-injl ⟩
  f ∎    
               
copair-injr : ∀{a b c d} {f : BCC (a * b) d} {g : BCC (a * c) d}
    → copair f g ∘ (id ⊗ injr) ≈ g
-- symmetric to proof steps in copair-injl
copair-injr {f = f} {g} = begin⟨ Hom _ _ ⟩
  copair f g ∘ (< id ∘ π₁ , injr ∘ π₂ >)
    ≈⟨ sym assoc ⟩
  [ f , g ] ∘ (distrf ∘ < id ∘ π₁ , injr ∘ π₂ >)
      ≈⟨ congl (trans
       (sym assoc)
       (congl (trans
         comp-pair
         (cong-pair
           (trans (sym assoc) (trans (congl π₂-pair) (trans assoc (congr match-injr))))
           (trans π₁-pair idl))))) ⟩
   [ f , g ] ∘ apply ∘ < curry (injr ∘ < π₂ , π₁ >) ∘ π₂ , π₁ >
       ≈⟨ congl (congl (cong-pair
         (trans
           comp-curry (cong-curry (trans (sym assoc)
           (congl (congl (cong-pair refl idl))))))
         refl)) ⟩
  [ f , g ] ∘ apply ∘ < curry (injr ∘ < π₂ , π₁ > ∘ < π₂ ∘ π₁ , π₂ >) , π₁ >
      ≈⟨ congl (congl (cong-pair (cong-curry
        (congl (trans comp-pair (cong-pair π₂-pair π₁-pair))))
        refl)) ⟩
  [ f , g ] ∘ apply ∘ < curry (injr ∘ < π₂ , π₂ ∘ π₁ >) , π₁ >
      ≈⟨ congl (trans (β⇒ _ _) (sym assoc)) ⟩
  [ f , g ] ∘ injr ∘ (< π₂ , π₂ ∘ π₁ > ∘ < id , π₁ >)
      ≈⟨ congl (congl (trans
          comp-pair
          (cong-pair π₂-pair (trans
            (sym assoc)
            (trans (congl π₁-pair) idr))))) ⟩
  [ f , g ] ∘ injr ∘ (< π₁ , π₂ >)
      ≈⟨ congl (trans (congl (uniq-pair idr idr)) idr) ⟩
  [ f , g ] ∘ injr
      ≈⟨ match-injr ⟩
  g ∎

uniq-copair : ∀ {a b c d} {f : BCC (a * b) d} {g : BCC (a * c) d} {h : BCC (a * (b + c)) d}
    → f ≈ h ∘ (id ⊗ injl)
    → g ≈ h ∘ (id ⊗ injr)
    → copair f g ≈ h
uniq-copair p q = trans
  (congr (trans (cong-match p q) (sym comp-match)))
  (trans
    (sym assoc)
    (trans
      (congl (trans
        (congr (cong-match (cong-pair idl refl) (cong-pair idl refl)))
        distrfnb))
      idr))

-- standard copair laws

cong-copair : ∀ {a b c d} {f f' : BCC (a * b) d} {g g' : BCC (a * c) d}
  → f ≈ f'
  → g ≈ g'
  → copair f g ≈ copair f' g'
cong-copair p q = uniq-copair
  (trans p (sym copair-injl))
  (trans q (sym copair-injr))  

comp-copair : ∀ {a b c d e} {f : BCC (a * b) d} {g : BCC (a * c) d} {h : BCC d e}
  → h ∘ copair f g ≈ copair (h ∘ f) (h ∘ g)
comp-copair = sym (uniq-copair
  (sym (trans (sym assoc) (congl copair-injl)))
  (sym (trans (sym assoc) (congl copair-injr))))

-- special copair law

post-comp-copair : ∀ {a b c d e} {f : BCC (a * b) d}
  {g : BCC (a * c) d} {h : BCC e a}
  → copair f g ∘ (h ⊗ id) ≈ copair (f ∘ h ⊗ id) (g ∘ h ⊗ id)
post-comp-copair {f = f} {g} {h} = begin⟨ Hom _ _ ⟩
  copair f g ∘ (h ⊗ id)
    ≈⟨ sym (uniq-copair refl refl) ⟩
  copair
    ((copair f g ∘ (h ⊗ id)) ∘ (id ⊗ injl))
    ((copair f g ∘ (h ⊗ id)) ∘ (id ⊗ injr))
    ≈⟨ cong-copair
      (trans (sym assoc) (trans (congl swap-⊗) assoc))
      (trans (sym assoc) (trans (congl swap-⊗) assoc)) ⟩
  copair
    ((copair f g ∘ (id ⊗ injl)) ∘ (h ⊗ id))
    ((copair f g ∘ (id ⊗ injr)) ∘ (h ⊗ id))
    ≈⟨ cong-copair (congr copair-injl) (congr copair-injr) ⟩
  copair
    (f ∘ h ⊗ id)
    (g ∘ h ⊗ id) ∎
    where
      swap-⊗ : ∀{a b c d} {f : BCC a b} {g : BCC c d}
        → (f ⊗ id) ∘ (id ⊗ g) ≈ (id ⊗ g) ∘ (f ⊗ id)
      swap-⊗ = trans
        comp-pair                    -- merge pairs on left
        (sym (trans comp-pair  -- merge pairs on right
          (cong-pair
            -- simplify the first components on both sides till they're equal
            (trans
              (congr idl)
              (trans
                π₁-pair
                (sym (trans (sym assoc) (congl (trans π₁-pair idl))))))
            -- simplify the second component on both sides till they're equal
            (trans
              (sym assoc)
              (trans
                (congl (trans π₂-pair idl))
                (sym (trans (congr idl) π₂-pair)))))))

-- standard case rules

cong-caseM : ∀ {a b c d}
  {x x' :  BCC a (b + c)} {f f' : BCC (a * b) d} {g g' : BCC (a * c) d}
  → x ≈ x'
  → f ≈ f'
  → g ≈ g'
  → caseM x f g ≈ caseM x' f' g'
cong-caseM p q r = cong-∘ (cong-copair q r) (cong-pair refl p)

comp-caseM : ∀ {a b c d e} {h : BCC d e}
  {x :  BCC a (b + c)} {f  : BCC (a * b) d} {g : BCC (a * c) d}
  → h ∘ (caseM x f g) ≈ caseM x (h ∘ f) (h ∘ g)
comp-caseM = trans assoc (congr comp-copair)

-- eta rules

η⇒ : ∀{a b c} → {f : BCC a (b ⇒ c)}
  → f ≈ curry (uncurry f)
η⇒ = sym (uniq-curry refl)

η* : ∀{a b c} → {f : BCC a (b * c)}
  → f ≈ < π₁ ∘ f , π₂ ∘ f >
η* = sym (uniq-pair refl refl)

η+ : ∀{a b c} → {f : BCC a (b + c)}
  → f ≈ caseM f (injl ∘ π₂) (injr ∘ π₂)
η+ = sym
  (trans
    (congr
      (uniq-copair
        (sym π₂-pair)
        (sym π₂-pair)))
    π₂-pair)

-- special case rules

post-comp-caseM : ∀ {a b c d e} {h : BCC e a}
  {x :  BCC a (b + c)} {f  : BCC (a * b) d} {g : BCC (a * c) d}
  → (caseM x f g) ∘ h ≈ caseM (x ∘ h) (f ∘ h ⊗ id {b}) (g ∘ h ⊗ id)
post-comp-caseM {h = h} {x} {f} {g} = begin⟨ Hom _ _ ⟩
  (caseM x f g) ∘ h
    ≈⟨ sym assoc ⟩
  copair f g ∘ < id , x > ∘ h
    ≈⟨ congl comp-pair ⟩
  copair f g ∘ < id ∘ h , x ∘ h >
    ≈⟨ congl (cong-pair idl refl) ⟩
  copair f g ∘ < h , x ∘ h >
    ≈⟨ congl (trans
       (cong-pair
         (sym (trans (sym assoc) (trans (congl π₁-pair) idr)))
         (sym π₂-pair))
       (sym (comp-pair {h = < id , x ∘ h >}  {f = h ∘ π₁} {g = π₂}))) ⟩
  copair f g ∘ < h ∘ π₁ , π₂ > ∘  < id , x ∘ h > 
    ≈⟨ assoc ⟩
  (copair f g ∘ < h ∘ π₁ , π₂ >) ∘ < id , x ∘ h > 
    ≈⟨ congr (sym (uniq-copair
      (sym (trans
        (congr
          (trans
            (congl (cong-pair refl (sym idl)))
            post-comp-copair))
         copair-injl))
       (sym (trans
        (congr
          (trans
            (congl (cong-pair refl (sym idl)))
            post-comp-copair))
         copair-injr)))) ⟩
  copair (f ∘ h ⊗ id) (g ∘ h ⊗ id) ∘ < id , x ∘ h >
    ≈⟨ refl ⟩
  caseM (x ∘ h) (f ∘ h ⊗ id) (g ∘ h ⊗ id) ∎    


apply-case : ∀{a b c d e}
  {x : BCC a (b + c)} {y : BCC a d}
  {f : BCC (a * b) (d ⇒ e)} {g : BCC (a * c) (d ⇒ e)} 
  → apply ∘ < caseM x f g , y > ≈
    caseM x
      (apply ∘ < f , y ∘ π₁ >)
      (apply ∘ < g , y ∘ π₁ >)
apply-case = sym (trans (sym comp-caseM) (congl (trans η*
  (cong-pair
    (trans comp-caseM (cong-caseM refl π₁-pair π₁-pair))
    (trans
      comp-caseM
      (trans
        (cong-caseM refl π₂-pair π₂-pair)
        (trans
          (sym comp-caseM)
          (trans (congl useless-case) idr))))))))
  where
  useless-case : ∀{a b c} {x : BCC a (b + c)} → caseM x π₁ π₁ ≈ id {a}
  useless-case =
    trans
      (congr
        (uniq-copair
          (sym (trans π₁-pair idl))
          (sym (trans π₁-pair idl))))
       π₁-pair


