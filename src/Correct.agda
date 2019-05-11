module Correct where

open import Sel
open import BCC
open import NBE
open import Type
open import Lemma
open import Presheaf
open import Data.Unit
open import Data.Empty
  renaming (⊥-elim to ⊥-elim')
  using (⊥)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product
  using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ ; ∃ ; ∃₂)
  
open 𝒫
open NBE.TreeMonad
open NBE.TreeOps

Sem : Ty → 𝒫 → Set
Sem x y = In y x

-- relation for induction on tree values
Rt : ∀ {a b B}
  → (Rl : ∀ {i} → BCC i b → Sem i B → Set) 
  → BCC a b
  → Tree a B
  → Set
Rt Rl t (leaf a)         = Rl t a
Rt Rl t (dead x)         = t ≈ init ∘ qₓ x
Rt Rl t (branch x c₁ c₂) =
  ∃₂ λ t₁ t₂
    → (Rt Rl t₁ c₁)
    × (Rt Rl t₂ c₂)
    × (t ≈ caseM (qₓ x) t₁ t₂)

Rl₀ : ∀ {a} → BCC a 𝟘 → Sem a 𝟘' → Set
Rl₀ _ = ⊥-elim'
  
R₀ : ∀ {a} → BCC a 𝟘 → Tree a 𝟘' → Set
R₀ t c = Rt Rl₀ t c

mutual

  -- logical relation between terms and semantic values
  R : ∀ {a b} → BCC a b → Sem a ⟦ b ⟧ → Set
  R {a} {b = 𝕓} t v =
    t ≈ q v
  R {a} {b = 𝟙} t v =
    ⊤
  R {a} {b = 𝟘} t v =
    R₀ t v
  R {a} {b = b ⇒ b₁} t v =
    ∀ {c t₁ v₁} → (τ : Sel c a) → R t₁ v₁ → R (apply ∘ < liftBCC τ t , t₁ >) (v τ v₁)
  R {a} {b = b * b₁} t v =
    R (π₁ ∘ t) (proj₁ v) × R (π₂ ∘ t) (proj₂ v)
  R {a} {b + c} t v =
   R₊ t v

  Rl₊ : ∀ {a b c} → BCC a (b + c) → Sem a ⟦ b ⟧ ⊎ Sem a ⟦ c ⟧ → Set
  Rl₊ t (inj₁ x) = ∃ (λ t' → R t' x × (injl ∘ t' ≈ t))
  Rl₊ t (inj₂ y) = ∃ (λ t' → R t' y × (injr ∘ t' ≈ t))
   
  R₊ : ∀ {a b c} → BCC a (b + c) → Tree a (⟦ b ⟧ +' ⟦ c ⟧) → Set
  R₊ t c = Rt Rl₊ t c   

-- Rt indexed by R
Rt' : ∀ {a b} → BCC a b → Tree a ⟦ b ⟧ → Set
Rt' = Rt R

Rtn : ∀ {a b} → BCC a b → Tree a (Nf' b) → Set
Rtn = Rt (λ t v → t ≈ q v)

inv₀ : ∀ {a} {t t' : BCC a 𝟘}
  → (v : Tree a 𝟘')
  → t ≈ t' → R₀ t' v → R₀ t v
inv₀ (leaf ()) p q
inv₀ (dead x) p q =
  eq-trans p q
inv₀ (branch x v v₁) p (t₁ , t₂ , t₁q , t₂q , r) =
  t₁ , t₂ , t₁q , t₂q , eq-trans p r

inv+ : ∀ {a b c} {t t' : BCC a (b + c)}
    → (v : Tree a (⟦ b ⟧ +' ⟦ c ⟧))
    → t ≈ t' → R₊ t' v → R₊ t v
inv+ (leaf (inj₁ _)) p (t₁ , q , r) =
  t₁ , q , eq-trans r (eq-sym p)
inv+ (leaf (inj₂ _)) p (t₁ , q , r) =
  t₁ , q , eq-trans r (eq-sym p)
inv+ (dead _)        p q            =
  eq-trans p q
inv+ (branch _ _ _)  p (t₁ , t₂ , t₁q , t₂q , r) =
  t₁ , t₂ , t₁q , t₂q , eq-trans p r
 
inv : ∀{b a} {t t' : BCC a b} {v : Sem a ⟦ b ⟧}
  → t  ≈ t'
  → R t' v
  → R t  v
inv {𝕓}         p q = eq-trans p q
inv {𝟙}         p q = tt
inv {𝟘} {v = v} p q = inv₀ v p q
inv {b ⇒ b₁}    p q {c = c} =
  λ τ x → inv {b₁} (congl (cong-pair (congr p) eq-refl)) (q τ x)
inv {b * b₁}    p q =
  inv {b} (congl p) (proj₁ q) , inv {b₁} (congl p) (proj₂ q)
inv {b = _ + _} {v = v} p q =
  inv+ v p q

liftConv : ∀ {a b c} {t t' : BCC a b} 
  → (τ : Sel c a)
  → t ≈ t'
  → liftBCC τ t ≈ liftBCC τ t'
liftConv τ p = congr p  

liftPresRt : ∀{b a c B}
  → (v : Tree a B)
  → {lP : {d : Ty} → BCC d b → Sem d B → Set}
  → {t  : BCC a b}
  → (τ : Sel c a)
  → Rt lP t v
  → (m : ∀{e c} {y t} (τ : Sel e c) → lP t y → lP (liftBCC τ t) (lift B τ y))
  → Rt lP (liftBCC τ t) (liftTree τ v)
liftPresRt (leaf a) τ p m = m τ p
liftPresRt (dead x) τ p  m =
  eq-trans
    (congr p)
    (eq-trans (eq-sym assoc) (congl (nat-qₓ _ _)))
liftPresRt (branch x v₁ v₂) τ (t₁ , t₂ , p₁ , p₂ , r) m =
  liftBCC (keep τ) t₁ ,
  liftBCC (keep τ) t₂ ,
  liftPresRt v₁ (keep τ) p₁ m ,
  liftPresRt v₂ (keep τ) p₂ m ,
  eq-trans (congr r) ((eq-trans
      post-comp-caseM
      (cong-caseM
        (nat-qₓ _ _)
        (congl (cong-pair eq-refl idl))
        (congl (cong-pair eq-refl idl)))))

liftPresR : ∀ {b a c}
  → (τ : Sel c a)
  → {t : BCC a b} {v : Sem a ⟦ b ⟧}
  → R t v
  → R (liftBCC τ t) (lift ⟦ b ⟧ τ v)
liftPresR {𝕓} τ {v = v}      p  = eq-trans (liftConv τ p) (nat-q τ v)
liftPresR {𝟙} τ              p  = tt
liftPresR {𝟘} τ {v = v}      p  = liftPresRt v τ p λ {_} {_} {y} _ x → ⊥-elim' y
liftPresR {b ⇒ b₁} τ {t} {v} p  = λ τ₁ x →
  inv {b₁}
    (congl (cong-pair (eq-sym bcc-pres-∘) eq-refl))
    (p (τ ∙ τ₁) x) 
liftPresR {b * b₁} τ (p₁ , p₂) =
  inv {b} assoc (liftPresR {b} τ p₁) ,
  inv {b₁} assoc (liftPresR {b₁} τ p₂)
liftPresR {b₁ + b₂} τ  {v = v}        p = liftPresRt v τ p (helper _)
  where
  helper : ∀ {e c} {t : BCC c (b₁ + b₂)}
      → (y : Sem c ⟦ b₁ ⟧ ⊎ Sem c ⟦ b₂ ⟧)
      → (τ : Sel e c)
      → Rl₊ t y
      → Rl₊ (t ∘ embToBCC τ) (lift (⟦ b₁ ⟧ +' ⟦ b₂ ⟧) τ y)
  helper (inj₁ x) τ (t₁ , p , q) = _ , (liftPresR {b₁} τ p) , eq-trans assoc (liftConv τ q)
  helper (inj₂ y) τ (t₁ , p , q) = _ , (liftPresR {b₂} τ p) , eq-trans assoc (liftConv τ q)

liftPresRt' : ∀{b a c}
  → (v : Tree a (⟦ b ⟧))
  → {t  : BCC a b}
  → (τ : Sel c a)
  → Rt' t v
  → Rt'(liftBCC τ t) (liftTree τ v)
liftPresRt' {b} v τ p = liftPresRt v τ p (λ σ x → liftPresR {b} σ x)

---------------------------------------
-- correctness of various operations --
---------------------------------------

corrJoin : ∀ {a b B} (t : BCC a b) (v : Tree a (Tree' B))
  → {P : ∀ {c} → BCC c b → Sem c B → Set}
  → Rt (Rt P) t v
  → Rt P t (join v)
corrJoin t (leaf a) p = p
corrJoin t (dead x) p = p
corrJoin t (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
  t₁ , t₂ , corrJoin _ v₁ p  , corrJoin _ v₂ q , r

-- corrProj₁ and corrProj₂ should be replacable with a "corrMap"

corrProj₁ : ∀{a b₁ b₂}
  (t : BCC a (b₁ * b₂))
  (v : Tree a (⟦ b₁ ⟧ ×' ⟦ b₂ ⟧))
  → Rt' t v
  → Rt' (π₁ ∘ t) (map proj₁ v)
corrProj₁ t (leaf a) p = proj₁ p
corrProj₁ t (dead x) p = eq-trans
  (congl p)
  (eq-trans assoc (congr (eq-sym uniq-init)))
corrProj₁ {a} t (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
  (π₁ ∘ t₁) , (π₁ ∘ t₂) ,
  corrProj₁ t₁ v₁ p , corrProj₁ t₂ v₂ q ,
  eq-trans (congl r) comp-caseM
  
corrProj₂ : ∀ {a b₁ b₂}
  (t : BCC a (b₁ * b₂))
  (v : Tree a (⟦ b₁ ⟧ ×' ⟦ b₂ ⟧))
  → Rt' t v
  → Rt' (π₂ ∘ t) (map proj₂ v)
corrProj₂ t (leaf a) p = proj₂ p
corrProj₂ t (dead x) p = eq-trans
  (congl p)
  (eq-trans assoc (congr (eq-sym uniq-init)))
corrProj₂ {a} t (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
  (π₂ ∘ t₁) , (π₂ ∘ t₂) ,
  corrProj₂ t₁ v₁ p , corrProj₂ t₂ v₂ q ,
  eq-trans (congl r) comp-caseM  

corrRunTreeNf : ∀{a b}
  → (t : BCC a b) (v : Tree a (Nf' b))
  → Rtn t v
  → t ≈ q (runTreeNf v)
corrRunTreeNf t (leaf a) p = p
corrRunTreeNf t (dead x) p = p
corrRunTreeNf t (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
  eq-trans r
    (cong-caseM
      eq-refl
      (corrRunTreeNf t₁ v₁ p) (corrRunTreeNf t₂ v₂ q))

mutual

  corrApTree : ∀ {a b₁ b₂}
    → (t  : BCC a (b₁ ⇒ b₂))
    → (t' : BCC a b₁)
    → (v  : Tree a (⟦ b₁ ⇒ b₂ ⟧))
    → (v' : Tree a ⟦ b₁ ⟧)
    → Rt' t v
    → Rt' t' v'
    → Rt' (apply ∘ < t , t' >) (apTree {b₁} {b₂} v v')
  corrApTree {a} {b₁} {b₂} t t₁ (leaf v) v₁ p q =
    inv {b₂}
      (congl (cong-pair (eq-sym bcc-pres-id) eq-refl))
      (p iden (corrRunTree {b₁} t₁ v₁ q))
  corrApTree {a} {b₁} {b₂} t t₁ (dead x) v₁ p q =
    eq-trans
      (congl (cong-pair
        -- the placement of uniq-init is the key here
        (eq-trans p (eq-trans (congr (uniq-init {f = curry (init ∘ π₁)})) comp-curry))
        eq-refl))
     (eq-trans
       (β⇒ _ _)
       (eq-trans
         (congr (eq-trans (eq-sym assoc) (congl π₁-pair)))
         (eq-trans
           (eq-trans
             (eq-sym assoc)
             (congl (eq-trans (eq-sym assoc) (congl π₁-pair))))
           (eq-trans assoc idr))))
  corrApTree {a} {b₁} {b₂} t t' (branch x v₁ v₂) v (t₁' , t₂' , p₁ , p₂ , r) q =
    (apply ∘ < t₁' , liftBCC (drop iden) t' >),
    (apply ∘ < t₂' , liftBCC (drop iden) t' >) ,
    corrApTree t₁' _ v₁ _ p₁ (liftPresRt' {b₁} v (drop iden) q) ,
    corrApTree t₂' _ v₂ _ p₂ (liftPresRt' {b₁} v (drop iden) q) ,
    eq-trans
      (congl (cong-pair r eq-refl))
      (eq-trans
        apply-case
        (cong-caseM
          eq-refl
          (congl (cong-pair
            eq-refl
            (eq-sym (eq-trans
              assoc
              (congr (eq-trans (congl embdId) idr))))))
          ((congl (cong-pair
            eq-refl
            (eq-sym (eq-trans
              assoc
              (congr (eq-trans (congl embdId) idr)))))))))
              
  corrRunTree : ∀{b a}
    → (t : BCC a b) (v : Tree a ⟦ b ⟧)
    → Rt' t v
    → R t (runTree {b} v)
  corrRunTree {𝕓}       t v p = corrRunTreeNf t v p
  corrRunTree {𝟙}       t v p = tt
  corrRunTree {𝟘}       t v p = corrJoin t v p
  corrRunTree {b₁ ⇒ b₂} t v p {t₁ = t₁} {v₁} =
    λ τ x → corrRunTree {b₂}
      (apply ∘ < liftBCC τ t , t₁ > )
      (apTree {b₁} {b₂} (liftTree τ v) (leaf v₁))
      (corrApTree (liftBCC τ t) t₁ (liftTree τ v) (leaf v₁) (liftPresRt' {b₁ ⇒ b₂} v τ p) x)
  corrRunTree {b₁ * b₂} t v p =
    corrRunTree {b₁} _ _ (corrProj₁ t v p) ,
    corrRunTree {b₂} _ _ (corrProj₂ t v p)
  corrRunTree {b + b₁} t v p  = corrJoin t v p

corr-𝟘-elim : ∀ {c a} {u : BCC a 𝟘} {v : Tree a 𝟘'}
  → R₀ u v
  → R (init {c} ∘ u) (runTree {c} (map (cast ⟦ c ⟧) v))
corr-𝟘-elim {c} {u = u} {v = v} p =
  corrRunTree {c} _ _ (aux-lemma v p)
  where
  -- composing init is same as mapping ⊥-elim
  aux-lemma : ∀ {c a} {u : BCC a 𝟘}
    → (v : Tree a 𝟘')
    → R₀ u v
    → Rt' (init {c} ∘ u) (map (cast ⟦ c ⟧) v)
  aux-lemma (leaf ()) p
  aux-lemma (dead x)  p         =
    eq-trans (congl p) (eq-trans assoc (congr (eq-sym uniq-init)))
  aux-lemma (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
    (init ∘ t₁) , (init ∘ t₂) ,
    aux-lemma v₁ p , (aux-lemma v₂ q , eq-trans (congl r) comp-caseM)

Fund : {b c : Ty} (t : BCC b c) → Set
Fund {b} {c} t = ∀ {a} {u : BCC a b} {v : Sem a ⟦ b ⟧}
  → R u v
  → R (t ∘ u) (eval t v)
  
-- the fundamental theorem of R
corrEval : ∀{c b}
  → (t : BCC b c)
  → Fund t
corrEval {c} id         p       = inv {c} idl p
corrEval {c} (t ∘ t₁)   p       =
  inv {c} (eq-sym assoc) (corrEval t (corrEval t₁ p))
corrEval π₁         (p₁ , _)    = p₁
corrEval π₂         (_ , p₂)    = p₂
corrEval {c₁ * c₂} < t , t₁ > p =
  inv {c₁} (eq-trans assoc (congr π₁-pair)) (corrEval t p) ,
  inv {c₂} (eq-trans assoc (congr π₂-pair)) (corrEval t₁ p)
corrEval {c} init       p       = corr-𝟘-elim {c} p
corrEval unit           p       = tt
corrEval {c ⇒ c₁} {b} (curry t) {u = u} p {t₁ = t₁}  = λ τ x →
  inv {c₁}
    (eq-trans
      (congl (cong-pair (eq-trans (eq-sym assoc) comp-curry) eq-refl))
      (eq-trans (β⇒ _ _) (eq-trans
        (eq-sym assoc)
        (congl (eq-trans comp-pair (cong-pair
          (eq-trans (eq-sym assoc) (eq-trans (congl π₁-pair) idr))
          (eq-trans (eq-sym assoc) (eq-trans (congl π₂-pair) idl))))))))
    (corrEval {c₁}
      t {u = < liftBCC τ u , t₁ >}
      (inv {b} π₁-pair (liftPresR {b} τ p) , inv {c} π₂-pair x))
corrEval {c} apply    (p₁ , p₂)  =
  inv {c}
    (congl (eq-trans η* (cong-pair
      (eq-sym (eq-trans (congl embdId) idr))
      eq-refl)))
    (p₁ iden p₂)
corrEval injl           p          = _ , p , eq-refl
corrEval injr           p          = _ , p , eq-refl
corrEval {c} [ t₁ , t₂ ] {v = v} p = corrRunTree {c} _ _ (corrMatch' t₁ t₂ v p)
  where
  corrMatch' : ∀ {a c d e} {u :  BCC a (d + e)}
      (t₁ : BCC d c)
      (t₂ : BCC e c)
      → (v : Sem a (Tree' (⟦ d ⟧ +' ⟦ e ⟧)))
      → R₊ u v
      → Rt' ([ t₁ , t₂ ] ∘ u) (map (match' {d} {e} {c} (eval t₁) (eval t₂)) v)
  corrMatch' {c = c} t₁ t₂ (leaf (inj₁ x)) (t' , p , q) = inv {c}
    (eq-trans
      (congl (eq-sym q))
      (eq-trans assoc (congr match-injl)))
    (corrEval t₁ p)
  corrMatch' {c = c} t₁ t₂ (leaf (inj₂ y)) (t' , p , q) = inv {c}
    (eq-trans
      (congl (eq-sym q))
      (eq-trans assoc (congr match-injr)))
    (corrEval t₂ p)
  corrMatch' t₁ t₂ (dead x) p = eq-trans (congl p) (eq-trans assoc (congr (eq-sym uniq-init)))
  corrMatch' {a} {c} {d} {e} t₁ t₂ (branch x v₁ v₂) (t₁' , t₂' , p , q , r) =
    ([ t₁ , t₂ ] ∘ t₁') ,
    ([ t₁ , t₂ ] ∘ t₂') ,
    corrMatch' t₁ t₂ v₁ p ,
    corrMatch' t₁ t₂ v₂ q ,
    eq-trans (congl r) comp-caseM

corrReify₀ : ∀ {a} {t : BCC a 𝟘} (v : Tree a 𝟘') →
  R₀ t v →
  t ≈ q (runTreeNf (map (cast (Nf' 𝟘)) v))
corrReify₀ (leaf ()) p
corrReify₀ (dead x) p = p
corrReify₀ (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
  eq-trans r (cong-caseM eq-refl (corrReify₀ v₁ p) (corrReify₀ v₂ q))

mutual

  corrReifyVal : ∀{b a} {t : BCC a b} {v : Sem a ⟦ b ⟧}
    → R t v → t ≈ (q (reifyVal v))
  corrReifyVal {𝕓}         p = p
  corrReifyVal {𝟙}         p = eq-sym uniq-unit
  corrReifyVal {𝟘} {v = v} p = corrReify₀ v p    
  corrReifyVal {b ⇒ b₁}    p  = eq-trans
    η⇒
    (cong-curry
      (corrReifyVal {b₁}
        (inv {b₁}
          (congl (cong-pair (congl (eq-trans (eq-sym idl) (congr (eq-sym embdId))))
          (eq-trans idl keepIdenIsIden)))
          (p (drop iden) (corrReflect {b})))))
  corrReifyVal {b * b₁}    p = eq-trans
    η* -- eta expand product, returns a pair
    (cong-pair (corrReifyVal (proj₁ p)) ((corrReifyVal (proj₂ p))))
  corrReifyVal {b + b₁} {v = v} p = corrReifyOr v p 

  corrReifyOr : ∀{a b₁ b₂} {t : BCC a (b₁ + b₂)} (v : Sem a (Tree' (⟦ b₁ ⟧ +' ⟦ b₂ ⟧)))
      → R₊ t v
      → t ≈ q (runTreeNf (map reifyValOr v))
  corrReifyOr (leaf (inj₁ x)) (t , p , q) = eq-trans (eq-sym q) (congl (corrReifyVal p))
  corrReifyOr (leaf (inj₂ y)) (t , p , q) = eq-trans (eq-sym q) (congl (corrReifyVal p))
  corrReifyOr (dead x)        p           = p
  corrReifyOr (branch x v₁ v₂) (t₁ , t₂ , p , q , r) =
    eq-trans r (cong-caseM eq-refl (corrReifyOr v₁ p) (corrReifyOr v₂ q))
  
  corrReflect : ∀ {b a} → {n : Ne a b} → R (qₓ n) (reflect b n)
  corrReflect {𝕓}       = eq-refl
  corrReflect {𝟙}       = tt
  corrReflect {𝟘}       = eq-trans (eq-sym idl) (congr (eq-sym uniq-init))
  corrReflect {b₁ ⇒ b₂} = λ τ x  →
    inv {b₂}
      (congl (cong-pair (nat-qₓ _ _) (corrReifyVal x)))
      (corrReflect {b₂})
  corrReflect {b₁ * b₂} = corrReflect {b₁} , corrReflect {b₂}
  corrReflect {b₁ + b₂} =
    (injl ∘ π₂) ,
    (injr ∘ π₂) ,
    (π₂ , inv {b₁} keepIdenIsIden (corrReflect {b₁}) , eq-refl) ,
    (π₂ , inv {b₂} keepIdenIsIden (corrReflect {b₂}) , eq-refl) ,
    η+   -- eta expand sum type , returns a caseM

corrReflectᵢ : ∀ a → R (id {a}) (reflectᵢ a)
corrReflectᵢ a = inv {a}
  (eq-sym bcc-pres-id)
  (corrReflect {a} {n = sel iden})

corrReify : ∀ {a b}
  → {t : BCC a b}
  → Fund t
  → t ≈ q (reify (eval t))
corrReify {a} {b} f = corrReifyVal (inv {b} (eq-sym idr) (f (corrReflectᵢ a)))

correctNorm : ∀{a b} (t : BCC a b) → t ≈ q (norm t)
correctNorm {a} {b} t = corrReify (corrEval t)
