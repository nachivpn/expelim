open import Type
open import Util
open import BCC
open import Sel
open import Presheaf
open import Data.Unit using (tt)
open import Data.Sum using (inj₁ ; inj₂)

-- neutral and normal forms
mutual

  data Ne (a : Ty) : Ty → Set where
    sel : ∀ {b}   → Sel a b      → Ne a b           -- id / π₁ / < , >        
    fst : ∀ {b c} → Ne a (b * c) → Ne a b           -- π₁ ∘ x
    snd : ∀ {b c} → Ne a (b * c) → Ne a c           -- π₂ ∘ x
    app : ∀ {b c} → Ne a (b ⇒ c) → Nf a b → Ne a c  -- eval ∘ < x , n >
        
  data Nf (a : Ty) : Ty → Set where
    unit :             Nf a 𝟙
    ne-𝕓 :             Ne a 𝕓 → Nf a 𝕓
    ne-⊥ : ∀ {b}     → Ne a 𝟘 → Nf a b
    injl : ∀ {b c}   → Nf a b → Nf a (b + c)
    injr : ∀ {b c}   → Nf a c → Nf a (b + c)
    pair : ∀ {b c}   → Nf a b → Nf a c → Nf a (b * c)
    abs  : ∀ {b c}   → Nf (a * b) c → Nf a (b ⇒ c)
    case : ∀ {b c d} → Ne a (b + c) → Nf (a * b) d → Nf (a * c) d → Nf a d

mutual

  liftNf : ∀ {i j a} → Sel j i → Nf i a → Nf j a
  liftNf e unit         = unit
  liftNf e (ne-𝕓 x)     = ne-𝕓 (liftNe e x)
  liftNf e (ne-⊥ x)     = ne-⊥ (liftNe e x)
  liftNf e (injl n)     = injl (liftNf e n)
  liftNf e (injr n)     = injr (liftNf e n)
  liftNf e (pair n n₁)  = pair (liftNf e n) (liftNf e n₁)
  liftNf e (abs n)      = abs (liftNf (keep e) n)
  liftNf e (case x p q) = case (liftNe e x) (liftNf (keep e) p) (liftNf (keep e) q)
  
  liftNe : ∀ {i j a} → Sel j i → Ne i a → Ne j a
  liftNe e (sel x)   = sel (x ∙ e)
  liftNe e (fst x)   = fst (liftNe e x)
  liftNe e (snd x)   = snd (liftNe e x)
  liftNe e (app n x) = app (liftNe e n) (liftNf e x)

open 𝒫

liftBCC : ∀ {i j a} → Sel j i → BCC i a → BCC j a
liftBCC e m = m ∘ embToBCC e

BCC' : (a : Ty) → 𝒫
BCC' a .In i = BCC i a
BCC' a .lift = liftBCC

Ne' : (a : Ty) → 𝒫
Ne' a .In i = Ne i a
Ne' a .lift = liftNe

Nf' : (a : Ty) → 𝒫
Nf' a .In i = Nf i a
Nf' a .lift = liftNf

-- the decision tree monad
module TreeMonad where

  data Tree (i : Ty) (A : 𝒫) : Set where
    leaf   : (x : A .In i) →  Tree i A
    dead   : Ne i 𝟘 → Tree i A
    -- "semantic case"
    branch : ∀{c d} → Ne i (c + d) → Tree (i * c) A →  Tree (i * d) A → Tree i A 

  liftTree : ∀ {A i j} → Sel j i → Tree i A  → Tree j A
  liftTree {A} e (leaf x)       = leaf (lift A e x)
  liftTree     e (dead x)       = dead (liftNe e x)
  liftTree     e (branch x p q) =
    branch (liftNe e x)
      (liftTree (keep e) p)
      (liftTree (keep e) q)
  
  Tree' : (A : 𝒫) → 𝒫
  Tree' A .In i  = Tree i A
  Tree' A .lift    = liftTree

  return : ∀ {A} → A →̇ Tree' A
  return = leaf
  
  map : ∀ {A B : 𝒫} → (A →̇ B) → Tree' A →̇ Tree' B
  map t (leaf x)       = leaf (t x)
  map t (dead x)       = dead x
  map t (branch x p q) = branch x (map t p) (map t q)

  join : ∀{A} → Tree' (Tree' A) →̇ Tree' A
  join (leaf x)       = x
  join (dead x)       = dead x
  join (branch x p q) = branch x (join p) (join q)

open TreeMonad

-- interpretation of types as presheaves
⟦_⟧ : Ty → 𝒫
⟦    𝟘   ⟧ = Tree' 𝟘'
⟦    𝟙   ⟧ = 𝟙'
⟦    𝕓   ⟧ = Nf' 𝕓
⟦ a ⇒ b ⟧ = ⟦ a ⟧ ⇒' ⟦ b ⟧
⟦ a * b ⟧ = ⟦ a ⟧ ×' ⟦ b ⟧
⟦ a + b ⟧ = Tree' (⟦ a ⟧ +' ⟦ b ⟧)

-- special tree operations
module TreeOps where

  runTreeNf : ∀ {a} → Tree' (Nf' a) →̇ Nf' a
  runTreeNf (leaf x)      = x
  runTreeNf (dead x)      = ne-⊥ x
  runTreeNf (branch x p q) = case x (runTreeNf p) (runTreeNf q)

  mutual

    -- (Tree c ⟦_⟧) is an "applicative functor"
    apTree : ∀ {a b c} → Tree c ⟦ a ⇒ b ⟧ → Tree c ⟦ a ⟧ → Tree c ⟦ b ⟧
    apTree {A} {B} (leaf x)       c = leaf (x iden (runTree {A} c))
    apTree {A} {B} (dead x)       c = dead x
    apTree {A} {B} (branch x f g) c =
      branch x
        (apTree {A} {B} f (lift (Tree' ⟦ A ⟧) (drop iden) c))
        (apTree {A} {B} g (lift (Tree' ⟦ A ⟧) (drop iden) c))
  
    runTree : ∀ {a} → Tree' ⟦ a ⟧ →̇ ⟦ a ⟧
    runTree {𝟘}     c = join c
    runTree {𝟙}     _ = tt
    runTree {𝕓}     c = runTreeNf c
    runTree {A ⇒ B} c = λ τ a → runTree {B} (apTree {A} {B} (liftTree τ c) (leaf a))
    runTree {A * B} c = runTree {A} (map proj₁ c) , runTree {B} (map proj₂ c)
    runTree {A + B} c = join c

open TreeOps

cast : ∀ A → 𝟘' →̇ A
cast _ ()

match' : ∀{a b c} → (⟦ a ⟧ →̇ ⟦ c ⟧) → (⟦ b ⟧ →̇ ⟦ c ⟧) → ((⟦ a ⟧ +' ⟦ b ⟧) →̇ ⟦ c ⟧)
match' f g (inj₁ x) = f x
match' f g (inj₂ y) = g y
    
eval : ∀ {b a} → BCC a b → (⟦ a ⟧ →̇ ⟦ b ⟧)
eval id x                    = x
eval (t ∘ s) x               = (eval t) (eval s x)
eval π₁ (p , _)              = p
eval π₂ (_ , q)              = q
eval < p , q > x             = eval p x , eval q x
eval {b} init x              = runTree {b} (map (cast ⟦ b ⟧) x)
eval unit x                  = tt
eval {b} {a} (curry f) x     = λ τ y → eval f (⟦ a ⟧ .lift τ x , y)
eval apply (f , x)           = f iden x
eval injl x                  = leaf (inj₁ x)
eval injr x                  = leaf (inj₂ x)
eval {c} {a + b} [ p , q ] x =
  runTree {c}
    (map (match' {a} {b} {c} (eval p) (eval q)) x)

mutual

  reflect : ∀ (a : Ty) → Ne' a →̇ ⟦ a ⟧
  reflect 𝟘 x       = dead x
  reflect 𝟙 x       = tt
  reflect 𝕓 x       = ne-𝕓 x
  reflect (a ⇒ b) f = λ τ x → reflect b (app (liftNe τ f) (reifyVal x))
  reflect (a * b) x = reflect a (fst x) , reflect b (snd x)
  reflect (a + b) x = branch x
    (leaf (inj₁ (reflect a (snd (sel iden)))))
    (leaf (inj₂ (reflect b (snd (sel iden)))))

  reifyVal : ∀ {a : Ty} → ⟦ a ⟧ →̇ Nf' a
  reifyVal {𝟘} t           = runTreeNf (map (cast (Nf' 𝟘)) t)
  reifyVal {𝟙} t           = unit
  reifyVal {𝕓} t           = t
  reifyVal {A ⇒ A₁} f      = abs (reifyVal (f (drop iden) (reflect A (snd (sel iden)))))
  reifyVal {T * A} (p , q) = pair (reifyVal p) (reifyVal q)
  reifyVal {A + B} t       = runTreeNf (map reifyValOr t)
  
  reifyValOr : ∀ {a b} → (⟦ a ⟧ +' ⟦ b ⟧) →̇ Nf' (a + b)
  reifyValOr (inj₁ x) = injl (reifyVal x)
  reifyValOr (inj₂ y) = injr (reifyVal y)

reflectᵢ : ∀ (a : Ty) → ⟦ a ⟧ .In a
reflectᵢ A = reflect A (sel iden)

reify : ∀ {a b : Ty} → (⟦ a ⟧ →̇ ⟦ b ⟧) → Nf a b
reify {T} f = reifyVal (f (reflectᵢ T))
    
norm : ∀ {a : Ty} → BCC' a →̇ Nf' a
norm t = reify (eval t)

-- quotations
mutual

  qₓ : ∀ {a} → Ne' a →̇ BCC' a
  qₓ (sel x)   = liftBCC x id
  qₓ (fst x)   = π₁ ∘ qₓ x
  qₓ (snd x)   = π₂ ∘ qₓ x
  qₓ (app x n) = apply ∘ < qₓ x , q n >

  q : ∀ {a} → Nf' a →̇ BCC' a
  q unit          = unit
  q (ne-𝕓 x)      = qₓ x
  q (ne-⊥ x)      = init ∘ qₓ x
  q (injl n)      = injl ∘ q n
  q (injr n)      = injr ∘ q n
  q (pair n n₁)   = < q n , q n₁ >
  q (abs n)       = curry (q n)
  q (case x n n₁) = caseM (qₓ x) (q n) (q n₁)
