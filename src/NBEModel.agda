open import Type
open import Util
open import BCC
open import Sel
open import NBE
open import Presheaf

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong ; cong₂) renaming (sym to ≡-sym ; trans to ≡-trans)

open Tree

--------------------------
-- Category of selections
--------------------------

--
-- `keep` as an endo-functor on category of selections
--

Keep₀ : (c : Ty) → Ty → Ty
Keep₀ c b = b * c

Keep₁  : (c : Ty) → {a b : Ty} → Sel a b → Sel (Keep₀ c a) (Keep₀ c b)
Keep₁ c = keep

keep-pres-id : {a b : Ty} → Keep₁ b iden ≡ iden {a * b}
keep-pres-id = uniq-iden

keep-pres-∙ : {a b c : Ty}  {s₁ : Sel b a} {s₂ : Sel c b}
    → Keep₁ c (s₁ ∙ s₂) ≡ Keep₁ c s₁ ∙ Keep₁ c s₂
keep-pres-∙ = refl

--
-- the identity functor
--

Id : {a : Set} → a → a
Id x = x

Id₀ = Id ; Id₁ = Id

--
-- `drop iden` as a natural transformation from `Keep` to `Id`
--

-- natural in `c`
Dr : (c : Ty) → {a : Ty} → Sel (a * c) a
Dr c = drop iden

-- naturality condition
nat-Dr : {a b c : Ty} {s : Sel a b} →
  Id₁ s ∙ Dr c ≡ (Dr c ∙ Keep₁ c s)
nat-Dr = cong drop (≡-trans sel-idr (≡-sym sel-idl))

-- NOTES:
--
-- The category of selections can be modeled by
-- an arbitrary category 𝒞, with the following requirements:
-- ⋆ an endofunctor Keep on 𝒞
-- * a natural transformation Dr : Keep →̇ Id

-- Keep allows extension (_ * c),
-- while Dr allows us to undo the extension (π₁)

-- Q: looks like there's no need for an initial/terminal object in 𝒞?
-- TODO: model `embSel` the embedding functor from 𝒞 to BCC

------------------
-- Presheaf model
------------------

-- Functor laws of Ne' and Nf' presheafs

mutual

  ne-pres-id : {a b : Ty} → (n : Ne a b) → liftNe iden n ≡ n
  ne-pres-id (sel x) = cong sel (sel-idr)
  ne-pres-id (fst n) = cong fst (ne-pres-id n)
  ne-pres-id (snd n) = cong snd (ne-pres-id n)
  ne-pres-id (app n x) = cong₂ app (ne-pres-id n) (nf-pres-id x)

  nf-pres-id : {a b : Ty} → (n : Nf a b) → liftNf iden n ≡ n
  nf-pres-id unit         = refl
  nf-pres-id (ne-𝕓 x)     = cong ne-𝕓 (ne-pres-id x)
  nf-pres-id (ne-⊥ x)     = cong ne-⊥ (ne-pres-id x)
  nf-pres-id (injl n)     = cong injl (nf-pres-id n)
  nf-pres-id (injr n)     = cong injr (nf-pres-id n)
  nf-pres-id (pair m n)   = cong₂ pair (nf-pres-id m) (nf-pres-id n)
  nf-pres-id (abs n)      = cong abs (nf-pres-id n)
  nf-pres-id (case x m n) = cong₃ case (ne-pres-id x) (nf-pres-id m) (nf-pres-id n)

mutual

  ne-pres-∙ : {a b c d : Ty} {s₁ : Sel b a} {s₂ : Sel c b}
    → (n : Ne a d) → liftNe (s₁ ∙ s₂) n ≡ (liftNe s₂ (liftNe s₁ n))
  ne-pres-∙ {s₁ = s₁} (sel x) = cong sel (≡-sym (sel-assoc {x = x} {y = s₁}))
  ne-pres-∙ (fst n) = cong fst (ne-pres-∙ n)
  ne-pres-∙ (snd n) = cong snd (ne-pres-∙ n)
  ne-pres-∙ (app n x) = cong₂ app (ne-pres-∙ n) (nf-pres-∙ x)

  nf-pres-∙ : {a b c d : Ty} {s₁ : Sel b a} {s₂ : Sel c b}
    → (n : Nf a d) → liftNf (s₁ ∙ s₂) n ≡ (liftNf s₂ (liftNf s₁ n))
  nf-pres-∙ unit     = refl
  nf-pres-∙ (ne-𝕓 x) = cong ne-𝕓 (ne-pres-∙ x)
  nf-pres-∙ (ne-⊥ x) = cong ne-⊥ (ne-pres-∙ x)
  nf-pres-∙ (injl n) = cong injl (nf-pres-∙ n)
  nf-pres-∙ (injr n) = cong injr (nf-pres-∙ n)
  nf-pres-∙ (pair m n) = cong₂ pair (nf-pres-∙ m) (nf-pres-∙ n)
  nf-pres-∙ (abs n) = cong abs (nf-pres-∙ n)
  nf-pres-∙ (case x m n) = cong₃ case (ne-pres-∙ x) (nf-pres-∙ m) (nf-pres-∙ n)

-- Functor laws of an arbitrary presheaf

postulate
  𝒫-pres-id : {P : 𝒫} {a : Ty} {x : P .𝒫.In a}
    → 𝒫.lift P iden x ≡ x
  𝒫-pres-∙  : {P : 𝒫} {a b c : Ty}  {s₁ : Sel b a} {s₂ : Sel c b} {x : P .𝒫.In a}
    → 𝒫.lift P (s₁ ∙ s₂) x ≡ 𝒫.lift P s₂ (𝒫.lift P s₁ x)

-- Functor laws of the (Tree' B) presheaf, for some presheaf B

tree-pres-id : {a : Ty} {B : 𝒫} → (t : Tree a B) → liftTree iden t ≡ t
tree-pres-id {B = B} (leaf x)
  = cong leaf (𝒫-pres-id {B})
tree-pres-id (dead x)
  = cong dead (ne-pres-id x)
tree-pres-id (branch x t₁ t₂)
  = cong₃ branch (ne-pres-id x) (tree-pres-id t₁) (tree-pres-id t₂)

tree-pres-∙ : {D : 𝒫} {a b c : Ty}  {s₁ : Sel b a} {s₂ : Sel c b}
    → (t : Tree a D) → liftTree (s₁ ∙ s₂) t ≡ (liftTree s₂ (liftTree s₁ t))
tree-pres-∙ {D} (leaf x)
  = cong leaf (𝒫-pres-∙ {D})
tree-pres-∙ (dead x)
  = cong dead (ne-pres-∙ x)
tree-pres-∙ (branch x t₁ t₂)
  = cong₃ branch (ne-pres-∙ x) (tree-pres-∙ t₁) (tree-pres-∙ t₂)
