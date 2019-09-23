-------------------------------------------------------------------------
-- Categorical account of exponential elimination (using free categories)
-------------------------------------------------------------------------

-- Stdlib imports
open import Level
  using (0ℓ)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit
  using (⊤)

-- Local imports
open import Type
  using (Ty)
open import Util
  using (firstOrd)
open import BCC
  using (BCC ; _≈_ ; cong-∘)
open import DBC
  using (DBC ; qD)
open import NBE
  using (norm)
open import Main
  using (_≋_ ; embD)
  renaming (main to expElim)

-- Categories-library imports
open import Categories.Category
  using (Category)
open import Categories.Functor
  using (Functor)
open import Categories.Category.SubCategory
  using (SubCat ; SubCategory)

open BCC.BCC
open BCC._≈_
open DBC.DBC

Category0 = Category 0ℓ 0ℓ 0ℓ

-- The Free BiCartesian Closed Category (Free BiCCC), generated over set 𝕓
FreeBiCCC : Category0
FreeBiCCC = record
              { Obj = Ty
              ; _⇒_ = BCC
              ; _≈_ = _≈_
              ; id  = id
              ; _∘_ = _∘_
              ; assoc     = sym (assoc)
              ; identityˡ = idl
              ; identityʳ = idr
              ; equiv     = record {
                refl      = refl ;
                sym       = sym ;
                trans     = trans }
              ; ∘-resp-≈  = cong-∘
              }

-- First-Order subcategory of the Free BiCCC
FOSubFreeBiCCC : SubCat FreeBiCCC (Σ Ty firstOrd)
FOSubFreeBiCCC = record {
  U    = proj₁ ;
  R    = λ _ → ⊤ ; -- we want all the arrows in the subcategory
  Rid  = _ ;
  _∘R_ = _ }

-- First-Order Free BiCCC
FOFreeBiCC : Category0
FOFreeBiCC = SubCategory _ (FOSubFreeBiCCC)

-- The Free Distributive BiCartesian Category, generated over set 𝕓
FreeDistrBCC : Category0
FreeDistrBCC = record
              { Obj = Σ Ty firstOrd
              ; _⇒_ = λ { (a , _) (b , _) → DBC a b }
              ; _≈_ = λ f g → embD f ≈ embD g
              ; id  = id
              ; _∘_ = _∘_
              ; assoc     = sym (assoc)
              ; identityˡ = idl
              ; identityʳ = idr
              ; equiv     = record {
                refl      = refl ;
                sym       = sym ;
                trans     = trans }
              ; ∘-resp-≈  = cong-∘
              }

-- "Eliminator" functor from the First-Order Free BiCCC to
-- the Free Distributive BiCartesian Category
Eliminator : Functor FOFreeBiCC FreeDistrBCC
Eliminator = record

      { -- object map: identity
        F₀           = λ x → x

        -- morphism map: map morphisms to the quotation (qD) of their normal forms
      ; F₁           = λ { {_ , fa} {_ , fb} (f , _) → qD fa fb (norm f) }

        -- Eliminator (id {a}) ≈ id (Eliminator {a})
      ; identity     = sym (proj₂ (expElim _ _ BCC.id))

        -- Eliminator (g ∘ f) ≈ Eliminator g ∘ Eliminator f
      ; homomorphism =  λ { {_} {_} {_} {f , _} {g , _} →
        let
          (g'∘f' , expElim_gf) = expElim _ _ (g ∘ f)  -- g ∘ f ≋ g' ∘ f'
          (f' , expElim_f)     = expElim _ _ f        -- f ≋ f'
          (g' , expElim_g)     = expElim _ _ g        -- g ≋ g'
        in trans (sym expElim_gf) (cong-∘ expElim_g  expElim_f) }

        -- f ≈ g → Eliminator f ≈ Eliminator g
      ; F-resp-≈     = λ { {_} {_} {f , _} {g , _} p →
          let
            (f' , expElim_f) = (expElim _ _ f)  -- f ≋ f'
            (g' , expElim_g) = (expElim _ _ g)  -- g ≋ g'
          in trans (sym expElim_f) (trans p expElim_g) }
      }

-- "Embedder" functor which embeds the Free Distributive BiCartesian Category
-- into the First-Order Free BiCCC
Embedder : Functor FreeDistrBCC FOFreeBiCC
Embedder = record
             { F₀ = λ x → x
             ; F₁ = λ x → embD x , _
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = λ p → p
             }
-- Q: Is "Embedder" a forgetful functor?
