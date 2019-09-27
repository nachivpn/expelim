-------------------------------------------------------------------------
-- Categorical account of exponential elimination (using free categories)
-------------------------------------------------------------------------

-- Stdlib imports
open import Level using (0ℓ)
open import Data.Product using (Σ ; proj₁ ; proj₂ ; _,_)
open import Data.Unit using (⊤)

-- Local imports
open import Type using (Ty)
open import Util using (firstOrd)
open import BCC using (BCC ; _≈_ ; cong-∘)
open import DBC using (DBC ; qD)
open import NBE using (norm)
open import Main
  using (_≋_ ; embD ; expElim-pres-≈)

-- Categories-library imports
open import Categories.Category using (Category)
open import Categories.Adjoint
  using (_⊣_) renaming (Adjoint to Adj)
open import Categories.Functor
  using (Functor ; _∘F_) renaming (id to Id)
open import Categories.Category.SubCategory
  using (SubCat ; SubCategory)
open import Categories.Adjoint.Equivalence
  using ()
  renaming (⊣Equivalence to ⊣Eq)
open import Categories.NaturalTransformation
  using () renaming (NaturalTransformation to _→̇_)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (_≃_)
  renaming (NaturalIsomorphism to NatIso
    ; sym to ≃-sym)
open import Categories.Category.Equivalence
  using ()
  renaming (WeakInverse to WkInv
    ; StrongEquivalence to StrongEq)

open BCC.BCC
open BCC._≈_
open DBC.DBC

Category0 = Category 0ℓ 0ℓ 0ℓ

-- The Free BiCartesian Closed Category (Free BiCCC),
-- generated using the singleton graph containing a node 𝕓 (base type)
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

-- First-Order (full) subcategory of the Free BiCCC
FOSubFreeBiCCC : SubCat FreeBiCCC (Σ Ty firstOrd)
FOSubFreeBiCCC = record {
  U    = proj₁ ;
  R    = λ _ → ⊤ ; -- we want all the arrows in the subcategory
  Rid  = _ ;
  _∘R_ = _ }

-- First-Order Free BiCCC
FOFreeBiCCC : Category0
FOFreeBiCCC = SubCategory _ (FOSubFreeBiCCC)

-- The Free Distributive BiCartesian Category,
-- generated using the singleton graph containing a node 𝕓
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

open Functor

-- "Eliminator" functor from the First-Order Free BiCCC to
-- the Free Distributive BiCartesian Category
Eliminator : Functor FOFreeBiCCC FreeDistrBCC
--
-- object map: identity
F₀ Eliminator o       = o
--
-- morphism map: map morphisms to the quotation (qD) of their normal forms
F₁ Eliminator {_ , fa} {_ , fb}  (f , _) = qD fa fb (norm f)
--
-- Eliminator (id {a}) ≈ id (Eliminator {a})
identity Eliminator = sym (expElim-pres-≈ BCC.id)
--
-- Eliminator (g ∘ f) ≈ Eliminator g ∘ Eliminator f
homomorphism Eliminator {X} {Y} {Z} {f , _} {g , _} = trans
    (sym (expElim-pres-≈ (g ∘ f)))
    (cong-∘ (expElim-pres-≈ g) (expElim-pres-≈ f))
--
-- f ≈ g → Eliminator f ≈ Eliminator g
F-resp-≈ Eliminator {_} {_} {f , _} {g , _} p =
  trans (sym (expElim-pres-≈ f)) (trans p (expElim-pres-≈ g))

-- "Embedder" functor which embeds the Free Distributive BiCartesian Category
-- into the First-Order Free BiCCC
Embedder : Functor FreeDistrBCC FOFreeBiCCC
Embedder = record
             { F₀ = λ x → x
             ; F₁ = λ x → embD x , _
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = λ p → p
             }

open _→̇_

-- Natural transformations between the Identity functor
-- and the composition of Embedder and Eliminator

unit' : Id →̇ (Embedder ∘F Eliminator)
η       unit' (a , fa) = BCC.id , _
commute unit' (f , _)  = trans idl (sym (trans idr (sym (expElim-pres-≈ f))))

unit-back : (Embedder ∘F Eliminator) →̇ Id
η       unit-back _       = BCC.id , _
commute unit-back (f , _) = trans idl (sym (trans idr (expElim-pres-≈ f)))

unit-iso : Id ≃ (Embedder ∘F Eliminator)
NatIso.F⇒G unit-iso   = unit'
NatIso.F⇐G unit-iso   = unit-back
NatIso.iso unit-iso _ = record { isoˡ = idl ; isoʳ = idl }

counit' : (Eliminator ∘F Embedder) →̇ Id
η       counit' _ = DBC.id
commute counit' f = trans idl (sym (trans idr (expElim-pres-≈ (embD f))))

counit-back : Id →̇ (Eliminator ∘F Embedder)
η       counit-back _ = DBC.id
commute counit-back f = trans idl (trans (expElim-pres-≈ (embD f)) (sym idr))

counit-iso : (Eliminator ∘F Embedder) ≃ Id
NatIso.F⇒G counit-iso   = counit'
NatIso.F⇐G counit-iso   = counit-back
NatIso.iso counit-iso _ = record { isoˡ = idl ; isoʳ = idl }

-- Eliminator is the left adjoint of Embedder
ElEmAdj : Eliminator ⊣ Embedder
Adj.unit   ElEmAdj = unit'
Adj.counit ElEmAdj = counit'
Adj.zig    ElEmAdj = trans idl (sym (expElim-pres-≈ BCC.id))
Adj.zag    ElEmAdj = idl

-- Embedder is the weak inverse of Eliminator
ElEmWkInv : WkInv Eliminator Embedder
WkInv.F∘G≈id ElEmWkInv = counit-iso
WkInv.G∘F≈id ElEmWkInv = ≃-sym unit-iso

-- FOFreeBiCCC and FreeDistrBCC are equivalent categories
FODistrEq : StrongEq FOFreeBiCCC FreeDistrBCC
StrongEq.F FODistrEq            = Eliminator
StrongEq.G FODistrEq            = Embedder
StrongEq.weak-inverse FODistrEq = ElEmWkInv

-- Eliminator ⊣ Embedder is an adjoint equivalence
ElEmAdjEq : ⊣Eq Eliminator Embedder
⊣Eq.unit   ElEmAdjEq = unit-iso
⊣Eq.counit ElEmAdjEq = counit-iso
⊣Eq.zig    ElEmAdjEq = trans idl (sym (expElim-pres-≈ BCC.id))
