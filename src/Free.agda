-------------------------------------------------------------------------
-- Categorical account of exponential elimination (using free categories)
-------------------------------------------------------------------------

-- Stdlib imports
open import Level using (0ℓ)
open import Data.Product
  using (Σ ; proj₁ ; proj₂ ; _,_ ; ∃)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_)
  renaming (sym to ≡-sym ; cong₂ to ≡-cong₂)

-- Local imports
open import Type using (Ty)
open import Util using (firstOrd)
open import BCC using (BCC ; _≈_ ; cong-∘)
open import DBC using (DBC ; qD)
open import NBE using (norm ; q)
open import Main
  using (_≋_ ; embD ; q≣qD)
  renaming (main to expElim)
open import Correct using (correctNorm)

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
FBiCCC : Category0
FBiCCC = record
              { Obj = Ty
              ; _⇒_ = BCC
              ; _≈_ = _≈_
              ; id  = id
              ; _∘_ = _∘_
              ; assoc     = sym (assoc)
              ; sym-assoc = assoc
              ; identityˡ = idl
              ; identityʳ = idr
              ; equiv     = record {
                refl      = refl ;
                sym       = sym ;
                trans     = trans }
              ; ∘-resp-≈  = cong-∘
              }

-- First-Order *full* subcategory of the Free BiCCC
FOSub : SubCat FBiCCC (Σ Ty firstOrd)
FOSub = record {
  U    = proj₁ ;
  R    = λ _ → ⊤ ; -- we want all the arrows in the subcategory
  Rid  = _ ;
  _∘R_ = _ }

-- "First-Order Free BiCCC"
FOFBiCCC : Category0
FOFBiCCC = SubCategory _ (FOSub)

-- Distributive subcategory of the Free BiCCC
-- this subcategory is not full!
DistrSub : SubCat FBiCCC (Σ Ty firstOrd)
DistrSub = record {
  U    = proj₁ ;
  R    = λ t → Σ (DBC _ _) (λ t' → t ≡ embD t') ; -- only arrows which can be syntactically encoded as DBC terms
  Rid  = id , _≡_.refl ;
  _∘R_ = λ {(f , p) (g , q) → (f ∘ g) , ≡-cong₂ _∘_ p q} }

-- "Distributive Free BiCCC"
-- Note: This is need not be the free distributive category since
--       it enjoys a richer eq. theory, i.e., _≈_ of FBiCCC
DistrFBiCCC : Category0
DistrFBiCCC = SubCategory _ DistrSub

open Functor

-- "Eliminator" functor from the First-Order Free BiCCC to
-- the Distributive Free BiCCC
Eliminator : Functor FOFBiCCC DistrFBiCCC
--
-- object map: identity
F₀ Eliminator o = o
--
-- morphism map: map morphisms to the quotation (qD) of their normal forms
F₁ Eliminator {_ , fa} {_ , fb} (f , _) =
  let n = norm f
  in q n , qD fa fb n , q≣qD _ _ n
--
-- Eliminator (id {a}) ≈ id (Eliminator {a})
identity Eliminator = sym (correctNorm id)
--
-- Eliminator (g ∘ f) ≈ Eliminator g ∘ Eliminator f
homomorphism Eliminator {X} {Y} {Z} {f , _} {g , _} =
  trans (sym (correctNorm (g ∘ f))) (cong-∘ (correctNorm g) (correctNorm f))
--
-- f ≈ g → Eliminator f ≈ Eliminator g
F-resp-≈ Eliminator {_} {_} {f , _} {g , _} p =
  trans (sym (correctNorm f)) (trans p (correctNorm g))

-- "Embedder" functor which embeds the Distributive Free BiCCC
-- into the First-Order Free BiCCC
Embedder : Functor DistrFBiCCC FOFBiCCC
Embedder = record
             { F₀ = λ x → x
             ; F₁ = λ { (f , _) → f , _ }
             ; identity = refl
             ; homomorphism = refl
             ; F-resp-≈ = λ p → p
             }

open _→̇_

-- Natural transformations between the Identity functor
-- and the composition of Embedder and Eliminator

unit' : Id →̇ (Embedder ∘F Eliminator)
η       unit' (a , fa) = BCC.id , _
commute unit' (f , _)  = trans idl (sym (trans idr (sym (correctNorm f))))

unit-back : (Embedder ∘F Eliminator) →̇ Id
η       unit-back _       = BCC.id , _
commute unit-back (f , _) = trans idl (sym (trans idr (correctNorm f)))

unit-iso : Id ≃ (Embedder ∘F Eliminator)
NatIso.F⇒G unit-iso   = unit'
NatIso.F⇐G unit-iso   = unit-back
NatIso.iso unit-iso _ = record { isoˡ = idl ; isoʳ = idl }

counit' : (Eliminator ∘F Embedder) →̇ Id
η       counit' x       = id , id , _≡_.refl
commute counit' (f , _) = trans idl (sym (trans idr (correctNorm f)))

counit-back : Id →̇ (Eliminator ∘F Embedder)
η       counit-back _       = id , id , _≡_.refl
commute counit-back (f , _) = trans idl (trans (correctNorm f) (sym idr))

counit-iso : (Eliminator ∘F Embedder) ≃ Id
NatIso.F⇒G counit-iso   = counit'
NatIso.F⇐G counit-iso   = counit-back
NatIso.iso counit-iso _ = record { isoˡ = idl ; isoʳ = idl }

-- Eliminator is the left adjoint of Embedder
ElEmAdj : Eliminator ⊣ Embedder
Adj.unit   ElEmAdj = unit'
Adj.counit ElEmAdj = counit'
Adj.zig    ElEmAdj = trans idl (sym (correctNorm id))
Adj.zag    ElEmAdj = idl

-- Embedder is the weak inverse of Eliminator
ElEmWkInv : WkInv Eliminator Embedder
WkInv.F∘G≈id ElEmWkInv = counit-iso
WkInv.G∘F≈id ElEmWkInv = ≃-sym unit-iso

-- FOFBiCCC and DistrFBiCCC are equivalent categories
FODistrEq : StrongEq FOFBiCCC DistrFBiCCC
StrongEq.F FODistrEq            = Eliminator
StrongEq.G FODistrEq            = Embedder
StrongEq.weak-inverse FODistrEq = ElEmWkInv

-- Eliminator ⊣ Embedder is an adjoint equivalence
ElEmAdjEq : ⊣Eq Eliminator Embedder
⊣Eq.unit   ElEmAdjEq = unit-iso
⊣Eq.counit ElEmAdjEq = counit-iso
⊣Eq.zig    ElEmAdjEq = trans idl (sym (correctNorm id))
