{-# OPTIONS --allow-unsolved-metas #-}

module DBC where


open import Sel
open import NBE
open import BCC
open import Type
open import Util
open import Data.Unit using (tt)

data DBC : (a b : Ty) → Set where

  -- Category morphisms
  id : ∀ {a} → DBC a a
  _∘_ : ∀ {a b c} → DBC b c → DBC a b → DBC a c

  -- Product morphisms
  π₁    : ∀ {a b} → DBC (a * b) a
  π₂    : ∀ {a b} → DBC (a * b) b
  <_,_> : ∀ {a b c} → DBC a b → DBC a c → DBC a (b * c)

  -- Initial morphism
  init : ∀ {a} → DBC 𝟘 a

  -- Terminal morphism
  unit : ∀ {a} → DBC a 𝟙

  -- co-product morphisms
  injl  : ∀ {a b} → DBC a (a + b)
  injr  : ∀ {a b} → DBC b (a + b)
  [_,_] : ∀ {a b c} → DBC a c → DBC b c → DBC (a + b) c

  -- distributivity (needed for qD)
  distr : ∀ {a b c} →  DBC (a * (b + c)) ((a * b) + (a * c))

selSafety : ∀ {a b} → notFun a → Sel a b → notFun b
selSafety p end𝟙     = tt
selSafety p end𝕓     = tt
selSafety p end𝟘     = tt
selSafety p end⇒     = p
selSafety p end+     = p
selSafety p (drop e) = selSafety (proj₁ p) e
selSafety p (keep e) = selSafety (proj₁ p) e , (proj₂ p)

neutralSafety : ∀{a b} → notFun a → Ne a b → notFun b
neutralSafety p (fst n)   = proj₁ (neutralSafety p n)
neutralSafety p (snd n)   = proj₂ (neutralSafety p n)
neutralSafety p (app n x) with neutralSafety p n
...                       | ()
neutralSafety p (sel x)   = selSafety p x

embSelD : ∀{a b : Ty} → Sel a b → DBC a b
embSelD end𝟙     = id
embSelD end𝕓     = id
embSelD end𝟘     = id
embSelD end⇒     = id
embSelD end+     = id
embSelD (drop e) = embSelD e ∘ π₁
embSelD (keep e) = < embSelD e ∘ π₁ , π₂ >

mutual

  qD : ∀{A B : Ty} → notFun A → notFun B → Nf A B → DBC A B
  qD p q (ne-⊥ x)    = init ∘ qNeD p x
  qD p q unit        = unit
  qD p q (ne-𝕓 x)    = qNeD p x
  qD p q (injl n)    = injl ∘ qD p (proj₁ q) n
  qD p q (injr n)    = injr ∘ qD p (proj₂ q) n
  qD p q (pair n n₁) = < qD p (proj₁ q) n , qD p (proj₂ q) n₁ >
  qD p () (abs n)
  qD p q (case x m n) = ([ m' , n' ] ∘ distr) ∘ < id , x' >
    where
    x' = qNeD p x
    m' = qD (p , proj₁ (neutralSafety p x)) q m
    n' = qD (p , proj₂ (neutralSafety p x)) q n

  qNeD : ∀{A B : Ty} → notFun A → Ne A B → DBC A B
  qNeD p (fst n)   = π₁ ∘ (qNeD p n)
  qNeD p (snd n)   = π₂ ∘ (qNeD p n)
  qNeD p (app n x) with neutralSafety p n
  ...                 | ()
  qNeD p (sel x)   = embSelD x

