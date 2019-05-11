open import Sel
open import Type
open import NBE

-- Subformula stuff

data _⊲_ : Ty → Ty → Set where
  self : ∀{a} → a ⊲ a
  subl  : {a b c : Ty} (_o_ : Ty → Ty → Ty) → a ⊲ b → a ⊲ (b o c)
  subr  : {a b c : Ty} (_o_ : Ty → Ty → Ty) → a ⊲ c → a ⊲ (b o c)
  subp  : {a b c d : Ty} → a ⊲ c → b ⊲ d → (a * b) ⊲ (c * d)

mutual

  neutrality : ∀{A B} → Ne A B → B ⊲ A
  neutrality (sel p)   = neutr-sel p
  neutrality (fst n)   = PSf-p₁ (neutrality n)
  neutrality (snd n)   = PSf-p₂ (neutrality n)
  neutrality (app n _) = PSf-exp (neutrality n)

  neutr-sel : ∀{A B} → Sel A B → B ⊲ A
  neutr-sel end𝟙     = self
  neutr-sel end𝕓     = self
  neutr-sel end𝟘     = self
  neutr-sel end⇒     = self
  neutr-sel end+     = self
  neutr-sel (drop p) = subl _*_ (neutr-sel p)
  neutr-sel (keep p) = subp (neutr-sel p) self

  PSf-p₁ : ∀ {B C A} → (B * C) ⊲ A → B ⊲ A
  PSf-p₁ self         = subl _*_ self
  PSf-p₁ (subl _o_ p) = subl _o_ (PSf-p₁ p)
  PSf-p₁ (subr _o_ p) = subr _o_ (PSf-p₁ p)
  PSf-p₁ (subp p q)   = subl _*_ p

  PSf-p₂ : ∀ {B C A} → (B * C) ⊲ A → C ⊲ A
  PSf-p₂ self         = subr _*_ self
  PSf-p₂ (subl _o_ p) = subl _o_ (PSf-p₂ p)
  PSf-p₂ (subr _o_ p) = subr _o_ (PSf-p₂ p)
  PSf-p₂ (subp p q)   = subr _*_ q

  PSf-exp : ∀ {B C A} → (B ⇒ C) ⊲ A → C ⊲ A
  PSf-exp self         = subr _⇒_ self
  PSf-exp (subl _o_ p) = subl _o_ (PSf-exp p)
  PSf-exp (subr _o_ p) = subr _o_ (PSf-exp p)
