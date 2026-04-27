-- This is an attempt at writing the iterator for the non-split notion of model, very transport heavy
-- by Kaposi Ambrus

{-# OPTIONS --rewriting #-}

open import Agda.Primitive
open import Lib
open import model
open import Syntax

module Iterator
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  {i}{j}{k}
  (M : Model funar relar {i}{j}{k})
  where

module M = Model M

cong-,ₚ : ∀{Γ Δ}{γ γ' : M.Sub Δ Γ} → γ ≡ γ' → ∀{A}{a : M.Pf Δ (A M.[ γ ]ᶠ)}{a' : M.Pf Δ (A M.[ γ' ]ᶠ)} → γ M.,ₚ a ≡ γ' M.,ₚ a'
cong-,ₚ refl = refl

subst-[]ᶠ : ∀{Γ}{A : M.For Γ}{Δ}{γ : M.Sub Δ Γ}{Δ'}(e : Δ ≡ Δ') →
  subst M.For e (A M.[ γ ]ᶠ) ≡ A M.[ subst (λ z → M.Sub z Γ) e γ ]ᶠ
subst-[]ᶠ refl = refl

,ₜ∘ : ∀{Γ Δ}{γ : M.Sub Δ Γ}{t : M.Tm Δ}{Θ}{δ : M.Sub Θ Δ} →
  (γ M.,ₜ t) M.∘ δ ≡ γ M.∘ δ M.,ₜ (t M.[ δ ]ᵗ)
,ₜ∘ {γ = γ}{δ = δ} = M.▹ₜη ◾ cong₂ M._,ₜ_ (M.ass ⁻¹ ◾ cong (M._∘ δ) M.▹ₜβ₁) (M.[∘]ᵗ ◾ cong (M._[ δ ]ᵗ) M.▹ₜβ₂)

,ₚ∘ : ∀{Γ Δ}{γ : M.Sub Δ Γ}{A}{a : M.Pf Δ (A M.[ γ ]ᶠ)}{Θ}{δ : M.Sub Θ Δ} →
  (γ M.,ₚ a) M.∘ δ ≡ γ M.∘ δ M.,ₚ substP (M.Pf Θ) (M.[∘]ᶠ ⁻¹) (a M.[ δ ]ᵖ)
,ₚ∘ {Γ}{Δ}{γ}{A}{a}{Θ}{δ} = M.▹ₚη ◾ cong-,ₚ (M.ass ⁻¹ ◾ cong (M._∘ δ) M.▹ₚβ₁)

data Fors (Γ : M.Con) : Set i
_▹ₚₛ_ : (Γ : M.Con) → Fors Γ → M.Con
data Fors Γ where
  ◇    : Fors Γ
  _▹ₚ_ : (As : Fors Γ) → M.For (Γ ▹ₚₛ As) → Fors Γ
Γ ▹ₚₛ ◇         = Γ
Γ ▹ₚₛ (As ▹ₚ A) = (Γ ▹ₚₛ As) M.▹ₚ A

cong-▹ₚ : ∀{Γ}{As As' : Fors Γ}(e : As ≡ As'){A : M.For (Γ ▹ₚₛ As)}{A' : M.For (Γ ▹ₚₛ As')} →
  subst (λ z → M.For (Γ ▹ₚₛ z)) e A ≡ A' → As ▹ₚ A ≡ As' ▹ₚ A'
cong-▹ₚ refl refl = refl

_[_]ᶠˢ  : ∀{Γ} → Fors Γ → ∀{Δ} → M.Sub Δ Γ → Fors Δ
_⁺ᵖˢ_   : ∀{Γ Δ}(γ : M.Sub Δ Γ)(As : Fors Γ) → M.Sub (Δ ▹ₚₛ (As [ γ ]ᶠˢ)) (Γ ▹ₚₛ As)
◇         [ γ ]ᶠˢ = ◇
(As ▹ₚ A) [ γ ]ᶠˢ = As [ γ ]ᶠˢ ▹ₚ A M.[ γ ⁺ᵖˢ As ]ᶠ
γ ⁺ᵖˢ ◇         = γ
γ ⁺ᵖˢ (As ▹ₚ A) = γ ⁺ᵖˢ As M.∘ M.pₚ M.,ₚ substP (M.Pf _) (M.[∘]ᶠ ⁻¹) M.qₚ

[∘]ᶠˢ  : ∀{Γ As}{Δ}{γ : M.Sub Δ Γ}{Θ}{δ : M.Sub Θ Δ} → As [ γ M.∘ δ ]ᶠˢ ≡ As [ γ ]ᶠˢ [ δ ]ᶠˢ
∘⁺ᵖˢ   : ∀{Γ As}{Δ}{γ : M.Sub Δ Γ}{Θ}{δ : M.Sub Θ Δ} →
  subst (λ z → M.Sub (Θ ▹ₚₛ z) (Γ ▹ₚₛ As)) ([∘]ᶠˢ {As = As}) ((γ M.∘ δ) ⁺ᵖˢ As) ≡ (γ ⁺ᵖˢ As) M.∘ (δ ⁺ᵖˢ (As [ γ ]ᶠˢ))
[∘]ᶠˢ {As = ◇} = refl
[∘]ᶠˢ {As = As ▹ₚ A}{γ = γ}{Θ}{δ} = cong-▹ₚ
  ([∘]ᶠˢ {As = As})
  (subst-[]ᶠ {A = A}{γ = (γ M.∘ δ) ⁺ᵖˢ As} (cong (Θ ▹ₚₛ_) ([∘]ᶠˢ {As = As}{γ = γ}{δ = δ})) ◾ cong (A M.[_]ᶠ) (∘⁺ᵖˢ  {As = As}) ◾ M.[∘]ᶠ)
∘⁺ᵖˢ {As = ◇} = refl
∘⁺ᵖˢ {As = As ▹ₚ A}{γ = γ}{Θ}{δ} = {!(∘⁺ᵖˢ {As = As} {γ = γ}{δ = δ})!}
[id]ᶠˢ : ∀{Γ}{As : Fors Γ} → As [ M.id ]ᶠˢ ≡ As
id⁺ᵖˢ  : ∀{Γ}{As : Fors Γ} → subst (λ z → M.Sub (Γ ▹ₚₛ z) (Γ ▹ₚₛ As)) ([id]ᶠˢ {As = As}) (M.id ⁺ᵖˢ As) ≡ M.id
[id]ᶠˢ {Γ} {◇} = refl
[id]ᶠˢ {Γ} {As ▹ₚ A} = cong-▹ₚ
  ([id]ᶠˢ {As = As})
  ({!subst-[]ᶠ {A = A}{γ = M.id ⁺ᵖˢ As}!} ◾ cong (A M.[_]ᶠ) (id⁺ᵖˢ {As = As}) ◾ M.[id]ᶠ)
id⁺ᵖˢ {Γ}{As} = {!!}

Pfs : (Γ : M.Con) → Fors Γ → Prop k
⟨_⟩ᵖˢ : ∀{Γ As} → Pfs Γ As → M.Sub Γ (Γ ▹ₚₛ As)
Pfs Γ ◇ = 𝟙p
Pfs Γ (As ▹ₚ A) = Σp (Pfs Γ As) λ as → M.Pf Γ (A M.[ ⟨ as ⟩ᵖˢ ]ᶠ)
⟨_⟩ᵖˢ {Γ} {◇}       _        = M.id
⟨_⟩ᵖˢ {Γ} {As ▹ₚ A} (as ,p a) = ⟨ as ⟩ᵖˢ M.,ₚ a

_[_]ᵖˢ : ∀{Γ As Δ} → Pfs Γ As → (γ : M.Sub Δ Γ) → Pfs Δ (As [ γ ]ᶠˢ)
⁺⟨⟩ᵖˢ  : ∀{Γ As Δ}{as : Pfs Γ As}{γ : M.Sub Δ Γ} → (γ ⁺ᵖˢ As) M.∘ ⟨ as [ γ ]ᵖˢ ⟩ᵖˢ ≡ ⟨ as ⟩ᵖˢ M.∘ γ
_[_]ᵖˢ {As = ◇}       _         γ = tt
_[_]ᵖˢ {As = As ▹ₚ A} (as ,p a) γ = (as [ γ ]ᵖˢ) ,p substP (M.Pf _) (M.[∘]ᶠ ⁻¹ ◾ cong (A M.[_]ᶠ) (⁺⟨⟩ᵖˢ {As = As} ⁻¹) ◾ M.[∘]ᶠ) (a M.[ γ ]ᵖ)
⁺⟨⟩ᵖˢ {As = ◇} = M.idr ◾ M.idl ⁻¹
⁺⟨⟩ᵖˢ {Γ}{As ▹ₚ A}{Δ}{as ,p a}{γ} = ,ₚ∘ ◾ cong-,ₚ (M.ass ◾ cong ((γ ⁺ᵖˢ As) M.∘_) M.▹ₚβ₁ ◾ ⁺⟨⟩ᵖˢ {As = As}) ◾ ,ₚ∘ ⁻¹

pₚₛ : ∀{Γ As} → M.Sub (Γ ▹ₚₛ As) Γ
pₚₛ {As = ◇}       = M.id
pₚₛ {As = As ▹ₚ A} = pₚₛ {As = As} M.∘ M.pₚ

qₚₛ : ∀{Γ As} → Pfs (Γ ▹ₚₛ As) (As [ pₚₛ {As = As} ]ᶠˢ)
▹ₚₛη : ∀{Γ As} → (pₚₛ {As = As} ⁺ᵖˢ As) M.∘ ⟨ qₚₛ {As = As} ⟩ᵖˢ ≡ M.id {Γ ▹ₚₛ As}
qₚₛ {As = ◇}       = tt
qₚₛ {As = As ▹ₚ A} = substP (Pfs _) ([∘]ᶠˢ ⁻¹) (qₚₛ {As = As} [ M.pₚ ]ᵖˢ) ,p
  substP (M.Pf _)
         (cong (A M.[_]ᶠ) {!? ◾ ⁺⟨⟩ᵖˢ {As = As}{γ = pₚₛ M.∘ M.pₚ} ⁻¹!} ◾ M.[∘]ᶠ)
         M.qₚ
▹ₚₛη {As = As} = {!!}

_,ₚₛ_ : ∀{Γ Δ}(γ : M.Sub Δ Γ){As}(as : Pfs Δ (As [ γ ]ᶠˢ)) → M.Sub Δ (Γ ▹ₚₛ As)
_,ₚₛ_ γ {As} as = (γ ⁺ᵖˢ As) M.∘ ⟨ as ⟩ᵖˢ

module S = Syntax funar relar
module I = Model S.I

⟦_⟧Ct : S.Con → M.Con
⟦ ◇ ⟧Ct = M.◇
⟦ Γ ▹ₜ ⟧Ct = ⟦ Γ ⟧Ct M.▹ₜ

⟦_⟧F' : ∀{Γₜ} → S.For Γₜ → M.For ⟦ Γₜ ⟧Ct

⟦_⟧Cp : ∀{Γₜ} → S.Conp Γₜ → Fors ⟦ Γₜ ⟧Ct
⟦ ◇ₚ ⟧Cp = ◇
⟦ Γₚ ▹ₚ A ⟧Cp = ⟦ Γₚ ⟧Cp ▹ₚ ⟦ A ⟧F' M.[ pₚₛ {As = ⟦ Γₚ ⟧Cp} ]ᶠ

⟦_⟧T' : ∀{Γₜ} → S.Tm Γₜ → M.Tm ⟦ Γₜ ⟧Ct
⟦_⟧Ts' : ∀{n Γₜ} → S.Tm Γₜ ^ n → M.Tm ⟦ Γₜ ⟧Ct ^ n
⟦ var vz ⟧T' = M.qₜ
⟦ var (vs x) ⟧T' = ⟦ var x ⟧T' M.[ M.pₜ ]ᵗ
⟦ fun ar ts ⟧T' = M.fun ar ⟦ ts ⟧Ts'
⟦_⟧Ts' {zero} ts = _
⟦_⟧Ts' {suc n} (t , ts) = ⟦ t ⟧T' , ⟦ ts ⟧Ts'

⟦ A ⊃ B ⟧F' = ⟦ A ⟧F' M.⊃ ⟦ B ⟧F'
⟦ A ∧ B ⟧F' = ⟦ A ⟧F' M.∧ ⟦ B ⟧F'
⟦ ⊤ ⟧F' = M.⊤
⟦ A ∨ B ⟧F' = ⟦ A ⟧F' M.∨ ⟦ B ⟧F'
⟦ ⊥ ⟧F' = M.⊥
⟦ Forall A ⟧F' = M.Forall ⟦ A ⟧F'
⟦ ∃ A ⟧F' = M.∃ ⟦ A ⟧F'
⟦ Rel ar ts ⟧F' = M.Rel ar ⟦ ts ⟧Ts'

⟦_⟧C : I.Con → M.Con
⟦ Γₜ , Γₚ ⟧C = ⟦ Γₜ ⟧Ct ▹ₚₛ ⟦ Γₚ ⟧Cp

⟦_⟧F : ∀{Γ} → I.For Γ → M.For ⟦ Γ ⟧C
⟦_⟧F {Γₜ , Γₚ} A = ⟦ A ⟧F' M.[ pₚₛ {As = ⟦ Γₚ ⟧Cp} ]ᶠ

⟦_⟧st : ∀{Δₜ Γₜ}(γₜ : S.Sub Δₜ Γₜ) → M.Sub ⟦ Δₜ ⟧Ct ⟦ Γₜ ⟧Ct
⟦ ε ⟧st = M.ε
⟦ γₜ ,ₜ t ⟧st = ⟦ γₜ ⟧st M.,ₜ ⟦ t ⟧T'

⟦[]⟧ts : ∀{Γₜ}{n}{ts : S.Tm Γₜ ^ n}{Δₜ}{γₜ : S.Sub Δₜ Γₜ} → ⟦ ts S.[ γₜ ]ᵗs ⟧Ts' ≡ map (M._[ ⟦ γₜ ⟧st ]ᵗ) ⟦ ts ⟧Ts'
⟦[]⟧t : ∀{Γₜ}{t : S.Tm Γₜ}{Δₜ}{γₜ : S.Sub Δₜ Γₜ} → ⟦ t S.[ γₜ ]ᵗ ⟧T' ≡ ⟦ t ⟧T' M.[ ⟦ γₜ ⟧st ]ᵗ
⟦[]⟧ts {n = zero} = refl
⟦[]⟧ts {n = suc n}{t , ts} = cong₂ _,_ (⟦[]⟧t {t = t}) (⟦[]⟧ts {n = n})
⟦[]⟧t {t = var vz}{γₜ = γₜ ,ₜ t} = M.▹ₜβ₂ ⁻¹
⟦[]⟧t {t = var (vs x)}{γₜ = γₜ ,ₜ t} = ⟦[]⟧t {t = var x} ◾ cong (⟦ S.var x ⟧T' M.[_]ᵗ) (M.▹ₜβ₁ ⁻¹) ◾ M.[∘]ᵗ
⟦[]⟧t {t = fun ar ts} = cong (M.fun ar) (⟦[]⟧ts {ts = ts}) ◾ M.fun[] ⁻¹

⟦pₜ⟧ : ∀{Γₜ} → ⟦ S.pₜ {Γₜ} ⟧st ≡ M.pₜ
⟦pₜ⟧ {◇} = M.◇η ⁻¹
⟦pₜ⟧ {Γₜ ▹ₜ} = {!!}

⟦∘⟧st : ∀{Δₜ Γₜ}{γₜ : S.Sub Δₜ Γₜ}{Θₜ}{δₜ : S.Sub Θₜ Δₜ} → ⟦ γₜ S.∘ δₜ ⟧st ≡ ⟦ γₜ ⟧st M.∘ ⟦ δₜ ⟧st
⟦∘⟧st {γₜ = ε} = M.◇η ⁻¹
⟦∘⟧st {γₜ = γₜ ,ₜ t}{δₜ = δₜ} = cong₂ M._,ₜ_ (⟦∘⟧st {γₜ = γₜ}{δₜ = δₜ}) (⟦[]⟧t {t = t}{γₜ = δₜ}) ◾ ,ₜ∘ {t = ⟦ t ⟧T'} ⁻¹

⟦[]⟧F : ∀{Γₜ}{A : S.For Γₜ}{Δₜ}{γₜ : S.Sub Δₜ Γₜ} → ⟦ A S.[ γₜ ]ᶠ ⟧F' ≡ ⟦ A ⟧F' M.[ ⟦ γₜ ⟧st ]ᶠ
⟦[]⟧F {A = A ⊃ B} = cong₂ M._⊃_ (⟦[]⟧F {A = A}) (⟦[]⟧F {A = B}) ◾ M.⊃[] ⁻¹
⟦[]⟧F {A = A ∧ B} = cong₂ M._∧_ (⟦[]⟧F {A = A}) (⟦[]⟧F {A = B}) ◾ M.∧[] ⁻¹
⟦[]⟧F {A = ⊤} = M.⊤[] ⁻¹
⟦[]⟧F {A = A ∨ B} = cong₂ M._∨_ (⟦[]⟧F {A = A}) (⟦[]⟧F {A = B}) ◾ M.∨[] ⁻¹
⟦[]⟧F {A = ⊥} = M.⊥[] ⁻¹
⟦[]⟧F {A = Forall A}{γₜ = γₜ} = cong M.Forall (⟦[]⟧F {A = A} ◾ cong (⟦ A ⟧F' M.[_]ᶠ) (cong (M._,ₜ M.qₜ) (cong ⟦_⟧st (S.∘p {γ = γₜ} ⁻¹) ◾ ⟦∘⟧st {γₜ = γₜ} ◾ cong (⟦ γₜ ⟧st M.∘_) {!!}))) ◾ M.Forall[] ⁻¹
⟦[]⟧F {A = ∃ A} = {!!}
⟦[]⟧F {A = Rel ar ts} = cong (M.Rel ar) ⟦[]⟧ts ◾ M.Rel[] ⁻¹


⟦[]⟧Cp : ∀{Γₜ}{Γₚ : S.Conp Γₜ}{Δₜ}{γₜ : S.Sub Δₜ Γₜ} → ⟦ Γₚ S.[ γₜ ]Conp ⟧Cp ≡ (⟦ Γₚ ⟧Cp [ ⟦ γₜ ⟧st ]ᶠˢ) -- ⟦ Γₚ ⟧Cp M.[ γ ]C
⟦[]⟧Cp {Γₜ}{Γₚ = ◇ₚ}               = refl
⟦[]⟧Cp {Γₜ}{Γₚ = Γₚ ▹ₚ A}{Δₜ}{γₜ} = cong-▹ₚ (⟦[]⟧Cp {Γₜ}{Γₚ}{Δₜ}{γₜ}) ({!!} ◾ M.[∘]ᶠ)
-- {!⟦[]⟧Cp {Γₚ = Γₚ}{Δₜ}{}!}

⟦_⟧P : ∀{Γ A} → I.Pf Γ A → M.Pf ⟦ Γ ⟧C (⟦_⟧F {Γ} A)
⟦ a [ γₜ ]ᵖ ⟧P = substP (M.Pf _) {!!} (⟦ a ⟧P M.[ {!γₜ!} ]ᵖ)
⟦ a [ γₚ ]ᵖᵖ ⟧P = {!!}
⟦ qₚ ⟧P = substP (M.Pf _) (M.[∘]ᶠ ⁻¹) M.qₚ
⟦ ⊃in b ⟧P = substP (M.Pf _) (M.⊃[] ⁻¹) (M.⊃in (substP (M.Pf _) M.[∘]ᶠ ⟦ b ⟧P))
⟦ ⊃out f a ⟧P = M.⊃out (substP (M.Pf _) M.⊃[] ⟦ f ⟧P) ⟦ a ⟧P
⟦ ∧in a b ⟧P = substP (M.Pf _) (M.∧[] ⁻¹) (M.∧in ⟦ a ⟧P ⟦ b ⟧P)
⟦ ∧out₁ a ⟧P = M.∧out₁ (substP (M.Pf _) M.∧[] ⟦ a ⟧P)
⟦ ∧out₂ b ⟧P = M.∧out₂ (substP (M.Pf _) M.∧[] ⟦ b ⟧P)
⟦ ⊤in ⟧P = substP (M.Pf _) (M.⊤[] ⁻¹) M.⊤in
⟦ ∨in₁ a ⟧P = substP (M.Pf _) (M.∨[] ⁻¹) (M.∨in₁ ⟦ a ⟧P)
⟦ ∨in₂ b ⟧P = substP (M.Pf _) (M.∨[] ⁻¹) (M.∨in₂ ⟦ b ⟧P)
⟦ ∨out ac bc ab ⟧P = M.∨out (substP (M.Pf _) M.[∘]ᶠ ⟦ ac ⟧P) (substP (M.Pf _) M.[∘]ᶠ ⟦ bc ⟧P) (substP (M.Pf _) M.∨[] ⟦ ab ⟧P)
⟦ ⊥out p ⟧P = M.⊥out (substP (M.Pf _) M.⊥[] ⟦ p ⟧P)
⟦_⟧P {Γₜ , Γₚ}{S.Forall A} (∀in a) = substP (M.Pf _) (M.Forall[] ⁻¹)
  (M.∀in (substP (M.Pf _)
                 (M.[∘]ᶠ ⁻¹ ◾ cong (λ z → ⟦ A ⟧F' M.[ z ]ᶠ) {!!})
                         (⟦ a ⟧P M.[ _,ₚₛ_ (pₚₛ {As = ⟦ Γₚ ⟧Cp} M.∘ M.pₜ M.,ₜ M.qₜ) {⟦ Γₚ S.[ S.pₜ ]Conp ⟧Cp}
                            (substP (Pfs _) {!!} (qₚₛ {As = ⟦ Γₚ ⟧Cp} [ M.pₜ ]ᵖˢ)) ]ᵖ)))
⟦ ∀out p ⟧P = {!!}
⟦ ∃in t p ⟧P = {!!}
⟦ ∃out p p₁ ⟧P = {!!}

{-
{-
⟦_⟧C : I.Con → M.Con

⟦_⟧F' : ∀{Γₜ} → S.For Γₜ → M.For ⟦ Γₜ ⟧Ct


⟦ Γ , Γₚ ⟧C = ⟦ Γₚ ⟧Cp

⟦p⟧ : ∀{Γₜ}{Γₚ : S.Conp Γₜ} → M.Sub ⟦ Γₚ ⟧Cp ⟦ Γₜ ⟧Ct

⟦_⟧Cp {Γₜ} ◇ₚ        = ⟦ Γₜ ⟧Ct
⟦_⟧Cp {Γₜ} (Γₚ ▹ₚ A) = ⟦ Γₚ ⟧Cp M.▹ₚ ⟦ A ⟧F' M.[ ⟦p⟧ {Γₜ}{Γₚ} ]ᶠ

⟦p⟧ {Γₜ} {◇ₚ} = M.id
⟦p⟧ {Γₜ} {Γₚ ▹ₚ A} = ⟦p⟧ {Γₜ} {Γₚ} M.∘ M.pₚ

⟦_⟧T' : ∀{Γₜ} → S.Tm Γₜ → M.Tm ⟦ Γₜ ⟧Ct
⟦_⟧Ts' : ∀{n Γₜ} → S.Tm Γₜ ^ n → M.Tm ⟦ Γₜ ⟧Ct ^ n
⟦ var vz ⟧T' = M.qₜ
⟦ var (vs x) ⟧T' = ⟦ var x ⟧T' M.[ M.pₜ ]ᵗ
⟦ fun ar ts ⟧T' = M.fun ar ⟦ ts ⟧Ts'

⟦_⟧Ts' {zero} ts = _
⟦_⟧Ts' {suc n} (t , ts) = ⟦ t ⟧T' , ⟦ ts ⟧Ts'

⟦ A ⊃ B ⟧F' = ⟦ A ⟧F' M.⊃ ⟦ B ⟧F'
⟦ A ∧ B ⟧F' = ⟦ A ⟧F' M.∧ ⟦ B ⟧F'
⟦ ⊤ ⟧F' = M.⊤
⟦ A ∨ B ⟧F' = ⟦ A ⟧F' M.∨ ⟦ B ⟧F'
⟦ ⊥ ⟧F' = M.⊥
⟦ Forall A ⟧F' = M.Forall ⟦ A ⟧F'
⟦ ∃ A ⟧F' = M.∃ ⟦ A ⟧F'
⟦ Rel ar ts ⟧F' = M.Rel ar ⟦ ts ⟧Ts'

⟦_⟧F : ∀{Γ} → I.For Γ → M.For ⟦ Γ ⟧C
⟦_⟧F {Γₜ , Γₚ} A = ⟦ A ⟧F' M.[ ⟦p⟧ {Γₜ}{Γₚ} ]ᶠ

⟦_⟧T : ∀{Γ} → I.Tm Γ → M.Tm ⟦ Γ ⟧C
⟦_⟧T {Γₜ , Γₚ} t = ⟦ t ⟧T' M.[ ⟦p⟧ {Γₜ}{Γₚ} ]ᵗ

⟦_⟧S : ∀{Γ Δ} → I.Sub Δ Γ → M.Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
⟦_⟧S {Γₜ , Γₚ}{Δₜ , Δₚ} (γₜ , γₚ) = {!!}

⟦p'⟧ : ∀{Γₜ}{Γₚ : S.Conp Γₜ} → M.Sub (⟦ Γₚ ⟧Cp M.▹ₜ) ⟦ Γₚ S.[ S.pₜ ]Conp ⟧Cp
⟦p'⟧ {Γₜ}{◇ₚ} = M.id
⟦p'⟧ {Γₜ}{Γₚ ▹ₚ A} = ⟦p'⟧ {Γₜ}{Γₚ} M.∘ (M.pₚ M.∘ M.pₜ M.,ₜ M.qₜ) M.,ₚ substP (M.Pf _) {!!} (M.qₚ M.[ M.pₜ ]ᵖ)


⟦_⟧P : ∀{Γ A} → I.Pf Γ A → M.Pf ⟦ Γ ⟧C (⟦_⟧F {Γ} A)
⟦ a [ γ ]ᵖ ⟧P = {!!}
⟦ a [ γₚ ]ᵖᵖ ⟧P = {!!}
⟦ qₚ ⟧P = substP (M.Pf _) (M.[∘]ᶠ ⁻¹) M.qₚ
⟦ ⊃in b ⟧P = substP (M.Pf _) (M.⊃[] ⁻¹) (M.⊃in (substP (M.Pf _) M.[∘]ᶠ ⟦ b ⟧P))
⟦ ⊃out f a ⟧P = M.⊃out (substP (M.Pf _) M.⊃[] ⟦ f ⟧P) ⟦ a ⟧P
⟦ ∧in a b ⟧P = substP (M.Pf _) (M.∧[] ⁻¹) (M.∧in ⟦ a ⟧P ⟦ b ⟧P)
⟦ ∧out₁ a ⟧P = M.∧out₁ (substP (M.Pf _) M.∧[] ⟦ a ⟧P)
⟦ ∧out₂ b ⟧P = M.∧out₂ (substP (M.Pf _) M.∧[] ⟦ b ⟧P)
⟦ ⊤in ⟧P = substP (M.Pf _) (M.⊤[] ⁻¹) M.⊤in
⟦ ∨in₁ a ⟧P = substP (M.Pf _) (M.∨[] ⁻¹) (M.∨in₁ ⟦ a ⟧P)
⟦ ∨in₂ b ⟧P = substP (M.Pf _) (M.∨[] ⁻¹) (M.∨in₂ ⟦ b ⟧P)
⟦ ∨out ac bc ab ⟧P = M.∨out (substP (M.Pf _) M.[∘]ᶠ ⟦ ac ⟧P) (substP (M.Pf _) M.[∘]ᶠ ⟦ bc ⟧P) (substP (M.Pf _) M.∨[] ⟦ ab ⟧P)
⟦ ⊥out p ⟧P = M.⊥out (substP (M.Pf _) M.⊥[] ⟦ p ⟧P)
⟦_⟧P {Γₜ , Γₚ}{S.Forall A} (∀in a) = substP (M.Pf _) (M.Forall[] ⁻¹) (M.∀in (substP (M.Pf _) (M.[∘]ᶠ ⁻¹ ◾ cong (λ z → ⟦ A ⟧F' M.[ z ]ᶠ) {!!}) (⟦ a ⟧P M.[ ⟦p'⟧ {Γₜ}{Γₚ} ]ᵖ)))
⟦ ∀out p ⟧P = {!!}
⟦ ∃in t p ⟧P = {!!}
⟦ ∃out p p₁ ⟧P = {!!}
-}
-}
