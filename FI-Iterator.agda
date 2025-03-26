{-# OPTIONS --prop --allow-unsolved-metas #-}

open import lib
open import FirstOrderIntuinistic

-- This is the iterator of FirstOrderIntuinistic.Model
-- We can view it as a morphisms in the category of algebras generator by Model, 
-- that go from the inital model (FirstOrderIntuinistic.IM) to any model (IM being the initial object and Iterator being the unique morphism)
module FI-Iterator
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  {i}{j}{k}{l}{m}
  (M : FirstOrderIntuinistic.Model funar relar i j k l m)
  where

module M = Model M

-- First we define Fors and Pfs
-- These are telescopes of Formulas and Proofs respectively
-- They can be viewed as "vectors" containing For-s and Pf-s
-- They can also be viewed as a new sort mirroring For and Pf
-- where Pf depends on For, Pfs depends on Fors

-- cong-,ₚ : γ ≡ γ' → γ ,p a ≡ γ' ,p a ≡ 
cong-,ₚ : ∀{Γ Δ}{γ γ' : M.Sub Δ Γ} → γ ≡ γ' → ∀{A}{a : M.Pf Δ (A M.[ γ ]F)}{a' : M.Pf Δ (A M.[ γ' ]F)} → γ M.,p a ≡ γ' M.,p a'
cong-,ₚ refl = refl

-- Dont do this
SubΔcong : ∀{Γ}{Δ}{γ : M.Sub Δ Γ}{Δ'} → (Δ ≡ Δ') → M.Sub Δ' Γ
SubΔcong {Γ} {Δ} {γ} {Δ'} x = {!   !}

-- γ : Sub Δ Γ → (e : Δ ≡ Δ') → (transport For  e (A [ γ ]F)) ≡ A [ transport Sub e γ ]F
subst-[]F : ∀{Γ}{A : M.For Γ}{Δ}{γ : M.Sub Δ Γ}{Δ'}(e : Δ ≡ Δ') →
  transport M.For e (A M.[ γ ]F) ≡ A M.[ transport (λ z → M.Sub z Γ) e γ ]F
subst-[]F {Γ}{A}{Δ}{γ}{Δ'} refl = {!   !}

{-
,ₜ∘ : ∀{Γ Δ}{γ : M.Sub Δ Γ}{t : M.Tm Δ}{Θ}{δ : M.Sub Θ Δ} →
  (γ M.,ₜ t) M.∘ δ ≡ γ M.∘ δ M.,ₜ (t M.[ δ ]ᵗ)
,ₜ∘ {γ = γ}{δ = δ} = M.▹ₜη ◾ cong₂ M._,ₜ_ (M.ass ⁻¹ ◾ cong (M._∘ δ) M.▹ₜβ₁) (M.[∘]ᵗ ◾ cong (M._[ δ ]ᵗ) M.▹ₜβ₂)

,ₚ∘ : ∀{Γ Δ}{γ : M.Sub Δ Γ}{A}{a : M.Pf Δ (A M.[ γ ]ᶠ)}{Θ}{δ : M.Sub Θ Δ} →
  (γ M.,ₚ a) M.∘ δ ≡ γ M.∘ δ M.,ₚ substP (M.Pf Θ) (M.[∘]ᶠ ⁻¹) (a M.[ δ ]ᵖ)
,ₚ∘ {Γ}{Δ}{γ}{A}{a}{Θ}{δ} = M.▹ₚη ◾ cong-,ₚ (M.ass ⁻¹ ◾ cong (M._∘ δ) M.▹ₚβ₁)
-}


-- Fors are mutually (inductively? ind-rec-ly?) defined with _▸ps_ which says that Pfs is locally representable
data Fors (Γ : M.Con) : Set k
_▸ps_ : (Γ : M.Con) → Fors Γ → M.Con

-- TODO proofs about Fors

data Fors Γ where
  ◆fs    : Fors Γ                                    -- Empty list
  _▸fs_ : (As : Fors Γ) → M.For (Γ ▸ps As) → Fors Γ   -- extending the list with and another formula in context Γ ++ As
-- _▸ps_ can also be viewed as _++_ for Fors
Γ ▸ps ◆fs       = Γ
Γ ▸ps (As ▸fs A) = (Γ ▸ps As) M.▸p A

_[_]fs  : ∀{Γ} → Fors Γ → ∀{Δ} → M.Sub Δ Γ → Fors Δ
_⁺ps_   : ∀{Γ Δ}(γ : M.Sub Δ Γ)(As : Fors Γ) → M.Sub (Δ ▸ps (As [ γ ]fs)) (Γ ▸ps As)
(◆fs         [ γ ]fs) = ◆fs
((As ▸fs A) [ γ ]fs)  = (As [ γ ]fs) ▸fs (A M.[ γ ⁺ps As ]F)
γ ⁺ps ◆fs       = γ
γ ⁺ps (As ▸fs A) = ((γ ⁺ps As) M.∘ M.pp) M.,p substp (M.Pf _) (sym M.[∘]F) M.qp

Pfs : (Γ : M.Con) → Fors Γ → Prop l
⟨_⟩ps : ∀{Γ As} → Pfs Γ As → M.Sub Γ (Γ ▸ps As)
Pfs Γ ◆fs = 𝟙p
Pfs Γ (As ▸fs A) = Σp (Pfs Γ As) λ as → M.Pf Γ (A M.[ ⟨ as ⟩ps ]F)
⟨_⟩ps {Γ} {◆fs} _ = M.id 
⟨_⟩ps {Γ} {As ▸fs A} (as ,Σ a) = ⟨ as ⟩ps M.,p a

_[_]ps : ∀{Γ As Δ} → Pfs Γ As → (γ : M.Sub Δ Γ) → Pfs Δ (As [ γ ]fs)
⁺⟨⟩ps  : ∀{Γ As Δ}{as : Pfs Γ As}{γ : M.Sub Δ Γ} → (γ ⁺ps As) M.∘ ⟨ as [ γ ]ps ⟩ps ≡ ⟨ as ⟩ps M.∘ γ
_[_]ps {As = ◆fs}       _         γ = *
_[_]ps {As = As ▸fs A} (as ,Σ a) γ = 
    (as [ γ ]ps) 
    ,Σ 
    (substp (M.Pf _) (trans (sym M.[∘]F) (trans (cong (A M.[_]F) (sym (⁺⟨⟩ps {As = As})) ) M.[∘]F)) (a M.[ γ ]p))

⁺⟨⟩ps {As = ◆fs} = trans M.idr (sym M.idl)
⁺⟨⟩ps {Γ}{As ▸fs A}{Δ}{as ,Σ a}{γ} = {! ,p  !} -- ,ₚ∘ ◾ cong-,ₚ (M.ass ◾ cong ((γ ⁺ᵖˢ As) M.∘_) M.▹ₚβ₁ ◾ ⁺⟨⟩ps {As = As}) ◾ ,ₚ∘ ⁻¹

-- Innentől Fors, Pfs nélküli próba amit Szumival beszéltünk egyik este

module S = Model (IM funar relar)
module IS = I funar relar

⟦_⟧Ct : IS.ConTm → M.Con
⟦_,_⟧Cp : (Γt : IS.ConTm) → IS.ConPf Γt → M.Con
⟦_⟧C : S.Con → M.Con
⟦_,_⟧F : (Γ : S.Con) → S.For Γ → M.For ⟦ Γ ⟧C


⟦ I.◆t ⟧Ct = M.◆
⟦ Γ I.▸t ⟧Ct = ⟦ Γ ⟧Ct M.▸t


⟦ Γt ,Σ Γp ⟧C = ⟦ Γt , Γp ⟧Cp
⟦ Γt , Γp I.▸p A ⟧Cp = ⟦ Γt , Γp ⟧Cp M.▸p ⟦ (Γt ,Σ Γp) , A ⟧F

⟦ Γt , I.◆p ⟧Cp = ⟦ Γt ⟧Ct

⟦_⟧S : ∀{Δ Γ} → S.Sub Δ Γ → M.Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
⟦_⟧St : ∀{Δ Γ} → IS.Subt Δ Γ → M.Sub ⟦ Δ ⟧Ct ⟦ Γ ⟧Ct
⟦_⟧Sp : ∀{Γt}{Δ Γ : IS.ConPf Γt} → IS.Subp Δ Γ → M.Sub ⟦ Γt , Δ ⟧Cp ⟦ Γt , Γ ⟧Cp

⟦_⟧T : ∀{Γ} → S.Tm Γ → M.Tm ⟦ Γ ⟧C
⟦_⟧Ts : ∀{Γ n} → S.Tms Γ n → M.Tms ⟦ Γ ⟧C n

⟦ I.εt ⟧St = M.ε
⟦ γ I.,t t ⟧St = ⟦ γ ⟧St M.,t {!   !} -- ⟦ t ⟧T

⟦ γt ,Σ γp ⟧S = {! ⟦ γt ⟧St  !}
⟦_⟧Sp {Γt} {Δ} {Γ} x = {! Γ  !}

⟦_⟧T = {!   !}
⟦_⟧Ts = {!   !}

⟦ Γ , I.⊥ ⟧F = {!   !} -- Ha ezt a sort megadom, vagy bármelyik sorát ⟦_⟧F-nek akkor nem terminator check-el
⟦ Γ , I.⊤ ⟧F = {!   !}
⟦ Γ , x I.⊃ x₁ ⟧F = {!   !}
⟦ Γ , x I.∧ x₁ ⟧F = {!   !}
⟦ Γ , x I.∨ x₁ ⟧F = {!   !}
⟦ Γ , I.∀' x ⟧F = {!   !}
⟦ Γ , I.∃' x ⟧F = {!   !}
⟦ Γ , I.Eq x x₁ ⟧F = {!   !}
⟦ Γ , I.rel n x x₁ ⟧F = {!   !}



⟦_⟧Pf : ∀{Γ A} → S.Pf Γ A → M.Pf ⟦ Γ ⟧C ⟦ Γ , A ⟧F
⟦ I.exfalso x ⟧Pf = {!   !}
⟦ I.tt ⟧Pf = {!   !}
⟦ I.⊃intro x ⟧Pf = {!   !}
⟦ x I.$ x₁ ⟧Pf = {!   !}
⟦ I.∧intro x x₁ ⟧Pf = {!   !}
⟦ I.∧elim₁ x ⟧Pf = {!   !}
⟦ I.∧elim₂ x ⟧Pf = {!   !}
⟦ I.∨elim x x₁ x₂ ⟧Pf = {!   !}
⟦ I.∨intro₁ x ⟧Pf = {!   !}
⟦ I.∨intro₂ x ⟧Pf = {!   !}
⟦ I.∀intro x ⟧Pf = {!   !}
⟦ I.un∀ x t ⟧Pf = {!   !}
⟦ I.∃intro t x ⟧Pf = {!   !}
⟦ I.∃elim x x₁ ⟧Pf = {!   !}
⟦ I.ref ⟧Pf = {!   !}
⟦ I.subst' K x x₁ ⟧Pf = {!   !}
⟦ x I.[ γ ]P ⟧Pf = {!   !}
⟦ x I.[ x₁ ]p ⟧Pf = {!   !}
⟦ I.qp ⟧Pf = {!   !}

{-
⟦_⟧C : Σ S.ConTm S.ConPf → M.Con
⟦_⟧Ct : S.ConTm → M.Con
⟦ S.◆t ⟧Ct = M.◆ 
⟦ Γ S.▸t ⟧Ct = ⟦ Γ ⟧Ct M.▸t

⟦_⟧F' : ∀{Γt} → S.For Γt → M.For ⟦ Γt ⟧C
  
⟦_⟧Cp : ∀{Γt} → S.ConPf Γt → M.Con
⟦ Γt ,Σ Γp ⟧C  = ?
⟦ S.◆p ⟧Cp = M.◆
⟦ Γp S.▸p A ⟧Cp = ⟦ Γp ⟧Cp M.▸p {! ⟦ A ⟧F'  !} -- ⟦ Γp ⟧Cp ▸p (⟦ A ⟧F' M.[ pₚₛ {As = ⟦ Γp ⟧Cp} ]F) -- ⟦ A ⟧F' M.[ pₚₛ {As = ⟦ Γₚ ⟧Cp} ]ᶠ

⟦_⟧T' : ∀{Γₜ} → S.Tm Γₜ → M.Tm ⟦ Γₜ ⟧Ct
⟦_⟧Ts' : ∀{n Γₜ} → S.Tm Γₜ ^ n → M.Tm ⟦ Γₜ ⟧Ct ^ n
-}  