{-# OPTIONS --prop #-}

open import lib
open import FirstOrderIntuinistic


-- Families or Subset or Classical semantics
module FI-FamModel
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  (D : Set)
  (Tm : D → Set)
  (rel : (n : ℕ) → relar n → (d : D) → ((Tm d) ^ n) → Prop)
  (fun : (n : ℕ) → funar n → (d : D) → ((Tm d) ^ n) → Tm d) where

  FamModel : Model funar relar _ _ _ _ _
  FamModel = record
    { Con = D → Set                         -- Set
    ; Sub = λ Γ Δ → (d : D) → (Γ d → Δ d)   -- λ Γ Δ → (d : D) → Γ → Δ
    ; _∘_ = λ Γd Δd d Θ → Γd d (Δd d Θ)
    ; id = λ d x → x
    ; ass = refl
    ; idl = refl
    ; idr = refl
    ; ◆ = λ _ → 𝟙
    ; ε = λ d x → *
    ; ◆η = λ σ → refl
    ; For = λ Γ → (d : D) → Γ d → Prop
    ; _[_]F = λ A Γ d Δ → A d (Γ d Δ)
    ; [∘]F = refl
    ; [id]F = refl
    ; Pf = λ Γ A → (d : D)(a : Γ d) → A d a
    ; _[_]p = λ PfK γ d Δd → PfK d (γ d Δd)
    ; _▸p_ = λ Γ A d → Σsp (Γ d) (A d)
    ; _,p_ = λ γ PfK d Δd → (γ d Δd) ,Σ (PfK d Δd)
    ; pp = λ d (Γd ,Σ Kd) → Γd
    ; qp = λ d (Γd ,Σ Kd) → Kd
    ; ▸pβ₁ = refl
    ; ▸pη = refl
    ; ⊥ = λ _ _ → 𝟘p
    ; ⊥[] = refl
    ; exfalso = λ Pf⊥ d Γd → ind𝟘p (Pf⊥ d Γd)
    ; ⊤ = λ d x → 𝟙p
    ; ⊤[] = refl
    ; tt = λ _ _ → *
    ; _⊃_ = λ K L d Γd → (K d Γd) → (L d Γd)
    ; ⊃[] = refl
    ; ⊃intro = λ PfKL d Γd → λ Kd → PfKL d (Γd ,Σ Kd)
    ; ⊃elim = λ PfKL d (Γd ,Σ Kd) → PfKL d Γd Kd
    ; _∧_ = λ K L d Γd → (K d Γd) ×p (L d Γd)
    ; ∧[] = refl
    ; ∧intro = λ PfK PfL d Γd → (PfK d Γd) ,Σ (PfL d Γd)
    ; ∧elim₁ = λ PfKL d Γd → proj₁ (PfKL d Γd)
    ; ∧elim₂ = λ PfKL d Γd → proj₂ (PfKL d Γd)
    ; _∨_ = λ K L d Γd → (K d Γd) +p (L d Γd)
    ; ∨[] = refl
    ; ∨elim = λ {Γ}{K}{L}{C} PfKC PfLC PfKL d Γd → ind+p (λ _ → C d Γd) (λ y → PfKC d (Γd ,Σ y)) (λ y → PfLC d (Γd ,Σ y))  (PfKL d Γd)
    ; ∨intro₁ = λ PfK d Γd → inj₁ (PfK d Γd)
    ; ∨intro₂ = λ PfL d Γd → inj₂ (PfL d Γd)
    ; Tm = λ Γ → (d : D) → (Γ d) → (Tm d)
    ; _[_]t = λ t γ d Δd → t d (γ d Δd)
    ; [∘]t = refl
    ; [id]t = refl
    ; _▸t = λ Γ d → Σ (Γ d) λ _ → Tm d
    ; _,t_ = λ γ t d Δd → (γ d Δd) ,Σ t d Δd
    ; pt = λ d → proj₁
    ; qt = λ d → proj₂
    ; ▸tβ₁ = refl
    ; ▸tβ₂ = refl
    ; ▸tη = refl
    ; Tms = λ Γ n → (d : D) → Γ d → (Tm d) ^ n
    ; _[_]ts = λ ts γ d Δd → ts d (γ d Δd)
    ; [∘]ts = refl
    ; [id]ts = refl
    ; εs = λ d x → *
    ; ◆sη = λ _ → refl
    ; _,s_ = λ ts t d Γd → t d Γd ,Σ ts d Γd
    ; π₁ = λ ts d Γd → proj₂ (ts d Γd)
    ; π₂ = λ ts d Γd → proj₁ (ts d Γd)
    ; ▸sβ₁ = refl
    ; ▸sβ₂ = refl
    ; ▸sη = refl
    ; ,[] = refl
    ; fun = λ n x ts d Γd → fun n x d (ts d Γd)
    ; fun[] = refl
    ; rel = λ n x ts d Γd → rel n x d (ts d Γd)
    ; rel[] = refl
    ; ∀' = λ K d Γd → (t : Tm d) → K d (Γd ,Σ t)
    ; ∀[] = refl
    ; ∀intro = λ PfK d Γd t → PfK d (Γd ,Σ t)
    ; ∀elim = λ Pf∀K d (Γd ,Σ t) → Pf∀K d Γd t
    ; ∃' = λ K d Γd → ∃ (Tm d) λ t → K d (Γd ,Σ t)
    ; ∃[] = refl
    ; ∃intro = λ t PfK d Γd → (t d Γd) ,∃ (PfK d Γd)
    ; ∃elim = λ Pf∃K PfKL d Γd → with∃ (Pf∃K d Γd) (λ t K → PfKL d ((Γd ,Σ t) ,Σ K))
    ; Eq = λ t t' d Γd → t d Γd ≡ t' d Γd
    ; Eq[] = refl
    ; Eqrefl = λ d a → refl
    ; subst' = λ K eqtt' PfK d Γd → substp (λ t → K d (Γd ,Σ t)) (eqtt' d Γd) (PfK d Γd)
    }