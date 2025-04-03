{-# OPTIONS --prop #-}

open import lib
open import FirstOrderIntuinistic

-- Kripke or Presheaf model
module FI-KripkeModel
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  (W : Set)
  (_≤_ : W → W → Prop)
  (id≤ : {w : W} → w ≤ w)
  (_∘≤_ : {w w' w'' : W} → w' ≤ w → w'' ≤ w' → w'' ≤ w)
  (Tm : Set)
  (Rel : (n : ℕ) → relar n → (Tm ^ n) → W → Prop)
  (Rel≤ : ∀{n}{ar : relar n}{ts : Tm ^ n}{w w'} → Rel n ar ts w → w' ≤ w → Rel n ar ts w')
  (fun : (n : ℕ) → funar n → (Tm ^ n) → Tm)
  where

  record PSh : Set₁ where
    field
      ∣_∣    : W → Prop
      _∶_⟨_⟩ : ∀{w w'} → ∣_∣ w → w' ≤ w → ∣_∣ w'
  open PSh public

  record DepPSh (Γt : Set)(Γp : Γt → PSh) : Set₁ where
    field
      ∣_∣    : (γtₓ : Γt) → {w : W} → ∣ Γp γtₓ ∣ w → Prop
      _∶_⟨_⟩ : ∀{w w'}{γtₓ : Γt}{γpₓ : PSh.∣ Γp γtₓ ∣ w} → ∣_∣ γtₓ γpₓ → (f : w' ≤ w) → ∣_∣ γtₓ (Γp γtₓ ∶ γpₓ ⟨ f ⟩)
  open DepPSh public

  KripkeModel : Model funar relar _ _ _ _ _
  KripkeModel = record
    { Con = Σ Set λ Γ → Γ → PSh -- set built using Tm and the proof assumptions
    ; Sub = λ (Δt ,Σ Δp) (Γt ,Σ Γp) → Σsp (Δt → Γt) λ γt → ∀{w}(δtₓ : Δt) → ∣ Δp δtₓ ∣ w → ∣ Γp (γt δtₓ) ∣ w
    ; _∘_ = λ (γt ,Σ γp) (δt ,Σ δp) → (λ θtₓ → γt (δt θtₓ)) ,Σ (λ θtₓ θpₓ → γp (δt θtₓ) (δp θtₓ θpₓ) )
    ; id = (λ γtₓ → γtₓ) ,Σ (λ γtₓ γpₓ → γpₓ)
    ; ass = refl
    ; idl = refl
    ; idr = refl
    ; ◆ = 𝟙 ,Σ λ _ → record { ∣_∣ = λ _ → 𝟙p ; _∶_⟨_⟩ = λ _ _ → * }
    ; ε = (λ _ → *) ,Σ (λ _ _ → *)
    ; ◆η = λ _ → refl
    ; For = λ (Γt ,Σ Γp) → DepPSh Γt Γp
    ; _[_]F = λ A (γt ,Σ γp) → record
      { ∣_∣ = λ δtₓ δpₓ → ∣ A ∣ (γt δtₓ) (γp δtₓ δpₓ)
      ; _∶_⟨_⟩ = λ aw f → A ∶ aw ⟨ f ⟩ }
    ; [∘]F = refl
    ; [id]F = refl
    ; Pf = λ (Γt ,Σ Γp) A → (γtₓ : Γt) → {w : W}(γpₓ : ∣ Γp γtₓ ∣ w) → ∣ A ∣ γtₓ γpₓ
    ; _[_]p = λ a (γt ,Σ γp) δtₓ δpₓ → a (γt δtₓ) (γp _ δpₓ)
    ; _▸p_ = λ (Γt ,Σ Γp) A → Γt ,Σ λ γtₓ → record
        { ∣_∣ = λ w → Σp (∣ Γp γtₓ ∣ w) λ γpₓ → ∣ A ∣ γtₓ γpₓ
        ; _∶_⟨_⟩ = λ (γpₓ ,Σ aₓ) f → Γp γtₓ ∶ γpₓ ⟨ f ⟩ ,Σ (A ∶ aₓ ⟨ f ⟩) }
    ; _,p_ = λ (γt ,Σ γp) a → (λ δtₓ → γt δtₓ) ,Σ λ δtₓ δpₓ → γp δtₓ δpₓ ,Σ a δtₓ δpₓ
    ; pp = (λ γtₓ → γtₓ) ,Σ λ γtₓ (γpₓ ,Σ aₓ) → γpₓ
    ; qp = λ γtₓ (γpₓ ,Σ aₓ) → aₓ
    ; ▸pβ₁ = refl
    ; ▸pη = refl
    ; ⊥ = record { ∣_∣ = λ _ _ → 𝟘p ; _∶_⟨_⟩ = λ () }
    ; ⊥[] = refl
    ; exfalso = λ 0p γtₓ γpₓ → ind𝟘p (0p γtₓ γpₓ)
    ; ⊤ = record { ∣_∣ = λ _ _ → 𝟙p ; _∶_⟨_⟩ = λ _ _ → * }
    ; ⊤[] = refl
    ; tt = λ _ _ → *
    ; _⊃_ = λ A B → record { ∣_∣ = λ γtₓ {w} γpₓ → ∀{w'}(f : w' ≤ w) → {!∣ A ∣ γtₓ (γpₓ!} ; _∶_⟨_⟩ = {!!} }
    ; ⊃[] = {!!}
    ; ⊃intro = {!   !}
    ; ⊃elim = {!   !}
    ; _∧_ = λ A B → record { ∣_∣ = λ γtₓ γpₓ → ∣ A ∣ γtₓ γpₓ ×p ∣ B ∣ γtₓ γpₓ ; _∶_⟨_⟩ = λ (aₓ ,Σ bₓ) f → (A ∶ aₓ ⟨ f ⟩) ,Σ (B ∶ bₓ ⟨ f ⟩) }
    ; ∧[] = refl
    ; ∧intro = {!   !}
    ; ∧elim₁ = {!   !}
    ; ∧elim₂ = {!   !}
    ; _∨_ = {!   !}
    ; ∨[] = {!   !}
    ; ∨elim = {!   !}
    ; ∨intro₁ = {!   !}
    ; ∨intro₂ = {!   !}
    ; Tm = λ (Γt ,Σ Γp) → Γt → Tm
    ; _[_]t = λ t (γt ,Σ γp) δtₓ → t (γt δtₓ)
    ; [∘]t = refl
    ; [id]t = refl
    ; _▸t = λ (Γt ,Σ Γp) → (Γt × Tm) ,Σ (λ (γtₓ ,Σ tₓ) → Γp γtₓ)
    ; _,t_ = λ (γt ,Σ γp) t → (λ δtₓ → γt δtₓ ,Σ t δtₓ) ,Σ λ δtₓ δpₓ → γp δtₓ δpₓ
    ; pt = (λ (γtₓ ,Σ tₓ) → γtₓ) ,Σ (λ _ γpₓ → γpₓ)
    ; qt = λ (γtₓ ,Σ tₓ) → tₓ
    ; ▸tβ₁ = refl
    ; ▸tβ₂ = refl
    ; ▸tη = refl
    ; Tms = λ (Γt ,Σ Γp) n → Γt → Tm ^ n
    ; _[_]ts = λ ts (γt ,Σ γp) δtₓ → ts (γt δtₓ)
    ; [∘]ts = refl
    ; [id]ts = refl
    ; εs = λ _ → *
    ; ◆sη = λ _ → refl
    ; _,s_ = λ ts t γtₓ → t γtₓ ,Σ ts γtₓ
    ; π₁ = λ ts γtₓ → proj₂ (ts γtₓ)
    ; π₂ = λ ts γtₓ → proj₁ (ts γtₓ)
    ; ▸sβ₁ = refl
    ; ▸sβ₂ = refl
    ; ▸sη = refl
    ; ,[] = refl
    ; fun = λ n ar ts γtₓ → fun n ar (ts γtₓ)
    ; fun[] = refl
    ; rel = λ n ar ts → record { ∣_∣ = λ γtₓ {w} γpₓ → Rel n ar (ts γtₓ) w ; _∶_⟨_⟩ = Rel≤ }
    ; rel[] = refl
    ; ∀' = λ A → record { ∣_∣ = λ γtₓ {w} γpₓ → (tₓ : Tm) → ∣ A ∣ (γtₓ ,Σ tₓ) γpₓ ; _∶_⟨_⟩ = λ ∀aₓ f tₓ → A ∶ ∀aₓ tₓ ⟨ f ⟩ }
    ; ∀[] = refl
    ; ∀intro = λ a γtₓ γpₓ tₓ → a (γtₓ ,Σ tₓ) γpₓ
    ; ∀elim = λ ∀a (γtₓ ,Σ tₓ) γpₓ → ∀a γtₓ γpₓ tₓ
    ; ∃' = {!   !}
    ; ∃[] = {!   !}
    ; ∃intro = {!   !}
    ; ∃elim = {!   !}
    ; Eq = {!   !}
    ; Eq[] = {!   !}
    ; Eqrefl = {!   !}
    ; subst' = {!   !}
    } 

