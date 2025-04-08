{-# OPTIONS --prop #-}

open import lib
open import FirstOrderIntuinistic

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

  record Conp : Set₁ where
    field
      ∣_∣    : W → Prop
      _∶_⟨_⟩ : ∀{w w'} → ∣_∣ w → w' ≤ w → ∣_∣ w'
  open Conp public

  record For (Γt : Set) : Set₁ where
    field
      ∣_∣    : Γt → W → Prop
      _∶_⟨_⟩ : ∀{w w'}{γtₓ : Γt} → ∣_∣ γtₓ w → w' ≤ w → ∣_∣ γtₓ w'
  open For public

  KripkeModel : Model funar relar _ _ _ _ _
  KripkeModel = record
    { Con = Σ Set λ Γ → Γ → Conp -- set built using Tm and the proof assumptions
    ; Sub = λ (Δt ,Σ Δp) (Γt ,Σ Γp) → Σsp (Δt → Γt) λ γt → ∀{w}(δtₓ : Δt) → ∣ Δp δtₓ ∣ w → ∣ Γp (γt δtₓ) ∣ w
    ; _∘_ = λ (γt ,Σ γp) (δt ,Σ δp) → (λ θtₓ → γt (δt θtₓ)) ,Σ (λ θtₓ θpₓ → γp (δt θtₓ) (δp θtₓ θpₓ) )
    ; id = (λ γtₓ → γtₓ) ,Σ (λ γtₓ γpₓ → γpₓ)
    ; ass = refl
    ; idl = refl
    ; idr = refl
    ; ◆ = 𝟙 ,Σ λ _ → record { ∣_∣ = λ _ → 𝟙p ; _∶_⟨_⟩ = λ _ _ → * }
    ; ε = (λ _ → *) ,Σ (λ _ _ → *)
    ; ◆η = λ _ → refl
    ; For = λ (Γt ,Σ Γp) → For Γt
    ; _[_]F = λ A (γt ,Σ γp) → record
      { ∣_∣ = λ δtₓ w → ∣ A ∣ (γt δtₓ) w
      ; _∶_⟨_⟩ = λ aₓ f → A ∶ aₓ ⟨ f ⟩ }
    ; [∘]F = refl
    ; [id]F = refl
    ; Pf = λ (Γt ,Σ Γp) A → (γtₓ : Γt) → {w : W}(γpₓ : ∣ Γp γtₓ ∣ w) → ∣ A ∣ γtₓ w
    ; _[_]p = λ a (γt ,Σ γp) δtₓ δpₓ → a (γt δtₓ) (γp _ δpₓ)
    ; _▸p_ = λ (Γt ,Σ Γp) A → Γt ,Σ λ γtₓ → record
        { ∣_∣ = λ w → Σp (∣ Γp γtₓ ∣ w) λ γpₓ → ∣ A ∣ γtₓ w
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
    ; _⊃_ = λ A B → record { ∣_∣ = λ γtₓ w → ∀{w'} → w' ≤ w → ∣ A ∣ γtₓ w' → ∣ B ∣ γtₓ w' ; _∶_⟨_⟩ = λ pₓ f g → pₓ (f ∘≤ g) }
    ; ⊃[] = refl
    ; ⊃intro = λ {(Γt ,Σ Γp) ,Σ A} b γtₓ γpₓ f aₓ → b γtₓ (Γp γtₓ ∶ γpₓ ⟨ f ⟩ ,Σ aₓ)
    ; ⊃elim = λ p γtₓ (γpₓ ,Σ aₓ) → p γtₓ γpₓ id≤ aₓ
    ; _∧_ = λ A B → record { ∣_∣ = λ γtₓ γpₓ → ∣ A ∣ γtₓ γpₓ ×p ∣ B ∣ γtₓ γpₓ ; _∶_⟨_⟩ = λ (aₓ ,Σ bₓ) f → (A ∶ aₓ ⟨ f ⟩) ,Σ (B ∶ bₓ ⟨ f ⟩) }
    ; ∧[] = refl
    ; ∧intro = λ a b γtₓ γpₓ → a γtₓ γpₓ ,Σ b γtₓ γpₓ
    ; ∧elim₁ = λ ab γtₓ γpₓ → proj₁ (ab γtₓ γpₓ)
    ; ∧elim₂ = λ ab γtₓ γpₓ → proj₂ (ab γtₓ γpₓ)
    ; _∨_ = λ A B → record { ∣_∣ = λ γtₓ w → ∣ A ∣ γtₓ w +p ∣ B ∣ γtₓ w ; _∶_⟨_⟩ = λ { (inj₁ aₓ) f → inj₁ (A ∶ aₓ ⟨ f ⟩) ; (inj₂ bₓ) f → inj₂ (B ∶ bₓ ⟨ f ⟩) } }
    ; ∨[] = refl
    ; ∨elim = λ {_}{_}{_}{C} f g ab γtₓ {w} γpₓ → ind+p (λ _ → ∣ C ∣ γtₓ w) (λ aₓ → f γtₓ (γpₓ ,Σ aₓ)) (λ bₓ → g γtₓ (γpₓ ,Σ bₓ)) (ab γtₓ γpₓ)
    ; ∨intro₁ = λ a γtₓ γpₓ → inj₁ (a γtₓ γpₓ)
    ; ∨intro₂ = λ b γtₓ γpₓ → inj₂ (b γtₓ γpₓ)
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
    ; rel = λ n ar ts → record { ∣_∣ = λ γtₓ w → Rel n ar (ts γtₓ) w ; _∶_⟨_⟩ = Rel≤ }
    ; rel[] = refl
    ; ∀' = λ A → record { ∣_∣ = λ γtₓ w → (tₓ : Tm) → ∣ A ∣ (γtₓ ,Σ tₓ) w ; _∶_⟨_⟩ = λ ∀aₓ f tₓ → A ∶ ∀aₓ tₓ ⟨ f ⟩ }
    ; ∀[] = refl
    ; ∀intro = λ a γtₓ γpₓ tₓ → a (γtₓ ,Σ tₓ) γpₓ
    ; ∀elim = λ ∀a (γtₓ ,Σ tₓ) γpₓ → ∀a γtₓ γpₓ tₓ
    ; ∃' = λ A → record { ∣_∣ = λ γtₓ w → ∃ Tm λ tₓ → ∣ A ∣ (γtₓ ,Σ tₓ) w ; _∶_⟨_⟩ = λ ∃aₓ f → with∃ ∃aₓ λ tₓ aₓ → tₓ ,∃ (A ∶ aₓ ⟨ f ⟩) }
    ; ∃[] = refl
    ; ∃intro = λ t aₓ γtₓ γpₓ → t γtₓ ,∃ aₓ γtₓ γpₓ
    ; ∃elim = λ ∃a b γtₓ γpₓ → with∃ (∃a γtₓ γpₓ) λ tₓ aₓ → b (γtₓ ,Σ tₓ) (γpₓ ,Σ aₓ)
    ; Eq = λ t t' → record { ∣_∣ = λ γtₓ w → t γtₓ ≡ t' γtₓ ; _∶_⟨_⟩ = λ e _ → e }
    ; Eq[] = refl
    ; Eqrefl = λ _ _ → refl
    ; subst' = λ { {Γt ,Σ Γp} A {t}{t'} e a γtₓ {w} γpₓ → substp (λ tₓ → ∣ A ∣ (γtₓ ,Σ tₓ) w) (e γtₓ γpₓ) (a γtₓ γpₓ) }
    } 
