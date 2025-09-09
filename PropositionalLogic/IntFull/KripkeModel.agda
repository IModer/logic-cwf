{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.KripkeModel
  (Atom : Set)
  -- W is a preorder, the interpretation of Contexts/Formulas will be a Presheaf over W
  (W    : Set)
  (_≥_  : W → W → Prop)
  (id≥  : {w : W} → w ≥ w)
  (_∘≥_ : {v w z : W} → w ≥ v → z ≥ w → z ≥ v)
  -- PV is another preord indexed by elements of W (or a dependant preord over W)
  -- PV will be the interpretation of atom
  (∣_∣pv    : Atom → W → Prop)
  (_pv:_⟨_⟩ : (a : Atom) → ∀{w w'} → (∣ a ∣pv w) → w' ≥ w → (∣ a ∣pv w'))
  where
  -- PSh is a presheaf over W
  record PSh : Set₁ where
      field
        ∣_∣    : W → Prop
        _∶_⟨_⟩ : ∀{w w'} → ∣_∣ w → w' ≥ w → ∣_∣ w'
  open PSh public

  -- We can define the presheaf in advance because Con and For are both Psh
  
  𝟙PSh : PSh
  ∣ 𝟙PSh ∣ = λ _ → 𝟙p
  _∶_⟨_⟩ 𝟙PSh = λ * _ → *

  𝟘PSh : PSh
  ∣ 𝟘PSh ∣ = λ _ → 𝟘p
  _∶_⟨_⟩ 𝟘PSh = λ x _ → x

  _×PSh_ : PSh → PSh → PSh
  ∣ Γ ×PSh K ∣ = λ w → ∣ Γ ∣ w ×p ∣ K ∣ w
  _∶_⟨_⟩ (Γ ×PSh K) = λ (Γw ,Σ Kw) γ → (Γ ∶ Γw ⟨ γ ⟩) ,Σ (K ∶ Kw ⟨ γ ⟩)

  _+PSh_ : PSh → PSh → PSh
  ∣ Γ +PSh K ∣ = λ w → ∣ Γ ∣ w +p ∣ K ∣ w
  _∶_⟨_⟩ (Γ +PSh K) =  λ A γ → ind+p _ (λ Γw → inj₁ (Γ ∶ Γw ⟨ γ ⟩)) (λ Kw → inj₂ (K ∶ Kw ⟨ γ ⟩)) A

  _⇒PSh_ : PSh → PSh → PSh
  ∣ Γ ⇒PSh K ∣ = λ w → {w' : W} → w' ≥ w → ∣ Γ ∣ w' → ∣ K ∣ w'
  _∶_⟨_⟩ (Γ ⇒PSh K) = λ A γ δ Γw' → A (γ ∘≥ δ) Γw'

  Kripke : Model Atom _ _ _ _
  Kripke = record
    { Con = PSh
    ; Sub = λ Γ Δ → {w : W} → ∣ Γ ∣ w → ∣ Δ ∣ w
    ; _∘_ = λ δ θ θw → δ (θ θw)
    ; id = λ x → x
    ; ◆ = 𝟙PSh
    ; ε = λ x → *
    ; For = PSh
    ; Pf = λ Γ K → {w : W} → ∣ Γ ∣ w → ∣ K ∣ w
    ; _[_] = λ PfK γ Δw → PfK (γ Δw)
    ; _▸_ = _×PSh_
    ; _,_ = λ γ PfK Δw → (γ Δw) ,Σ PfK Δw
    ; p = proj₁
    ; q = proj₂
    ; ⊥ = 𝟘PSh
    ; exfalso = λ Pf⊥ Γw → ind𝟘p (Pf⊥ Γw)
    ; ⊤ = 𝟙PSh
    ; tt = λ _ → *
    ; _⊃_ = _⇒PSh_
    ; ⊃intro = λ {Γ}{K}{L} PfL Γw γ Kw' → PfL ((Γ ∶ Γw ⟨ γ ⟩) ,Σ Kw')
    ; ⊃elim = λ PfKL (Γw ,Σ Kw) → PfKL Γw id≥ Kw
    ; _∧_ = _×PSh_
    ; ∧intro = λ PfK PfL Γw → (PfK Γw) ,Σ (PfL Γw)
    ; ∧elim₁ = λ PfKL Γw → proj₁ (PfKL Γw)
    ; ∧elim₂ = λ PfKL Γw → proj₂ (PfKL Γw)
    ; _∨_ = _+PSh_
    ; ∨intro₁ = λ u Γw → inj₁ (u Γw)
    ; ∨intro₂ = λ u Γw → inj₂ (u Γw)
    ; ∨elim = λ PfKC PfLC PfKL Γw → ind+p _ (λ Kw → PfKC (Γw ,Σ Kw)) (λ Lw → PfLC (Γw ,Σ Lw)) (PfKL Γw)
    ; atom = λ x → record { ∣_∣ = ∣ x ∣pv ; _∶_⟨_⟩ = _pv:_⟨_⟩ x }
    }