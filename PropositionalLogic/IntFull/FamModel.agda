{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.FamModel
  (C : Set)
  (Atom : Set)
  (atom : Atom → Prop)
  where

  Fam : Model Atom _ _ _ _
  Fam = record
    { Con = C → Prop
    ; Sub = λ Γ Δ → (c : C) → Γ c → Δ c
    ; _∘_ = λ γ δ c θc → γ c (δ c θc)
    ; id = λ _ x → x
    ; ◆ = λ x → 𝟙p
    ; ε = λ c x → *
    ; For = Prop
    ; Pf = λ Γ K → (c : C) → (Γ c) → K
    ; _[_] = λ PfK γ c δc → PfK c (γ c δc)
    ; _▸_ = λ Γ K c → (Γ c) ×p K
    ; _,_ = λ γ PfK c δc → γ c δc ,Σ PfK c δc
    ; p = λ c → proj₁
    ; q = λ c → proj₂
    ; ⊥ = 𝟘p
    ; exfalso = λ Pf0 c γc → ind𝟘p (Pf0 c γc) 
    ; ⊤ = 𝟙p
    ; tt = λ c x → *
    ; _⊃_ = λ K L → K → L
    ; ⊃intro = λ x c γx k → x c (γx ,Σ k)
    ; ⊃elim = λ PfKL c  (γc ,Σ k)→ PfKL c γc k
    ; _∧_ = λ K L → K ×p L
    ; ∧intro = λ PfK PfL c γc → (PfK c γc) ,Σ (PfL c γc)
    ; ∧elim₁ = λ PfKL c γc → proj₁ (PfKL c γc)
    ; ∧elim₂ = λ PfKL c γc → proj₂ (PfKL c γc)
    ; _∨_ = λ K L → K +p L
    ; ∨intro₁ = λ PfK c γc → inj₁ (PfK c γc)
    ; ∨intro₂ = λ PfL c γc → inj₂ (PfL c γc)
    ; ∨elim = λ {Γ}{K}{L}{C} PfKC PfLC PfKL c γc → ind+p (λ _ → C) (λ x → PfKC c (γc ,Σ x)) (λ y → PfLC c (γc ,Σ y)) (PfKL c γc)
    ; atom = atom
    }