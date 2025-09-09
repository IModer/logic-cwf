{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.BoolModel
  (Atom : Set)
  (atom : Atom → Bool)
  where

  _⊃B_ : Bool → Bool → Bool
  x ⊃B true = true
  true ⊃B false = false
  false ⊃B false = true

  _∧B_ : Bool → Bool → Bool
  true ∧B true = true
  _ ∧B _ = false
  
  _∨B_ : Bool → Bool → Bool
  false ∨B false = false
  _ ∨B _ = true
  
  BoolM : Model Atom _ _ _ _
  BoolM = record
    { Con = Prop
    ; Sub = λ Γ Δ → Γ → Δ
    ; _∘_ = λ γ δ θ → γ (δ θ)
    ; id = λ γ → γ
    ; ◆ = 𝟙p
    ; ε = λ _ → *
    ; For = Bool
    ; Pf = λ Γ A → Γ → A ≡ true
    ; _[_] = λ z γ δ → z (γ δ)
    ; _▸_ = λ Γ A → Γ ×p (A ≡ true)
    ; _,_ = λ γ p Δ → γ Δ ,Σ p Δ
    ; p = proj₁
    ; q = proj₂
    ; ⊥ = false
    ; exfalso = λ γ x → ind𝟘p (ex (γ x))
    ; ⊤ = true
    ; tt = λ x → refl
    ; _⊃_ = _⊃B_
    ; ⊃intro = λ { {Γ} {true} {true} x γ → refl
                 ; {Γ} {true} {false} x γ → x (γ ,Σ refl)
                 ; {Γ} {false} {true} x γ → refl
                 ; {Γ} {false} {false} x γ → refl }
    ; ⊃elim = λ { {Γ} {true} {true} x γ → refl
                ; {Γ} {true} {false} x γ → x (proj₁ γ)}
    ; _∧_ = _∧B_
    ; ∧intro = λ { {Γ} {true} {true} x y γ → refl
                 ; {Γ} {true} {false} x y γ → y γ
                 ; {Γ} {false} {true} x y γ → x γ
                 ; {Γ} {false} {false} x y γ → y γ }
    ; ∧elim₁ = λ { {Γ} {true} {true} x γ → refl
                 ; {Γ} {true} {false} x γ → refl
                 ; {Γ} {false} {true} x γ → x γ
                 ; {Γ} {false} {false} x γ → x γ}
    ; ∧elim₂ = λ { {Γ} {true} {true} x γ → refl
                 ; {Γ} {true} {false} x γ → x γ
                 ; {Γ} {false} {true} x γ → refl
                 ; {Γ} {false} {false} x γ → x γ}
    ; _∨_ = _∨B_
    ; ∨intro₁ = λ { {Γ} {true} {true} x γ → refl
                  ; {Γ} {true} {false} x γ → refl
                  ; {Γ} {false} {true} x γ → refl
                  ; {Γ} {false} {false} x γ → x γ}
    ; ∨intro₂ = λ { {Γ} {true} {true} x γ → refl
                  ; {Γ} {true} {false} x γ → refl
                  ; {Γ} {false} {true} x γ → refl
                  ; {Γ} {false} {false} x γ → x γ}
    ; ∨elim   = λ { {Γ} {true} {true} x y z γ → y (γ ,Σ refl)
                  ; {Γ} {true} {false} x y z γ → x (γ ,Σ refl)
                  ; {Γ} {false} {true} x y z γ → y (γ ,Σ refl)
                  ; {Γ} {false} {false} x y z γ → y (γ ,Σ z γ)}
    ; atom = atom
    }      
    where
      ex : false ≡ true → 𝟘p
      ex ()