{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntNegative.Model

module PropositionalLogic.IntNegative.Syntax
    (Atom : Set)
    where

-- Initial model or Syntax

infixl 5 _▸_
infixl 5 _,_
infixr 5 _⊃_
infixr 6 _∧_
infixr 7 _∘_

data For : Set where
    ⊤    : For
    _⊃_  : For → For → For
    _∧_  : For → For → For
    atom : Atom → For

data Con : Set where
    ◆   : Con
    _▸_ : Con → For → Con

data Pf  : Con → For → Prop
data Sub : Con → Con → Prop

data Pf where
    _[_] : ∀{Γ K} → Pf Γ K → ∀{Δ} → (γ : Sub Δ Γ) → Pf Δ K
    q    : ∀{Γ K} → Pf  (Γ ▸ K) K
    
    tt : ∀{Γ} → Pf Γ ⊤
    
    ∧intro : ∀{Γ K L} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
    ∧elim₁ : ∀{Γ K L} → Pf Γ (K ∧ L) → Pf Γ K
    ∧elim₂ : ∀{Γ K L} → Pf Γ (K ∧ L) → Pf Γ L
    
    ⊃intro : ∀{Γ K L} → Pf (Γ ▸ K) L → Pf Γ (K ⊃ L)
    ⊃elim  : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf (Γ ▸ K) L

data Sub where
    ε   : ∀{Γ} → Sub Γ ◆
    _,_ : ∀{Γ Δ K} → (γ : Sub Δ Γ) → Pf Δ K → Sub Δ (Γ ▸ K)    
    p   : ∀{Γ K} → Sub (Γ ▸ K) Γ
    id  : ∀{Γ} → Sub Γ Γ
    _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

IM : Model Atom _ _ _ _
IM = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = _∘_
    ; id = id
    ; ◆ = ◆
    ; ε = ε
    ; For = For
    ; Pf = Pf
    ; _[_] = _[_]
    ; _▸_ = _▸_
    ; _,_ = λ γ x → (γ , x)
    ; p = p
    ; q = q
    ; ⊤ = ⊤
    ; tt = tt
    ; _⊃_ = _⊃_
    ; ⊃intro = ⊃intro
    ; ⊃elim = ⊃elim
    ; ∧intro = ∧intro
    ; ∧elim₁ = ∧elim₁
    ; ∧elim₂ = ∧elim₂
    ; atom = atom
    }
