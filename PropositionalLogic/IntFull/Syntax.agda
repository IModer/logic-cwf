{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.Syntax
    --(P : Prop)
    (Atom : Set)
    where

-- Initial model or Syntax

infixl 5 _▸_
infixl 5 _,_
infixr 5 _⊃_
infixr 7 _∘_
infixr 6 _∨_
infixr 7 _∧_

data For : Set where
    ⊥ : For
    ⊤ : For
    _⊃_     : For → For → For
    _∧_     : For → For → For
    _∨_     : For → For → For
    atom : Atom → For

data Con : Set where
    ◆ : Con
    _▸_ : Con → For → Con 

data Pf : Con → For → Prop
data Sub : Con → Con → Prop

data Pf where    
    _[_] : ∀{Γ K} → Pf Γ K → ∀{Δ} → (γ : Sub Δ Γ) → Pf Δ K
    q    : ∀{Γ K} → Pf  (Γ ▸ K) K
    exfalso : ∀{Γ K} → Pf Γ ⊥ → Pf Γ K
    tt : ∀{Γ} → Pf Γ ⊤
    
    ⊃intro : ∀{Γ K L} → Pf (Γ ▸ K) L → Pf Γ (K ⊃ L)
    ⊃elim  : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf (Γ ▸ K) L
    
    ∧intro : ∀{Γ K L} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
    ∧elim₁  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
    ∧elim₂  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
    
    ∨intro₁ : ∀{Γ K L} → Pf Γ K → Pf Γ (K ∨ L) 
    ∨intro₂ : ∀{Γ K L} → Pf Γ L → Pf Γ (K ∨ L)
    ∨elim   : ∀{Γ K L C} → Pf (Γ ▸ K) C → Pf (Γ ▸ L) C → Pf Γ (K ∨ L) → Pf Γ C

data Sub where
    ε : ∀{Γ} → Sub Γ ◆
    _,_ : ∀{Γ Δ K} → (γ : Sub Δ Γ) → Pf Δ K → Sub Δ (Γ ▸ K)    
    p : ∀{Γ K} → Sub (Γ ▸ K) Γ
    id : ∀{Γ} → Sub Γ Γ
    _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

IM : Model Atom lzero lzero lzero lzero
IM = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = _∘_
    ; id = id
    ; ◆ = ◆
    ; ε = ε
    ; For = For
    ; Pf = Pf
    ; _[_] = λ x γ → x [ γ ]
    ; _▸_ = _▸_
    ; _,_ = λ γ x → (γ , x)
    ; p = p
    ; q = q
    ; ⊥ = ⊥
    ; exfalso = exfalso
    ; ⊤ = ⊤
    ; tt = tt
    ; _⊃_ = _⊃_
    ; ⊃intro = ⊃intro
    ; ⊃elim = ⊃elim
    ; _∧_ = _∧_
    ; ∧intro = ∧intro
    ; ∧elim₁ = ∧elim₁
    ; ∧elim₂ = ∧elim₂
    ; _∨_ = _∨_
    ; ∨intro₁ = ∨intro₁
    ; ∨intro₂ = ∨intro₂
    ; ∨elim = ∨elim
    ; atom = atom
    }
