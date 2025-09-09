{-# OPTIONS --prop #-}


module PropositionalLogic.Classical.Syntax
    (Atom : Set)
    where

open import lib
open import PropositionalLogic.Classical.Model
open import PropositionalLogic.IntFull.Syntax Atom renaming (IM to IMI) hiding (Pf; Sub)
open import PropositionalLogic.IntFull.Model renaming (Model to ModelI)


-- Initial model or Syntax
data Sub : Con → Con → Prop
data Pf : Con → For → Prop where
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
    dne   : {Γ : Con}{A : For} → Pf Γ (((A ⊃ ⊥) ⊃ ⊥) ⊃ A)

data Sub where
    ε : ∀{Γ} → Sub Γ ◆
    _,_ : ∀{Γ Δ K} → (γ : Sub Δ Γ) → Pf Δ K → Sub Δ (Γ ▸ K)    
    p : ∀{Γ K} → Sub (Γ ▸ K) Γ
    id : ∀{Γ} → Sub Γ Γ
    _∘_ : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ

IM : Model Atom lzero lzero lzero lzero
IM = record { super =
    record
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
    ; _,_ = λ γ x → γ , x
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
    ; atom = atom}
    ; dne = dne }