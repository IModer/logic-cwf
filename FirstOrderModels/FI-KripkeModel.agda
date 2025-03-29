{-# OPTIONS --prop #-}

open import lib
open import FirstOrderIntuinistic

-- Kripke or Presheaf model
module FI-KripkeModel
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  {i}{j}{k} 
  (C : Extra.Preord {i}{j})
  (Tm : Extra.Psh {i}{j}{k} C)
 -- (Tm : C → Set)
 -- (rel : (n : ℕ) → relar n → (d : D) → ((Tm d) ^ n) → Prop)
 -- (fun : (n : ℕ) → funar n → (d : D) → ((Tm d) ^ n) → Tm d) where
  where

  KripkeModel : Model funar relar _ _ _ _ _
  KripkeModel = record
    { Con = Extra.Psh {i}{j}{k} C
    ; Sub = λ Δ Γ → Extra.NatTrans C Δ Γ
    ; _∘_ = λ {
        record { γ = γ₁ ; comm = comm₁ } 
        record { γ = γ₂ ; comm = comm₂ } → 
        record { γ = λ x → γ₁ (γ₂ x) ; comm = trans comm₁ ((cong γ₁ comm₂))}}
    ; id = record { γ = λ x → x ; comm = refl }
    ; ass = refl
    ; idl = refl
    ; idr = refl
    ; ◆ = record { Γ = {!   !} ; _⟨_⟩ = {!   !} ; ⟨∘≥⟩ = {!   !} ; ⟨id≥⟩ = {!   !} }
    ; ε = {!   !}
    ; ◆η = {!   !}
    ; For = {!   !}
    ; _[_]F = {!   !}
    ; [∘]F = {!   !}
    ; [id]F = {!   !}
    ; Pf = {!   !}
    ; _[_]p = {!   !}
    ; _▸p_ = {!   !}
    ; _,p_ = {!   !}
    ; pp = {!   !}
    ; qp = {!   !}
    ; ▸pβ₁ = {!   !}
    ; ▸pη = {!   !}
    ; ⊥ = {!   !}
    ; ⊥[] = {!   !}
    ; exfalso = {!   !}
    ; ⊤ = {!   !}
    ; ⊤[] = {!   !}
    ; tt = {!   !}
    ; _⊃_ = {!   !}
    ; ⊃[] = {!   !}
    ; ⊃intro = {!   !}
    ; ⊃elim = {!   !}
    ; _∧_ = {!   !}
    ; ∧[] = {!   !}
    ; ∧intro = {!   !}
    ; ∧elim₁ = {!   !}
    ; ∧elim₂ = {!   !}
    ; _∨_ = {!   !}
    ; ∨[] = {!   !}
    ; ∨elim = {!   !}
    ; ∨intro₁ = {!   !}
    ; ∨intro₂ = {!   !}
    ; Tm = λ Γ → Extra.NatTrans C Γ Tm
    ; _[_]t = λ x x₁ → {!   !}
    ; [∘]t = {!   !}
    ; [id]t = {!   !}
    ; _▸t = {!   !}
    ; _,t_ = {!   !}
    ; pt = {!   !}
    ; qt = {!   !}
    ; ▸tβ₁ = {!   !}
    ; ▸tβ₂ = {!   !}
    ; ▸tη = {!   !}
    ; Tms = {!   !}
    ; _[_]ts = {!   !}
    ; [∘]ts = {!   !}
    ; [id]ts = {!   !}
    ; εs = {!   !}
    ; ◆sη = {!   !}
    ; _,s_ = {!   !}
    ; π₁ = {!   !}
    ; π₂ = {!   !}
    ; ▸sβ₁ = {!   !}
    ; ▸sβ₂ = {!   !}
    ; ▸sη = {!   !}
    ; ,[] = {!   !}
    ; fun = {!   !}
    ; fun[] = {!   !}
    ; rel = {!   !}
    ; rel[] = {!   !}
    ; ∀' = {!   !}
    ; ∀[] = {!   !}
    ; ∀intro = {!   !}
    ; ∀elim = {!   !}
    ; ∃' = {!   !}
    ; ∃[] = {!   !}
    ; ∃intro = {!   !}
    ; ∃elim = {!   !}
    ; Eq = {!   !}
    ; Eq[] = {!   !}
    ; Eqrefl = {!   !}
    ; subst' = {!   !}
    } 