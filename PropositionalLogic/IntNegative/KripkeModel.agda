{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntNegative.Model

module PropositionalLogic.IntNegative.KripkeModel
  (Atom : Set) 
  where

-- Tarski Model or Tarski semantics, everything is interpreted via the "standard" interpretation
module Semantics
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
    constructor Psh
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
    ; ⊤ = 𝟙PSh
    ; tt = λ _ → *
    ; _⊃_ = _⇒PSh_
    ; ⊃intro = λ {Γ}{K}{L} PfL Γw γ Kw' → PfL ((Γ ∶ Γw ⟨ γ ⟩) ,Σ Kw')
    ; ⊃elim = λ PfKL (Γw ,Σ Kw) → PfKL Γw id≥ Kw
    ; _∧_ = _×PSh_
    ; ∧intro = λ PfK PfL Γw → (PfK Γw) ,Σ (PfL Γw)
    ; ∧elim₁ = λ PfKL Γw → proj₁ (PfKL Γw)
    ; ∧elim₂ = λ PfKL Γw → proj₂ (PfKL Γw)
    ; atom = λ x → Psh (∣ x ∣pv) (_pv:_⟨_⟩ x)
    }

module Completeness where

  import PropositionalLogic.IntNegative.Syntax Atom as I
  -- We open Semantics with the specific W that allows us to show its iso to the Syntax

  open Semantics I.Con I.Sub I.id I._∘_ (λ a Γ → I.Pf Γ (I.atom a)) (λ a p → p I.[_])
  open import PropositionalLogic.IntNegative.Iterator
  open Ite Atom Kripke

  reify   : ∀{Γ} (A : I.For) -> ∣ ⟦ A ⟧F ∣ Γ -> I.Pf Γ A
  reflect : ∀{Γ} (A : I.For) -> I.Pf Γ A -> ∣ ⟦ A ⟧F ∣ Γ

  reify I.⊤        _         = I.tt
  reify (A I.⊃ B)  p         = I.⊃intro (reify B (p I.p (reflect A I.q)))
  reify (A I.∧ B) (pa ,Σ pb) = I.∧intro (reify A pa) (reify B pb)
  reify (I.atom a) p         = p
  
  reflect I.⊤        _ = *
  reflect (A I.⊃ B)  p = λ γ pa -> reflect B (I.⊃elim p I.[ γ I., (reify A pa) ])
  reflect (A I.∧ B)  p = (reflect A (I.∧elim₁ p)) ,Σ (reflect B (I.∧elim₂ p))
  reflect (I.atom a) p = p

  reflect-Con : ∀{Γ} Δ -> I.Sub Γ Δ -> ∣ ⟦ Δ ⟧C ∣ Γ
  reflect-Con I.◆       _ =  *
  reflect-Con (Δ I.▸ x) γ = (reflect-Con Δ (I.p I.∘ γ)) ,Σ (reflect x (I.q I.[ γ ]))

  open Model Kripke

  completeness : ∀{Γ} A -> Pf ⟦ Γ ⟧C ⟦ A ⟧F -> I.Pf Γ A
  completeness {Γ} A p = reify A (p (reflect-Con Γ I.id))

  soundness : ∀{Γ} A -> I.Pf Γ A -> Pf ⟦ Γ ⟧C ⟦ A ⟧F
  soundness A = ⟦_⟧Pf