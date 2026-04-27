open import lib

open import PropositionalLogic.IntFull.BoolModel
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.Examples
    (Atom : Set)
    (M : Model Atom lzero lzero lzero lzero)
    where

    open Model M

    prop2 : ∀{Γ A} → Pf Γ (¬ (¬ (¬ A))) → Pf Γ (¬ A)
    prop2 x = ⊃intro (contrad (⊃intro (contrad db1 db0)) (x [ p ]))

    lemHelperLemma : ∀{Γ A B C} → Pf Γ (((A ∨ B) ⊃ C) ⊃ ((A ⊃ C) ∧ (B ⊃ C)))
    lemHelperLemma = ⊃intro (∧intro (⊃intro (((q [ p ]) $ ∨intro₁ q))) (⊃intro ((q [ p ]) $ ∨intro₂ q)))

    lemhelp : ∀{Γ A B C} →  Pf Γ ((A ∨ B) ⊃ C) → Pf Γ ((A ⊃ C) ∧ (B ⊃ C))
    lemhelp Pf1 = ⊃elim lemHelperLemma [ (id , Pf1) ]

    doublenegintro : ∀{Γ A} → Pf Γ A → Pf Γ ((A ⊃ ⊥) ⊃ ⊥)
    doublenegintro PfA = ⊃intro (q $ (PfA [ p ]))