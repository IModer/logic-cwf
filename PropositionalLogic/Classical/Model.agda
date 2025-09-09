{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntFull.Model renaming (Model to ModelI)

module PropositionalLogic.Classical.Model
    (Atom : Set)
    where

record Model (i j k l : Level) : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    field
        super : ModelI Atom i j k l
    
    private module E = ModelI super
    open E
    -- A logic is classical if it has double negation elemination
    field
        dne : {Γ : E.Con}{A : E.For} → E.Pf Γ (¬ ¬ A E.⊃ A)
