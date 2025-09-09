{-# OPTIONS --prop #-}

open import lib

module 
    PropositionalLogic.IntNegative.Model
    (Atom : Set)
    where

record Model (i j k l : Level) : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    infixl 5 _▸_
    infixl 5 _,_
    infixr 5 _⊃_
    infixr 7 _∘_
    field
        Con   : Set i                                           -- Objects
        Sub   : Con → Con → Prop j                              -- Morphisms/Arrows
        _∘_   : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ          -- Composition arrows
        id    : ∀{Γ} → Sub Γ Γ                                  -- Identity arrows
        -- Our category comes with a terminal object
        ◆     : Con
        ε     : ∀{Γ} → Sub Γ ◆
        
        For   : Set k
        
        -- For Pf, we have additional operations _▸p_ (context extention) 
        -- Pf : For → Prop
        Pf    : Con → For → Prop l -- mivel Propba megy ezért nem kellenek a funktor törvények
        _[_] : ∀{Γ K} → Pf Γ K → ∀{Δ} → (γ : Sub Δ Γ) → Pf Δ K
        -- this functor is locally representable
        _▸_  : Con → For → Con
        _,_  : ∀{Γ Δ} → (γ : Sub Δ Γ) → ∀{K} → Pf Δ K → Sub Δ (Γ ▸ K)
        p    : ∀{Γ K} → Sub (Γ ▸ K) Γ
        q    : ∀{Γ K} → Pf  (Γ ▸ K) K
        
        ⊥       : For
        exfalso : ∀{Γ K} → Pf Γ ⊥ → Pf Γ K

        ⊤  : For
        tt : ∀{Γ} → Pf Γ ⊤

        _⊃_    : For → For → For
        ⊃intro : ∀{Γ K L} → Pf (Γ ▸ K) L → Pf Γ (K ⊃ L)
        ⊃elim  : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf (Γ ▸ K) L
        
        -- Atoms
        atom : Atom → For
        -- We do not have LEM

    -- De Bruijn indecies shorthands

    db0 = q

    db1 : ∀{Γ K L} → Pf (Γ ▸ K ▸ L) K 
    db1 = q [ p ]

    db2 : ∀{Γ K L M} → Pf (Γ ▸ K ▸ L ▸ M) K 
    db2 = (q [ p ]) [ p ]

    ¬_ : For → For
    ¬ A = A ⊃ ⊥

    -- modus ponens
    _$_ : ∀{Γ A B} → Pf Γ (A ⊃ B) → Pf Γ A → Pf Γ B
    PfAB $ PfA = ⊃elim PfAB [ id , PfA ]

    contrad : ∀{Γ K X} → Pf Γ K → Pf Γ (¬ K) → Pf Γ X
    contrad K ¬K = exfalso (¬K $ K)