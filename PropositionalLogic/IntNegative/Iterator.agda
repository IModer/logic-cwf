{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntNegative.Model
open import PropositionalLogic.IntNegative.Syntax

module PropositionalLogic.IntNegative.Iterator
    (Atom : Set) 
    where

-- The iterator of PropositionalLogic.IntNegative.Model meaning
-- that for any model M and the inital model I, there is a function I -> M

record Morphism{i i' j j' k k' l l' : Level}(A : Model Atom i j k l)(B : Model Atom i' j' k' l') : Set (i ⊔ j ⊔ k ⊔ l ⊔ i' ⊔ j' ⊔ k' ⊔ l') where
    private module A = Model A
    private module B = Model B
    field
        ⟦_⟧C  : A.Con → B.Con
        ⟦_⟧S  : {Γ Δ : A.Con} → A.Sub Δ Γ → B.Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
        ⟦_⟧F  : A.For → B.For
        ⟦_⟧Pf : {Γ : A.Con}{A : A.For} → A.Pf Γ A → B.Pf ⟦ Γ ⟧C ⟦ A ⟧F

        ⟦◆⟧   : ⟦ A.◆ ⟧C ≡  B.◆
        ⟦▸⟧   : {Γ : A.Con}{A : A.For} → ⟦ Γ A.▸ A ⟧C ≡  ⟦ Γ ⟧C B.▸ ⟦ A ⟧F
        ⟦⊃⟧   : {A B : A.For} → ⟦ A A.⊃ B ⟧F ≡ ⟦ A ⟧F B.⊃ ⟦ B ⟧F
        ⟦∧⟧   : {A B : A.For} → ⟦ A A.∧ B ⟧F ≡ ⟦ A ⟧F B.∧ ⟦ B ⟧F
        ⟦atom⟧ : {A : Atom} → ⟦ A.atom A ⟧F ≡ B.atom A

module Ite
    {i j k l : Level}(M : Model Atom i j k l) where

    private module M = Model M
    private module I = PropositionalLogic.IntNegative.Syntax Atom

    ⟦_⟧C : I.Con → M.Con
    ⟦_⟧S : {Γ Δ : I.Con} → I.Sub Δ Γ → M.Sub ⟦ Δ ⟧C ⟦ Γ ⟧C
    ⟦_⟧F : I.For → M.For
    ⟦_⟧Pf : {Γ : I.Con}{A : I.For} → I.Pf Γ A → M.Pf ⟦ Γ ⟧C ⟦ A ⟧F
    
    ⟦ ◆ ⟧C = M.◆
    ⟦ Γ ▸ A ⟧C = ⟦ Γ ⟧C M.▸ ⟦ A ⟧F

    ⟦ γ , PfA ⟧S = ⟦ γ ⟧S M., ⟦ PfA ⟧Pf
    ⟦ ε ⟧S = M.ε
    ⟦ p ⟧S = M.p
    ⟦ id ⟧S = M.id
    ⟦ γ ∘ δ ⟧S = ⟦ γ ⟧S M.∘ ⟦ δ ⟧S

    ⟦ ⊤ ⟧F = M.⊤
    ⟦ A ⊃ B ⟧F = ⟦ A ⟧F M.⊃ ⟦ B ⟧F 
    ⟦ A ∧ B ⟧F = ⟦ A ⟧F M.∧ ⟦ B ⟧F 
    ⟦ atom a ⟧F = M.atom a
    
    ⟦ PfA [ γ ] ⟧Pf = ⟦ PfA ⟧Pf M.[ ⟦ γ ⟧S ]
    ⟦ q ⟧Pf = M.q
    ⟦ tt ⟧Pf = M.tt
    ⟦ ⊃intro PfA ⟧Pf = M.⊃intro ⟦ PfA ⟧Pf
    ⟦ ⊃elim PfA ⟧Pf = M.⊃elim ⟦ PfA ⟧Pf
    ⟦ ∧intro PfA PfB ⟧Pf = M.∧intro ⟦ PfA ⟧Pf ⟦ PfB ⟧Pf
    ⟦ ∧elim₁ PfA ⟧Pf = M.∧elim₁ ⟦ PfA ⟧Pf
    ⟦ ∧elim₂ PfA ⟧Pf = M.∧elim₂ ⟦ PfA ⟧Pf

    Ite : Morphism (IM Atom) (M)
    Ite = record
        { ⟦_⟧C = ⟦_⟧C
        ; ⟦_⟧S = ⟦_⟧S
        ; ⟦_⟧F = ⟦_⟧F
        ; ⟦_⟧Pf = ⟦_⟧Pf
        ; ⟦◆⟧ = refl
        ; ⟦▸⟧ = refl
        ; ⟦⊃⟧ = refl
        ; ⟦∧⟧ = refl
        ; ⟦atom⟧ = refl
        }