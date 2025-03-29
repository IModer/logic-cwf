{-# OPTIONS --prop --allow-unsolved-metas #-}

open import lib

module 
    PropositionalIntuinistic
    (Atom : Set)
    where


record Model (i j k l : Level) : Set (lsuc (i ⊔ j ⊔ k ⊔ l)) where
    infixl 5 _▸_
    infixl 5 _,_
    infixr 7 _∘_
    infixr 6 _⊃_
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

        _∧_    : For → For → For
        ∧intro : ∀{Γ K L} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
        ∧elim₁  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
        ∧elim₂  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B

        _∨_     : For → For → For
        ∨intro₁ : ∀{Γ K L} → Pf Γ K → Pf Γ (K ∨ L) 
        ∨intro₂ : ∀{Γ K L} → Pf Γ L → Pf Γ (K ∨ L)
        ∨elim   : ∀{Γ K L C} → Pf (Γ ▸ K) C → Pf (Γ ▸ L) C → Pf Γ (K ∨ L) → Pf Γ C

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
    PfAB $ PfA = ⊃elim PfAB [ (id , PfA) ]

    --_$'_ : ∀{Γ A B C} → Pf (Γ ▸ A) C → Pf (Γ ▸ (A ⊃ B)) C → Pf (Γ ▸ B) C
    --PfA $' PfAB = let PfA' = ⊃intro PfA in let PfAB' = ⊃intro PfAB in ⊃elim {!   !}

    contrad : ∀{Γ K X} → Pf Γ K → Pf Γ (¬ K) → Pf Γ X
    contrad K ¬K = exfalso (¬K $ K)

    -- weaken

    prop2 : ∀{Γ A} → Pf Γ (¬ (¬ (¬ A))) → Pf Γ (¬ A)
    prop2 x = ⊃intro (contrad (⊃intro (contrad db1 db0)) (x [ p ]))

    lemHelperLemma : ∀{Γ A B C} → Pf Γ (((A ∨ B) ⊃ C) ⊃ ((A ⊃ C) ∧ (B ⊃ C)))
    lemHelperLemma = ⊃intro (∧intro (⊃intro (((q [ p ]) $ ∨intro₁ q))) (⊃intro ((q [ p ]) $ ∨intro₂ q)))

    lemhelp : ∀{Γ A B C} →  Pf Γ ((A ∨ B) ⊃ C) → Pf Γ ((A ⊃ C) ∧ (B ⊃ C))
    lemhelp Pf1 = ⊃elim lemHelperLemma [ (id , Pf1) ]

    --lemHelperLemma₂ : ∀{Γ A} → Pf Γ (((A ⊃ ⊥) ∧ ((A ⊃ ⊥) ⊃ ⊥)) ⊃ ⊥ )
    --lemHelperLemma₂ = ⊃intro (∧elim (contrad (q [ p ]) q ))

    --lemhelp₂ : ∀{Γ A} → Pf Γ ((A ⊃ ⊥) ∧ ((A ⊃ ⊥) ⊃ ⊥)) → Pf Γ ⊥
    --lemhelp₂ Pf1 = ⊃elim lemHelperLemma₂ [ id , Pf1 ]

    doublenegintro : ∀{Γ A} → Pf Γ A → Pf Γ ((A ⊃ ⊥) ⊃ ⊥)
    doublenegintro PfA = ⊃intro (q $ (PfA [ p ]))

    --contraLemma : ∀{Γ A} → Pf Γ (((A ⊃ ⊥) ∧ (((((A ⊃ ⊥)) ⊃ ⊥) ⊃ ⊥) ⊃ ⊥)) ⊃ ⊥)
    --contraLemma = ⊃intro (contrad (doublenegintro (∧elim (q [ p ]))) (∧elim q))

    --contrahelp : ∀{Γ A} → Pf Γ ((A ⊃ ⊥) ∧ (((((A ⊃ ⊥)) ⊃ ⊥) ⊃ ⊥) ⊃ ⊥)) → Pf Γ ⊥
    --contrahelp Pf1 = ⊃elim contraLemma [ id , Pf1 ]
    
--    leminb : ∀{Γ A} → Pf Γ (((A ⊃ ⊥) ∨ (((((A ⊃ ⊥)) ⊃ ⊥) ⊃ ⊥) ⊃ ⊥)) ⊃ ⊥)


module I where
    -- Here we dont need mutual recursion
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

IM : Model lzero lzero lzero lzero
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
    where
        open I

