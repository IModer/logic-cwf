{-# OPTIONS --prop #-}

open import lib
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.BethModel 
  (Atom : Set) 
  where

record Preorder : Set₁ where
  no-eta-equality

  infix 4 _≥_
  infixl 9 _∘≥_
  field
    W : Set
    _≥_ : W → W → Prop
    id≥ : ∀ {i} → i ≥ i
    _∘≥_ : ∀ {i j k} → j ≥ i → k ≥ j → k ≥ i

-- Over a Category we have
-- Sieve, Topology, Sheaf

module Sh (P : Preorder) where
  open Preorder P

  -- A Sieve is an upper set of an element, with proof that its higher up

  -- A Sieve is also an "ideal" in a sense that its all morphisms with cod i in P that are closed under precomposition 
  
  record Sieve (i : W) : Set₁ where
    field
      R     : (w : W) -> w ≥ i -> Prop -- all morphisms with cod i st.
      restr : ∀ {j j≥i k} -> R j j≥i -> (k≥j : k ≥ j) -> R k (j≥i ∘≥ k≥j) -- they can be procomposed

  {-
  Sieves on objects are an equivalent way to talk about subobjects of representable functors 
  in a presheaf category in terms of the total sets of elements of such a subfunctor.
  -}

  open Sieve public renaming (R to ∣_∣)

  infix 0 ⟨_,_⟩⊩_
  ⟨_,_⟩⊩_ : ∀ {i} j → j ≥ i → Sieve i → Prop
  ⟨ j , j≥i ⟩⊩ R = ∣ R ∣ j j≥i

  infixl 9 _[_]ˢ
  _[_]ˢ : ∀ {i j} → Sieve i → j ≥ i → Sieve j
  ∣ R [ j≥i ]ˢ ∣ k k≥j = ⟨ k , j≥i ∘≥ k≥j ⟩⊩ R
  (R [ j≥i ]ˢ) .restr j⊩A k≥j = R .restr j⊩A k≥j

  -- A Topology over a category is choosing with morphisms are covers

  record Top : Set₁ where
    infix 4 _◁_
    infixl 9 _[_]ᶜ
    field
      _◁_     : (i : W) -> Sieve i -> Prop -- a subset of points can be a cover st.
      _[_]ᶜ   : ∀{i j R} -> i ◁ R -> (j≥i : j ≥ i) -> j ◁ (R [ j≥i ]ˢ)
      -- The whole set is always an cover
      maximal : ∀{i R} -> ⟨ i , id≥ ⟩⊩ R -> i ◁ R
      -- the union of covers is a cover
      local   : ∀{i R S} -> i ◁ R -> (∀{j} (j≥i : j ≥ i) -> ⟨ j , j≥i ⟩⊩ R -> j ◁ S [ j≥i ]ˢ) -> i ◁ S

  -- Then a Sheaf is just a presheaf that has glue
  record Sheaf(J : Top) : Set₁ where
    
    open Top J
    
    field
      A     : W -> Prop
      restr : ∀{i j} -> A i -> j ≥ i -> A j
      glue  : ∀{i R} -> i ◁ R -> (∀{j} (j≥i : j ≥ i) -> ⟨ j , j≥i ⟩⊩ R -> A j) -> A i 

  open Sheaf public renaming (A to ∣_∣)

module Semantics
  (P : Preorder)
  (open Sh P)
  (J : Top)
  (val : Atom -> Sheaf J)
  where

  open Preorder P
  open Top J

  𝟙Sh : Sheaf J
  𝟙Sh .Sh.∣_∣ _ = 𝟙p
  𝟙Sh .Sh.restr = λ _ _ -> *
  𝟙Sh .Sh.glue  = λ i◁R u -> *

  𝟘Sh : Sheaf J
  𝟘Sh .Sh.∣_∣ i = i ◁ sieve
    where
      sieve : Sieve i
      ∣ sieve ∣ j j≥i = 𝟘p
      sieve .restr () k≥j
  𝟘Sh .Sh.restr = _[_]ᶜ
  𝟘Sh .Sh.glue  = local

  _×Sh_ : Sheaf J -> Sheaf J -> Sheaf J
  (A ×Sh B) .Sh.∣_∣ i = ∣ A ∣ i ×p ∣ B ∣ i
  (A ×Sh B) .Sh.restr = λ {(Ai ,Σ Bi) j≥i → (Sh.restr A Ai j≥i) ,Σ Sh.restr B Bi j≥i}
  (A ×Sh B) .Sh.glue  = λ i◁R f -> (A .glue i◁R λ j≥i x → proj₁ (f j≥i x)) ,Σ (B .glue i◁R λ j≥i x → proj₂ (f j≥i x))
  
  _⇒Sh_ : Sheaf J -> Sheaf J -> Sheaf J
  (A ⇒Sh B) .Sh.∣_∣ i = ∀{j} -> j ≥ i -> ∣ A ∣ j -> ∣ B ∣ j
  (A ⇒Sh B) .Sh.restr = λ f j≥i k≥j Ak → f (j≥i ∘≥ k≥j) Ak
  (A ⇒Sh B) .Sh.glue  = λ i◁R f j≥i Aj -> B .glue (i◁R [ j≥i ]ᶜ) λ j≥k Rj → f (j≥i ∘≥ j≥k) Rj id≥ (Sh.restr A Aj j≥k)

  _+Sh_ : Sheaf J -> Sheaf J -> Sheaf J
  (A +Sh B) .Sh.∣_∣ i = i ◁ sieve
    where
      sieve : Sieve i
      sieve .Sh.∣_∣   = λ j j≥i → ∣ A ∣ j +p ∣ B ∣ j
      sieve .Sh.restr (inj₁ Aj) = λ k≥j → inj₁ (Sh.restr A Aj k≥j)
      sieve .Sh.restr (inj₂ Bj) = λ k≥j → inj₂ (Sh.restr B Bj k≥j)
  (A +Sh B) .Sh.restr = _[_]ᶜ
  (A +Sh B) .Sh.glue  = local

  Con : Set₁
  Con = Sheaf J

  Sub : Sheaf J -> Sheaf J -> Prop
  Sub Δ Γ = ∀{i} ->  ∣ Δ ∣ i -> ∣ Γ ∣ i
  
  ◆ : Con
  ◆ = 𝟙Sh

  ε : ∀{Γ} -> Sub Γ ◆
  ε = λ _ → *

  id : ∀{Γ} -> Sub Γ Γ
  id = λ z → z

  _∘_ : ∀{Γ Δ Θ} -> Sub Δ Γ -> Sub Θ Δ -> Sub Θ Γ
  (δ ∘ γ) Θi = δ (γ Θi)

  For : Set₁
  For = Sheaf J

  Pf  : Con -> For -> Prop
  Pf  = Sub

  _[_] : ∀{Γ K} → Pf Γ K → ∀{Δ} -> Sub Δ Γ → Pf Δ K
  (t [ γ ]) Δi = t (γ Δi)

  _▸_ : Con -> For -> Con
  _▸_ = _×Sh_

  _,_ : {Γ Δ : Con} → Sub Δ Γ → {K : For} → Pf Δ K → Sub Δ (Γ ▸ K)
  _,_ = λ γ p Δi → γ Δi ,Σ p Δi

  p : {Γ : Con} {K : For} → Sub (Γ ▸ K) Γ
  p = proj₁
  q : {Γ : Con} {K : For} → Pf (Γ ▸ K) K
  q = proj₂

  ⊥ : For
  ⊥ = 𝟘Sh

  exfalso : {Γ : Con} {K : For} → Pf Γ ⊥ → Pf Γ K
  exfalso {Γ} {K} Pf⊥ {i} Γi = K .glue (Pf⊥ Γi) λ j≥i ()

  ⊤ : For
  ⊤ = 𝟙Sh

  tt : ∀{Γ} -> Pf Γ ⊤
  tt = λ _ → *

  _⊃_ : For -> For -> For
  _⊃_ = _⇒Sh_

  ⊃intro : ∀{Γ K L} → Pf (Γ ▸ K) L → Pf Γ (K ⊃ L)
  ⊃intro {Γ} pfl Γi j≥i Kj = pfl (Γ .restr Γi j≥i ,Σ Kj)
  
  ⊃elim  : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf (Γ ▸ K) L
  ⊃elim pfkl (Γi ,Σ Ki) = pfkl Γi id≥ Ki

  _∧_ : For -> For -> For
  _∧_ = _×Sh_

  ∧intro : ∀{Γ K L} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
  ∧intro = λ PfK PfL Γi → PfK Γi ,Σ PfL Γi
  
  ∧elim₁  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
  ∧elim₁ = λ PfAB Γi → proj₁ (PfAB Γi)
  
  ∧elim₂  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
  ∧elim₂ = λ PfAB Γi → proj₂ (PfAB Γi)

  _∨_ : For -> For -> For
  _∨_ = _+Sh_
  
  ∨intro₁ : ∀{Γ K L} → Pf Γ K → Pf Γ (K ∨ L)
  ∨intro₁ PfK Γi = maximal (inj₁ (PfK Γi))

  ∨intro₂ : ∀{Γ K L} → Pf Γ L → Pf Γ (K ∨ L)
  ∨intro₂ PfL Γi = maximal (inj₂ (PfL Γi))

  ∨elim   : ∀{Γ K L C} → Pf (Γ ▸ K) C → Pf (Γ ▸ L) C → Pf Γ (K ∨ L) → Pf Γ C
  ∨elim {Γ} {K} {L} {C} PfKC PfLC PfKL {i} Γi = C .glue (PfKL Γi) λ 
    { j≥i (inj₁ x) → PfKC (Sh.restr Γ Γi j≥i ,Σ x)
    ; j≥i (inj₂ x) → PfLC (Sh.restr Γ Γi j≥i ,Σ x)}

  atom : Atom → For
  atom = val

  Beth : Model Atom _ _ _ _
  Beth = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = λ {Γ}{Δ}{Θ} -> _∘_ {Γ}{Δ}{Θ}
    ; id = λ {Γ} -> id {Γ}
    ; ◆ = ◆
    ; ε = λ {Γ} -> ε {Γ}
    ; For = For
    ; Pf = Pf
    ; _[_] = λ {Γ}{K} -> _[_] {Γ}{K}
    ; _▸_ = _▸_
    ; _,_ = λ {Γ}{K} -> _,_ {Γ}{K}
    ; p = λ {Γ}{K} -> p {Γ}{K}
    ; q = λ {Γ}{K} -> q {Γ}{K}
    ; ⊥ = ⊥
    ; exfalso = λ {Γ} {K} -> exfalso {Γ} {K}
    ; ⊤ = ⊤
    ; tt = λ {Γ} -> tt {Γ}
    ; _⊃_ = _⊃_
    ; ⊃intro = λ {Γ}{K}{L} -> ⊃intro {Γ}{K}{L}
    ; ⊃elim = λ {Γ}{K}{L} -> ⊃elim {Γ}{K}{L}
    ; _∧_ = _∧_
    ; ∧intro = λ {Γ}{K}{L} -> ∧intro {Γ}{K}{L}
    ; ∧elim₁ = λ {Γ}{K}{L} -> ∧elim₁ {Γ}{K}{L}
    ; ∧elim₂ = λ {Γ}{K}{L} -> ∧elim₂ {Γ}{K}{L}
    ; _∨_ = _∨_
    ; ∨intro₁ = λ {Γ}{K}{L}    -> ∨intro₁ {Γ}{K}{L}
    ; ∨intro₂ = λ {Γ}{K}{L}    -> ∨intro₂ {Γ}{K}{L}
    ; ∨elim   = λ {Γ}{K}{L}{C} -> ∨elim   {Γ}{K}{L}{C}
    ; atom = atom
    }

