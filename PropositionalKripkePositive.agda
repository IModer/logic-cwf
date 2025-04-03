{-# OPTIONS --without-K --prop #-}

module PropositionalKripkePositive (Atom : Set) where

module I where
  infixr 7 _∧_
  infixr 5 _⇒_
  infixr 6 _∨_
  data Form : Set where
    atom : Atom → Form
    ⊤ : Form
    _∧_ : Form → Form → Form
    _⇒_ : Form → Form → Form
    ⊥ : Form
    _∨_ : Form → Form → Form

  infixl 2 _▹_
  data Ctx : Set where
    ◇ : Ctx
    _▹_ : Ctx → Form → Ctx

  infix 0 _⊢ˢ_ _⊢_
  data _⊢ˢ_ : Ctx → Ctx → Prop
  data _⊢_ : Ctx → Form → Prop

  infixl 9 _∘_
  infixl 4 _,_
  data _⊢ˢ_ where
    id : ∀ {Γ} → Γ ⊢ˢ Γ
    _∘_ : ∀ {Δ Γ Θ} → Δ ⊢ˢ Γ → Θ ⊢ˢ Δ → Θ ⊢ˢ Γ
    ε : ∀ {Γ} → Γ ⊢ˢ ◇
    p : ∀ {Γ A} → Γ ▹ A ⊢ˢ Γ
    _,_ : ∀ {Δ Γ A} → Δ ⊢ˢ Γ → Δ ⊢ A → Δ ⊢ˢ Γ ▹ A

  infixl 9 _[_]
  data _⊢_ where
    _[_] : ∀ {Γ A Δ} → Γ ⊢ A → Δ ⊢ˢ Γ → Δ ⊢ A
    q : ∀ {Γ A} → Γ ▹ A ⊢ A
    ⊤ᵢ : ∀ {Γ} → Γ ⊢ ⊤
    ∧ₑ₁ : ∀ {Γ A B} → Γ ⊢ A ∧ B → Γ ⊢ A
    ∧ₑ₂ : ∀ {Γ A B} → Γ ⊢ A ∧ B → Γ ⊢ B
    ∧ᵢ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
    ⇒ₑ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    ⇒ᵢ : ∀ {Γ A B} → Γ ▹ A ⊢ B → Γ ⊢ A ⇒ B
    ⊥ₑ : ∀ {Γ A} → Γ ⊢ ⊥ → Γ ⊢ A
    ∨ᵢ₁ : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ A ∨ B
    ∨ᵢ₂ : ∀ {Γ A B} → Γ ⊢ B → Γ ⊢ A ∨ B
    ∨ₑ : ∀ {Γ A B C} → Γ ▹ A ⊢ C → Γ ▹ B ⊢ C → Γ ⊢ A ∨ B → Γ ⊢ C

module M where
  record ⊤ : Prop where
    constructor tt

  infixr 2 _∧_
  record _∧_ (A B : Prop) : Prop where
    constructor _,,_
    field
      fst : A
      snd : B

  open _∧_ public

  data ⊥ : Prop where

  infixr 1 _∨_
  data _∨_ (A B : Prop) : Prop where
    inl : A → A ∨ B
    inr : B → A ∨ B

open M public hiding (⊤; _∧_; ⊥; _∨_)

-- Prop-valued category
record Preorder : Set₁ where
  no-eta-equality

  infix 4 _≥_
  infixl 9 _∙_
  field
    W : Set
    _≥_ : W → W → Prop
    refl : ∀ {i} → i ≥ i
    _∙_ : ∀ {i j k} → j ≥ i → k ≥ j → k ≥ i

-- Prop-valued presheaf
record Upset (P : Preorder) : Set₁ where
  no-eta-equality

  open Preorder P
  field
    A : W → Prop
    restr : ∀ {i j} → A i → j ≥ i → A j

open Upset public renaming (A to ∣_∣)

module Sem (P : Preorder) (val : Atom → Upset P) where
  open Preorder P

  infix 0 _⊩_
  _⊩_ : W → Upset P → Prop
  i ⊩ A = ∣ A ∣ i

  infix 0 _⊨_
  -- Superset
  record _⊨_ (Δ Γ : Upset P) : Prop where
    field
      γ : ∀ {i} → i ⊩ Δ → i ⊩ Γ

  open _⊨_ public renaming (γ to ∣_∣)

  Ctx : Set₁
  Ctx = Upset P

  id : ∀ {Γ} → Γ ⊨ Γ
  ∣ id ∣ i⊩Γ = i⊩Γ

  infixl 9 _∘_
  _∘_ : ∀ {Δ Γ Θ} → Δ ⊨ Γ → Θ ⊨ Δ → Θ ⊨ Γ
  ∣ γ ∘ δ ∣ i⊩Θ = ∣ γ ∣ (∣ δ ∣ i⊩Θ)

  Form : Set₁
  Form = Upset P

  infixl 9 _[_]
  _[_] : ∀ {Γ A Δ} → Γ ⊨ A → Δ ⊨ Γ → Δ ⊨ A
  _[_] = _∘_

  ◇ : Ctx
  ∣ ◇ ∣ i = M.⊤
  ◇ .restr tt j≥i = tt

  ε : ∀ {Γ} → Γ ⊨ ◇
  ∣ ε ∣ γ = tt

  infixl 2 _▹_
  _▹_ : Ctx → Form → Ctx
  ∣ Γ ▹ A ∣ i = (i ⊩ Γ) M.∧ (i ⊩ A)
  (Γ ▹ A) .restr (i⊩Γ ,, i⊩A) j≥i = Γ .restr i⊩Γ j≥i ,, A .restr i⊩A j≥i

  p : ∀ {Γ A} → Γ ▹ A ⊨ Γ
  ∣ p ∣ (i⊩Γ ,, i⊩A) = i⊩Γ

  q : ∀ {Γ A} → Γ ▹ A ⊨ A
  ∣ q ∣ (i⊩Γ ,, i⊩A) = i⊩A

  infixl 4 _,_
  _,_ : ∀ {Δ Γ A} → Δ ⊨ Γ → Δ ⊨ A → Δ ⊨ Γ ▹ A
  ∣ γ , a ∣ i⊩Δ = ∣ γ ∣ i⊩Δ ,, ∣ a ∣ i⊩Δ

  ⊤ : Form
  ⊤ = ◇

  ⊤ᵢ : ∀ {Γ} → Γ ⊨ ⊤
  ⊤ᵢ = ε

  infixr 7 _∧_
  _∧_ : Form → Form → Form
  _∧_ = _▹_

  ∧ₑ₁ : ∀ {Γ A B} → Γ ⊨ A ∧ B → Γ ⊨ A
  ∧ₑ₁ = p ∘_

  ∧ₑ₂ : ∀ {Γ A B} → Γ ⊨ A ∧ B → Γ ⊨ B
  ∧ₑ₂ = q ∘_

  ∧ᵢ : ∀ {Γ A B} → Γ ⊨ A → Γ ⊨ B → Γ ⊨ A ∧ B
  ∧ᵢ = _,_

  infixr 5 _⇒_
  _⇒_ : Form → Form → Form
  ∣ A ⇒ B ∣ i = ∀ {j} → j ≥ i → j ⊩ A → j ⊩ B
  (A ⇒ B) .restr f j≥i k≥j k⊩A = f (j≥i ∙ k≥j) k⊩A

  ⇒ₑ : ∀ {Γ A B} → Γ ⊨ A ⇒ B → Γ ⊨ A → Γ ⊨ B
  ∣ ⇒ₑ r a ∣ i⊩Γ = ∣ r ∣ i⊩Γ refl (∣ a ∣ i⊩Γ)

  ⇒ᵢ : ∀ {Γ A B} → Γ ▹ A ⊨ B → Γ ⊨ A ⇒ B
  ∣ ⇒ᵢ {Γ} b ∣ i⊩Γ j≥i j⊩A = ∣ b ∣ (Γ .restr i⊩Γ j≥i ,, j⊩A)

  ⊥ : Form
  ∣ ⊥ ∣ i = M.⊥
  ⊥ .restr () j≥i

  ⊥ₑ : ∀ {Γ A} → Γ ⊨ ⊥ → Γ ⊨ A
  ∣ ⊥ₑ r ∣ i⊩Γ with () ← ∣ r ∣ i⊩Γ

  infixr 6 _∨_
  _∨_ : Form → Form → Form
  ∣ A ∨ B ∣ i = ∣ A ∣ i M.∨ ∣ B ∣ i
  (A ∨ B) .restr (inl i⊩A) j≥i = inl (A .restr i⊩A j≥i)
  (A ∨ B) .restr (inr i⊩B) j≥i = inr (B .restr i⊩B j≥i)

  ∨ᵢ₁ : ∀ {Γ A B} → Γ ⊨ A → Γ ⊨ A ∨ B
  ∣ ∨ᵢ₁ a ∣ i⊩Γ = inl (∣ a ∣ i⊩Γ)

  ∨ᵢ₂ : ∀ {Γ A B} → Γ ⊨ B → Γ ⊨ A ∨ B
  ∣ ∨ᵢ₂ b ∣ i⊩Γ = inr (∣ b ∣ i⊩Γ)

  ∨ₑ : ∀ {Γ A B C} → Γ ▹ A ⊨ C → Γ ▹ B ⊨ C → Γ ⊨ A ∨ B → Γ ⊨ C
  ∣ ∨ₑ c₁ c₂ r ∣ i⊩Γ with ∣ r ∣ i⊩Γ
  ... | inl i⊩A = ∣ c₁ ∣ (i⊩Γ ,, i⊩A)
  ... | inr i⊩B = ∣ c₂ ∣ (i⊩Γ ,, i⊩B)

  open I using (_⊢ˢ_; _⊢_)

  ⟦_⟧ꟳ : I.Form → Form
  ⟦ I.atom A ⟧ꟳ = val A
  ⟦ I.⊤ ⟧ꟳ = ⊤
  ⟦ A I.∧ B ⟧ꟳ = ⟦ A ⟧ꟳ ∧ ⟦ B ⟧ꟳ
  ⟦ A I.⇒ B ⟧ꟳ = ⟦ A ⟧ꟳ ⇒ ⟦ B ⟧ꟳ
  ⟦ I.⊥ ⟧ꟳ = ⊥
  ⟦ A I.∨ B ⟧ꟳ = ⟦ A ⟧ꟳ ∨ ⟦ B ⟧ꟳ

  ⟦_⟧ꟲ : I.Ctx → Ctx
  ⟦ I.◇ ⟧ꟲ = ◇
  ⟦ Γ I.▹ A ⟧ꟲ = ⟦ Γ ⟧ꟲ ▹ ⟦ A ⟧ꟳ

  ⟦_⟧ˢ : ∀ {Δ Γ} → Δ ⊢ˢ Γ → ⟦ Δ ⟧ꟲ ⊨ ⟦ Γ ⟧ꟲ
  ⟦_⟧ᵖ : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧ꟲ ⊨ ⟦ A ⟧ꟳ

  ⟦ I.id ⟧ˢ = id
  ⟦ γ I.∘ δ ⟧ˢ = ⟦ γ ⟧ˢ ∘ ⟦ δ ⟧ˢ
  ⟦ I.ε ⟧ˢ = ε
  ⟦ I.p ⟧ˢ = p
  ⟦ γ I., a ⟧ˢ = ⟦ γ ⟧ˢ , ⟦ a ⟧ᵖ

  ⟦ a I.[ γ ] ⟧ᵖ = ⟦ a ⟧ᵖ [ ⟦ γ ⟧ˢ ]
  ⟦ I.q ⟧ᵖ = q
  ⟦ I.⊤ᵢ ⟧ᵖ = ⊤ᵢ
  ⟦ I.∧ₑ₁ r ⟧ᵖ = ∧ₑ₁ ⟦ r ⟧ᵖ
  ⟦ I.∧ₑ₂ r ⟧ᵖ = ∧ₑ₂ ⟦ r ⟧ᵖ
  ⟦ I.∧ᵢ a b ⟧ᵖ = ∧ᵢ ⟦ a ⟧ᵖ ⟦ b ⟧ᵖ
  ⟦ I.⇒ₑ r a ⟧ᵖ = ⇒ₑ ⟦ r ⟧ᵖ ⟦ a ⟧ᵖ
  ⟦ I.⇒ᵢ b ⟧ᵖ = ⇒ᵢ ⟦ b ⟧ᵖ
  ⟦ I.⊥ₑ r ⟧ᵖ = ⊥ₑ ⟦ r ⟧ᵖ
  ⟦ I.∨ᵢ₁ a ⟧ᵖ = ∨ᵢ₁ ⟦ a ⟧ᵖ
  ⟦ I.∨ᵢ₂ b ⟧ᵖ = ∨ᵢ₂ ⟦ b ⟧ᵖ
  ⟦ I.∨ₑ c₁ c₂ r ⟧ᵖ = ∨ₑ ⟦ c₁ ⟧ᵖ ⟦ c₂ ⟧ᵖ ⟦ r ⟧ᵖ

module Compl where
  open I

  P : Preorder
  P .Preorder.W = Ctx
  P .Preorder._≥_ = _⊢ˢ_
  P .Preorder.refl = id
  P .Preorder._∙_ = _∘_

  val : Atom → Upset P
  ∣ val A ∣ Γ = Γ ⊢ atom A
  val A .restr = _[_]

  open Sem P val using (_⊩_; _⊨_; ∣_∣; ⟦_⟧ꟲ; ⟦_⟧ꟳ; ⟦_⟧ˢ; ⟦_⟧ᵖ)

  reify : ∀ {Γ} A → Γ ⊩ ⟦ A ⟧ꟳ → Γ ⊢ A
  reflect : ∀ {Γ} A → Γ ⊢ A → Γ ⊩ ⟦ A ⟧ꟳ

  reify (atom A) a = a
  reify ⊤ tt = ⊤ᵢ
  reify (A ∧ B) (Γ⊩A ,, Γ⊩B) = ∧ᵢ (reify A Γ⊩A) (reify B Γ⊩B)
  reify (A ⇒ B) f = ⇒ᵢ (reify B (f p (reflect A q)))
  reify ⊥ ()
  reify (A ∨ B) (inl a) = ∨ᵢ₁ (reify A a)
  reify (A ∨ B) (inr b) = ∨ᵢ₂ (reify B b)

  reflect (atom A) a = a
  reflect ⊤ r = tt
  reflect (A ∧ B) r = reflect A (∧ₑ₁ r) ,, reflect B (∧ₑ₂ r)
  reflect (A ⇒ B) r γ Δ⊩A = reflect B (⇒ₑ (r [ γ ]) (reify A Δ⊩A))
  reflect ⊥ a = {!!}
  reflect (A ∨ B) r = {!∨ₑ ? ? r!}

  reflectꟲ : ∀ {Δ} Γ → Δ ⊢ˢ Γ → Δ ⊩ ⟦ Γ ⟧ꟲ
  reflectꟲ ◇ σ = tt
  reflectꟲ (Γ ▹ A) σ = reflectꟲ Γ (p ∘ σ) ,, reflect A (q [ σ ])

  complete : ∀ {Γ A} → ⟦ Γ ⟧ꟲ ⊨ ⟦ A ⟧ꟳ → Γ ⊢ A
  complete {Γ} {A} a = reify A (∣ a ∣ (reflectꟲ Γ id))
