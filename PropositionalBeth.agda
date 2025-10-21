{-# OPTIONS --without-K --prop --hidden-argument-puns #-}

module PropositionalBeth (Atom : Set) where

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

  infixl 4 _▹_
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
    _∘_ : ∀ {Γ Δ Θ} → Δ ⊢ˢ Γ → Θ ⊢ˢ Δ → Θ ⊢ˢ Γ
    ε : ∀ {Γ} → Γ ⊢ˢ ◇
    p : ∀ {Γ A} → Γ ▹ A ⊢ˢ Γ
    _,_ : ∀ {Γ Δ A} → Δ ⊢ˢ Γ → Δ ⊢ A → Δ ⊢ˢ Γ ▹ A

  infixl 9 _[_]
  data _⊢_ where
    _[_] : ∀ {Γ Δ A} → Γ ⊢ A → Δ ⊢ˢ Γ → Δ ⊢ A
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

module Sh (P : Preorder) where
  open Preorder P

  record Sieve (i : W) : Set₁ where
    field
      R : (j : W) → j ≥ i → Prop
      restr : ∀ {j j≥i k} → R j j≥i → (k≥j : k ≥ j) → R k (j≥i ∙ k≥j)

  open Sieve public renaming (R to ∣_∣)

  infix 0 ⟨_,_⟩⊩_
  ⟨_,_⟩⊩_ : ∀ {i} j → j ≥ i → Sieve i → Prop
  ⟨ j , j≥i ⟩⊩ R = ∣ R ∣ j j≥i

  infixl 9 _[_]ˢ
  _[_]ˢ : ∀ {i j} → Sieve i → j ≥ i → Sieve j
  ∣ R [ j≥i ]ˢ ∣ k k≥j = ⟨ k , j≥i ∙ k≥j ⟩⊩ R
  (R [ j≥i ]ˢ) .restr j⊩A k≥j = R .restr j⊩A k≥j

  -- Grothendieck topology
  record Top : Set₁ where
    no-eta-equality

    infix 4 _◁_
    infixl 9 _[_]ᶜ
    field
      _◁_ : (i : W) → Sieve i → Prop
      _[_]ᶜ : ∀ {i R j} → i ◁ R → (j≥i : j ≥ i) → j ◁ R [ j≥i ]ˢ
      maximal : ∀ {i R} → ⟨ i , refl ⟩⊩ R → i ◁ R
      local :
        ∀ {i R S} →
        i ◁ R → (∀ {j} (j≥i : j ≥ i) → ⟨ j , j≥i ⟩⊩ R → j ◁ S [ j≥i ]ˢ) → i ◁ S

  -- Prop-valued sheaf
  record Sheaf (J : Top) : Set₁ where
    no-eta-equality
    open Top J

    field
      A : W → Prop
      restr : ∀ {i j} → A i → j ≥ i → A j
      glue :
        ∀ {i R} → i ◁ R → (∀ {j} (j≥i : j ≥ i) → ⟨ j , j≥i ⟩⊩ R → A j) → A i

  open Sheaf public renaming (A to ∣_∣)

module Sem (P : Preorder) (open Sh P) (J : Top) (val : Atom → Sheaf J) where
  open Preorder P
  open Top J

  infix 0 _⊩_
  _⊩_ : W → Sheaf J → Prop
  i ⊩ A = ∣ A ∣ i

  infix 0 _⊨_
  -- Superset
  record _⊨_ (Δ Γ : Sheaf J) : Prop where
    field
      γ : ∀ {i} → i ⊩ Δ → i ⊩ Γ

  open _⊨_ public renaming (γ to ∣_∣)

  Ctx : Set₁
  Ctx = Sheaf J

  id : ∀ {Γ} → Γ ⊨ Γ
  ∣ id ∣ i⊩Γ = i⊩Γ

  infixl 9 _∘_
  _∘_ : ∀ {Δ Γ Θ} → Δ ⊨ Γ → Θ ⊨ Δ → Θ ⊨ Γ
  ∣ γ ∘ δ ∣ i⊩Θ = ∣ γ ∣ (∣ δ ∣ i⊩Θ)

  Form : Set₁
  Form = Sheaf J

  infixl 9 _[_]
  _[_] : ∀ {Γ A Δ} → Γ ⊨ A → Δ ⊨ Γ → Δ ⊨ A
  _[_] = _∘_

  ◇ : Ctx
  ∣ ◇ ∣ i = M.⊤
  ◇ .restr tt j≥i = tt
  ◇ .glue i◁R f = tt

  ε : ∀ {Γ} → Γ ⊨ ◇
  ∣ ε ∣ γ = tt

  _▹_ : Ctx → Form → Ctx
  ∣ Γ ▹ A ∣ i = (i ⊩ Γ) M.∧ (i ⊩ A)
  (Γ ▹ A) .restr (i⊩Γ ,, i⊩A) j≥i = Γ .restr i⊩Γ j≥i ,, A .restr i⊩A j≥i
  (Γ ▹ A) .glue i◁R f =
    Γ .glue i◁R (λ j≥i j⊩R → f j≥i j⊩R .fst) ,,
    A .glue i◁R (λ j≥i j⊩R → f j≥i j⊩R .snd)

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
  (A ⇒ B) .glue i◁R f j≥i j⊩A =
    B .glue (i◁R [ j≥i ]ᶜ) λ k≥j k⊩R →
      f (j≥i ∙ k≥j) k⊩R refl (A .restr j⊩A k≥j)

  ⇒ₑ : ∀ {Γ A B} → Γ ⊨ A ⇒ B → Γ ⊨ A → Γ ⊨ B
  ∣ ⇒ₑ r a ∣ i⊩Γ = ∣ r ∣ i⊩Γ refl (∣ a ∣ i⊩Γ)

  ⇒ᵢ : ∀ {Γ A B} → Γ ▹ A ⊨ B → Γ ⊨ A ⇒ B
  ∣ ⇒ᵢ {Γ} b ∣ i⊩Γ j≥i j⊩A = ∣ b ∣ (Γ .restr i⊩Γ j≥i ,, j⊩A)

  ⊥ : Form
  ∣ ⊥ ∣ i = i ◁ sieve
    where
    sieve : Sieve i
    ∣ sieve ∣ j j≥i = M.⊥
    sieve .restr () k≥j
  ⊥ .restr = _[_]ᶜ
  ⊥ .glue = local

  ⊥ₑ : ∀ {Γ A} → Γ ⊨ ⊥ → Γ ⊨ A
  ∣ ⊥ₑ {A} r ∣ i⊩Γ = A .glue (∣ r ∣ i⊩Γ) λ j≥i ()

  infixr 6 _∨_
  _∨_ : Form → Form → Form
  ∣ A ∨ B ∣ i = i ◁ sieve
    where
    sieve : Sieve i
    ∣ sieve ∣ j j≥i = (j ⊩ A) M.∨ (j ⊩ B)
    sieve .restr (inl j⊩A) k≥j = inl (A .restr j⊩A k≥j)
    sieve .restr (inr j⊩B) k≥j = inr (B .restr j⊩B k≥j)
  (A ∨ B) .restr = _[_]ᶜ
  (A ∨ B) .glue = local

  ∨ᵢ₁ : ∀ {Γ A B} → Γ ⊨ A → Γ ⊨ A ∨ B
  ∣ ∨ᵢ₁ a ∣ i⊩Γ = maximal (inl (∣ a ∣ i⊩Γ))

  ∨ᵢ₂ : ∀ {Γ A B} → Γ ⊨ B → Γ ⊨ A ∨ B
  ∣ ∨ᵢ₂ b ∣ i⊩Γ = maximal (inr (∣ b ∣ i⊩Γ))

  ∨ₑ : ∀ {Γ A B C} → Γ ▹ A ⊨ C → Γ ▹ B ⊨ C → Γ ⊨ A ∨ B → Γ ⊨ C
  ∣ ∨ₑ {Γ} {C} c₁ c₂ r ∣ i⊩Γ = C .glue (∣ r ∣ i⊩Γ) λ where
    j≥i (inl j⊩A) → ∣ c₁ ∣ (Γ .restr i⊩Γ j≥i ,, j⊩A)
    j≥i (inr j⊩B) → ∣ c₂ ∣ (Γ .restr i⊩Γ j≥i ,, j⊩B)

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

  open Sh P

  infix 4 _◁_
  {-# NO_UNIVERSE_CHECK #-}
  data _◁_ (Γ : Ctx) : Sieve Γ → Prop where
    maximal : ∀ {R} → ⟨ Γ , id ⟩⊩ R → Γ ◁ R
    ◁-⊥ : ∀ {R} → Γ ⊢ ⊥ → Γ ◁ R
    ◁-∨ :
      ∀ {A B R} →
      (∀ {Δ} (γ : Δ ⊢ˢ Γ) → Δ ⊢ A → Δ ◁ R [ γ ]ˢ) →
      (∀ {Δ} (γ : Δ ⊢ˢ Γ) → Δ ⊢ B → Δ ◁ R [ γ ]ˢ) →
      Γ ⊢ A ∨ B → Γ ◁ R

  _[_]ᶜ : ∀ {Γ R Δ} → Γ ◁ R → (γ : Δ ⊢ˢ Γ) → Δ ◁ R [ γ ]ˢ
  maximal {R} Γ⊩R [ γ ]ᶜ = maximal (R .restr Γ⊩R γ)
  ◁-⊥ r [ γ ]ᶜ = ◁-⊥ (r [ γ ])
  ◁-∨ f g r [ γ ]ᶜ = ◁-∨ (λ δ a → f (γ ∘ δ) a) (λ δ b → g (γ ∘ δ) b) (r [ γ ])

  local :
    ∀ {Γ R S} →
    Γ ◁ R → (∀ {Δ} (γ : Δ ⊢ˢ Γ) → ⟨ Δ , γ ⟩⊩ R → Δ ◁ S [ γ ]ˢ) → Γ ◁ S
  local (maximal Γ⊩R) f = f id Γ⊩R
  local (◁-⊥ r) f = ◁-⊥ r
  local (◁-∨ f g r) h =
    ◁-∨
      (λ γ a → local (f γ a) λ δ Θ⊩R → h (γ ∘ δ) Θ⊩R)
      (λ γ b → local (g γ b) λ δ Θ⊩R → h (γ ∘ δ) Θ⊩R)
      r

  J : Top
  J .Top._◁_ = _◁_
  J .Top._[_]ᶜ = _[_]ᶜ
  J .Top.maximal = maximal
  J .Top.local = local

  val : Atom → Sheaf J
  ∣ val A ∣ Γ = Γ ◁ sieve
    module val where
    sieve : Sieve Γ
    ∣ sieve ∣ Δ γ = Δ ⊢ atom A
    sieve .restr a δ = a [ δ ]
  val A .restr = _[_]ᶜ
  val A .glue = local

  open Sem P J val using (_⊩_; _⊨_; ∣_∣; ⟦_⟧ꟲ; ⟦_⟧ꟳ; ⟦_⟧ˢ; ⟦_⟧ᵖ)

  reify : ∀ {Γ} A → Γ ⊩ ⟦ A ⟧ꟳ → Γ ⊢ A
  reify-atom : ∀ {Γ} A → Γ ⊩ ⟦ atom A ⟧ꟳ → Γ ⊢ atom A
  reify-⊥ : ∀ {Γ} → Γ ⊩ ⟦ ⊥ ⟧ꟳ → Γ ⊢ ⊥
  reify-∨ : ∀ {Γ} A B → Γ ⊩ ⟦ A ∨ B ⟧ꟳ → Γ ⊢ A ∨ B
  reflect : ∀ {Γ} A → Γ ⊢ A → Γ ⊩ ⟦ A ⟧ꟳ

  reify (atom A) a = reify-atom A a
  reify ⊤ tt = ⊤ᵢ
  reify (A ∧ B) (a ,, b) = ∧ᵢ (reify A a) (reify B b)
  reify (A ⇒ B) f = ⇒ᵢ (reify B (f p (reflect A q)))
  reify ⊥ r = reify-⊥ r
  reify (A ∨ B) r = reify-∨ A B r

  reify-atom A (maximal a) = a
  reify-atom A (◁-⊥ r) = ⊥ₑ r
  reify-atom A (◁-∨ f g r) = ∨ₑ (reify-atom A (f p q)) (reify-atom A (g p q)) r

  reify-⊥ (maximal ())
  reify-⊥ (◁-⊥ r) = r
  reify-⊥ (◁-∨ f g r) = ∨ₑ (reify-⊥ (f p q)) (reify-⊥ (g p q)) r

  reify-∨ A B (maximal (inl a)) = ∨ᵢ₁ (reify A a)
  reify-∨ A B (maximal (inr b)) = ∨ᵢ₂ (reify B b)
  reify-∨ A B (◁-⊥ r) = ⊥ₑ r
  reify-∨ A B (◁-∨ f g r) = ∨ₑ (reify-∨ A B (f p q)) (reify-∨ A B (g p q)) r

  reflect (atom A) a = maximal a
  reflect ⊤ r = tt
  reflect (A ∧ B) r = reflect A (∧ₑ₁ r) ,, reflect B (∧ₑ₂ r)
  reflect (A ⇒ B) r γ a = reflect B (⇒ₑ (r [ γ ]) (reify A a))
  reflect ⊥ r = ◁-⊥ r
  reflect (A ∨ B) r =
    ◁-∨
      (λ γ a → maximal (M.inl (reflect A a)))
      (λ γ b → maximal (M.inr (reflect B b)))
      r

  reflectꟲ : ∀ {Δ} Γ → Δ ⊢ˢ Γ → Δ ⊩ ⟦ Γ ⟧ꟲ
  reflectꟲ ◇ σ = tt
  reflectꟲ (Γ ▹ A) σ = reflectꟲ Γ (p ∘ σ) ,, reflect A (q [ σ ])

  complete : ∀ {Γ A} → ⟦ Γ ⟧ꟲ ⊨ ⟦ A ⟧ꟳ → Γ ⊢ A
  complete {Γ} {A} a = reify A (∣ a ∣ (reflectꟲ Γ id))
