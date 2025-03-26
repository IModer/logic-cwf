{-# OPTIONS --prop #-}

module lib where

open import Agda.Primitive public

-- standard library

infixr 6 _,Σ_ _,∃_
infixl 5 _×_ _×p_
infixr 1 _+p_

data 𝟘 : Set where

ind𝟘 : ∀{i}{A : Set i} → 𝟘 → A
ind𝟘 ()

data 𝟘p : Prop where

ind𝟘p : ∀{i}{A : Prop i} → 𝟘p → A
ind𝟘p ()

record 𝟙p{i} : Prop i where
  constructor *

record Σp {i j}(A : Prop i)(B : A → Prop j) : Prop (i ⊔ j) where
  constructor _,Σ_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σp public
_×p_ : ∀{i j} → Prop i → Prop j → Prop (i ⊔ j)
A ×p B = Σp A λ _ → B

record 𝟙 {i} : Set i where
  constructor *

record Σ {i}{j}(A : Set i)(B : A → Set j) : Set (i ⊔ j) where
  --pattern
  --no-eta-equality
  constructor _,Σ_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public
_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B

record Σsp {i}{j}(A : Set i)(B : A → Prop j) : Set (i ⊔ j) where
  constructor _,Σ_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σsp public
_×sp_ : ∀{i j} → Set i → Prop j → Set (i ⊔ j)
A ×sp B = Σsp A λ _ → B

record propToSet(P : Prop) : Set where
  eta-equality
  constructor p⟦_⟧
  field
    c : P

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

iteℕ : ∀{i}{A : Set i} → A → (A → A) → ℕ → A
iteℕ z s zero = z
iteℕ z s (suc n) = s (iteℕ z s n)

indℕp : ∀{i}(A : ℕ → Prop i) → A zero → (∀ n → A n → A (suc n)) → (n : ℕ) → A n
indℕp A z s zero = z
indℕp A z s (suc n) = s n (indℕp A z s n)

indℕs : ∀{i}(A : ℕ → Set i) → A zero → (∀ n → A n → A (suc n)) → (n : ℕ) → A n
indℕs A z s zero = z
indℕs A z s (suc n) = s n (indℕs A z s n)

_^_ : ∀{i} → Set i → ℕ → Set i
T ^ zero = 𝟙
T ^ suc n = T × (T ^ n) -- iteℕ 𝟙 (_× T) n

ind^ : ∀{i}{n} → {T : Set i}{C : ℕ → Set i} → (𝟙 {i} → C zero) → (∀ n → T → C n → C (suc n)) → T ^ n → C n
ind^ {i} {zero} {T} {C} f g * = f *
ind^ {i} {suc n} {T} {C} f g (t ,Σ ts) = g n t (ind^ {i}{n}{T}{C} f g ts)

ind^' : ∀{i}{n} → {T : Set i}{C : ℕ → Set i} → C zero → (∀{m} → T → C m → C (suc m)) → T ^ n → C n
ind^' {i} {zero} {T} {C} f g * = f
ind^' {i} {suc n} {T} {C} f g (t ,Σ ts) = g t (ind^' {i}{n}{T}{C} f g ts)


data _+p_ {i j}(A : Prop i)(B : Prop j) : Prop (i ⊔ j) where
  inj₁ : A → A +p B
  inj₂ : B → A +p B

ind+p : ∀{i j k}{A : Prop i}{B : Prop j}(C : A +p B → Prop k) →
  ((x : A) → C (inj₁ x)) → ((y : B) → C (inj₂ y)) → (w : A +p B) → C w
ind+p C u v (inj₁ x) = u x
ind+p C u v (inj₂ y) = v y

data ∃ {i}{j}(A : Set i)(B : A → Prop j) : Prop (i ⊔ j) where
  _,∃_ : (a : A) → B a → ∃ A B

with∃ : ∀{i j k}{A : Set i}{B : A → Prop j}{C : Prop k} → ∃ A B → ((x : A) → B x → C) → C
with∃ (a ,∃ b) f = f a b

record ↑l {ℓ ℓ'}(A : Set ℓ) : Set (ℓ ⊔ ℓ') where
  constructor mk
  field
    un : A
open ↑l public

record ↑pl {ℓ ℓ'}(A : Prop ℓ) : Prop (ℓ ⊔ ℓ') where
  constructor mk
  field
    un : A
open ↑pl public

data Bool : Set where
  true false : Bool 

if_then_else_ : ∀{i}{A : Set i} → Bool → A → A → A
if true then a else b = a
if false then a else b = b


ifₚ_then_else_ : ∀{i}{A : Prop i} → Bool → A → A → A
ifₚ true then a else b = a
ifₚ false then a else b = b


indBool : ∀{i}{B : Bool → Set i} → B true → B false → ((b : Bool) → B b)
indBool x x₁ true = x
indBool x x₁ false = x₁

indBoolₚ : ∀{i}{B : Bool → Prop i} → B true → B false → ((b : Bool) → B b)
indBoolₚ x x₁ true = x
indBoolₚ x x₁ false = x₁

record LiftProp {a ℓ} (A : Prop a) : Prop (a ⊔ ℓ) where
  constructor liftprop
  field 
    lower : A

data _≡_ {i}{A : Set i}(x : A) : A → Prop i where
  refl : x ≡ x

-- {-# BUILTIN REWRITE _≡_ #-}

infix 4 _≡_
infix  3 _∎
infixr 2 _≡⟨_⟩_
infixr 2 _≡≡_
infix 3 _∎∎

data _≡s_ {i}{A : Set i} : A → A → Set i where
  _∎∎     : (x : A) → x ≡s x
  _≡≡_   : (x : A) → x ≡s x → x ≡s x

eqP : ∀ {i}{A : Set i}{x y : A} -> x ≡s y -> x ≡ y
eqP (x ≡≡ y) = refl
eqP (x ∎∎) = refl

postulate
  transport : ∀ {i j} {A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
  transport-refl : ∀ {i j} {A : Set i}{P : A → Set j}{x : A}{px : P x} → transport P refl px ≡ px
  -- {-# REWRITE transport-refl #-}

  funext : {A : Set}{B : A → Set}{f g : (a : A) → (B a)} → ((x : A) → f x ≡ g x) → f ≡ g

substp : ∀{i j}{A : Set i}(B : A → Prop j){a a' : A} → a ≡ a' → B a → B a'
substp B refl u = u

sym : ∀{i}{A : Set i}{a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : ∀{i}{A : Set i}{a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

_∎ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ x
x ∎ = refl {x = x}

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

mk,sp= : ∀{i}{j}{A : Set i}{B : A → Prop j}{a a' : A}{b : B a}{b' : B a'} → (a ≡ a') → _≡_ {A = Σsp A B} (a ,Σ b) (a' ,Σ b')
mk,sp= refl = refl

mk,= : ∀{i}{j}{A : Set i}{B : Set j}{a a' : A}{b b' : B} → (a ≡ a') → (b ≡ b') → _≡_ {A = A × B} (a ,Σ b) (a' ,Σ b')
mk,= refl refl = refl

data Squash {ℓ} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

squash-elim : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (P : Prop ℓ₂) → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x


module Extra where

  record Preord{i j} : Set (lsuc (i ⊔ j)) where
    field
      C : Set i
      _≥_  : C → C → Prop j
      id≥  : {c : C} → c ≥ c
      _∘≥_ : {a c b : C} → b ≥ c → a ≥ b → a ≥ c
  --open Preord

  record Psh{i j k}(P : Preord {i}{j}) : Set (lsuc (i ⊔ j ⊔ k)) where
    open Preord P
    
    field
      Γ     : C → Set k
      _⟨_⟩   : {J I : C} → Γ I → J ≥ I → Γ J
      ⟨∘≥⟩   : {K J I : C}{γ : Γ I}{f : J ≥ I}{g : K ≥ J} → γ ⟨ f ∘≥ g ⟩ ≡ (γ ⟨ f ⟩) ⟨ g ⟩
      ⟨id≥⟩  : {I : C}{γ : Γ I} → γ ⟨ id≥ ⟩ ≡ γ

  --record DepPshProp{i j k}(P : Preord {i}{j})(Ps : Psh {i}{j}{k} P) : Set (lsuc (i ⊔ j ⊔ k)) where
  --  open Preord P
  --  open Psh Ps
  --
  --  field
  --    A     : (I : C) → Γ I → Prop k
  --    _⟨_⟩   : {! A I γ  !} -- {J I : C} → A Γ I → J ≥ I → Γ J

  record NatTrans
    {i j k}
    (P : Preord {i}{j})
    (PshΔ : Psh {i}{j}{k} P)
    (PshΓ : Psh {i}{j}{k} P) : Set (lsuc (i ⊔ j ⊔ k)) where
    
    open Preord P
    open Psh PshΔ renaming (Γ to Δ; _⟨_⟩ to _⟨_⟩Δ)
    open Psh PshΓ renaming (_⟨_⟩ to _⟨_⟩Γ)

    field
      γ : {I : C} → Δ I → Γ I
      comm : {I J : C}{δ : Δ I}{f : J ≥ I} → (γ δ) ⟨ f ⟩Γ ≡ γ (δ ⟨ f ⟩Δ)