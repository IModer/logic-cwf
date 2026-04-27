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

map^ : ∀{i}{A B : Set i}{n} -> A ^ n -> (A -> B) -> B ^ n
map^ {i}{A}{B}{zero} * f = *
map^ {i}{A}{B}{suc n} (t ,Σ ts) f = f t ,Σ map^ ts f


data _+p_ {i j}(A : Prop i)(B : Prop j) : Prop (i ⊔ j) where
  inj₁ : A → A +p B
  inj₂ : B → A +p B

ind+p : ∀{i j k}{A : Prop i}{B : Prop j}(C : A +p B → Prop k) →
  ((x : A) → C (inj₁ x)) → ((y : B) → C (inj₂ y)) → (w : A +p B) → C w
ind+p C u v (inj₁ x) = u x
ind+p C u v (inj₂ y) = v y

data _+_ {i j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inj₁ : A → A + B
  inj₂ : B → A + B

ind+ : ∀{i j k}{A : Set i}{B : Set j}(C : A + B → Set k) →
  ((x : A) → C (inj₁ x)) → ((y : B) → C (inj₂ y)) → (w : A + B) → C w
ind+ C u v (inj₁ x) = u x
ind+ C u v (inj₂ y) = v y

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

data _≡p_ {i}{A : Prop i}(x : A) : A → Prop i where
  refl : x ≡p x

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
  transport  : ∀ {i j} {A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y  
  transport-refl : ∀ {i j} {A : Set i}{P : A → Set j}{x : A}{px : P x} → transport P refl px ≡ px
  -- {-# REWRITE transport-refl #-}

  -- funext A A' B B'
  funext      : ∀{i j}{A : Set i }{B : A → Set j}{f g : (a : A) → B a} → (∀(x : A) → f x   ≡ g x) → f ≡ g
  funextp     : ∀{i j}{A : Prop i}{B : A → Set j}{f g : (a : A) → B a} → (∀(x : A) → f x   ≡ g x) → f ≡ g
  funext-imp  : ∀{i j}{A : Set i }{B : A → Set j}{f g : {a : A} → B a} → (∀{x} ->    f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  funextp-imp : ∀{i j}{A : Prop i}{B : A → Set j}{f g : {a : A} → B a} → (∀{x} ->    f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  
substp : ∀{i j}{A : Set i}(B : A → Prop j){a a' : A} → a ≡ a' → B a → B a'
substp B refl u = u

substP : ∀{i j}{A : Prop i}(B : A → Prop j){a a' : A} → B a → B a'
substP B u = u

sym : ∀{i}{A : Set i}{a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : ∀{i}{A : Set i}{a a' a'' : A} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong-bin : ∀{i j k}{A : Set i}{B : Set j}{C : Set k}(R : A -> B -> C){a a' : A}{b b' : B} -> a ≡ a' -> b ≡ b' -> R a b ≡ R a' b'
cong-bin R refl refl = refl

cong-bin-dep : ∀{i j k}{A : Set i}{B : A -> Prop j}{C : Set k}(R : (a : A) -> B a -> C){a a' : A}{b : B a}{b' : B a'} -> (p : a ≡ a') -> R a b ≡ R a' b'
cong-bin-dep R refl = refl

_∎ : ∀{ℓ}{A : Set ℓ}(x : A) → x ≡ x
x ∎ = refl {x = x}

_≡⟨_⟩_ : ∀{ℓ}{A : Set ℓ}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

infixl 5 the
the : ∀{ℓ}(A : Set ℓ) → A → A
the _ a = a
{-# INLINE the #-}

syntax the A a = a ∈ A

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