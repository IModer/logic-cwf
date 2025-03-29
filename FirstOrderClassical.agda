{-# OPTIONS --prop --allow-unsolved-metas #-}

open import lib

module FirstOrderClassical
  (funar : ℕ → Set)
  (relar : ℕ → Set) 
  where

record Model (i j k l m : Level) : Set (lsuc (i ⊔ j ⊔ k ⊔ l ⊔ m)) where
  infixl 5 _▸t _▸p_
  infixl 5 _,t_ _,p_
  infixr 7 _∘_
  infixl 8 _[_]t _[_]ts _[_]F _[_]p
  infixr 6 _⊃_
  field
    -- We translate the Second order example into a first order GAT
    -- The main idea of the traslation is to encode the variables
    -- that we got from the second order operators for free

    -- These variables will be handles via a Cartesian Closed Category
    -- The objects are Contexts which will story our variables, and arrows are morphisms between context
    -- these are substitutions
    -- Cartesian Closed Category
    Con   : Set i                                           -- Objects
    Sub   : Con → Con → Set j                               -- Morphisms/Arrows
    _∘_   : ∀{Γ Δ Θ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ          -- Composition arrows
    id    : ∀{Γ} → Sub Γ Γ                                  -- Identity arrows
    -- Equations
    ass   : ∀{Γ Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ}{Ξ}{θ : Sub Ξ Θ} → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
    idl   : ∀{Γ Δ}{γ : Sub Δ Γ} → id ∘ γ ≡ γ
    idr   : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ∘ id ≡ γ
    -- Our category comes with a terminal object
    ◆     : Con
    ε     : ∀{Γ} → Sub Γ ◆
    -- Universal property
    ◆η    : ∀{Γ}(σ : Sub Γ ◆) → σ ≡ ε

    -- We then translate each of our sort into a functor from the 
    -- opposite of the base category (category of contexts (Conᵒᵖ)) to the category of Sets
    -- This is also called the presheaf over the base category (PrShf(Con))
    -- For : Set
    -- The functors action on Objects (Con)
    For   : Con → Set k
    -- The functors action on Arrows (Sub Δ Γ)
    _[_]F : ∀{Γ Δ} → For Γ → Sub Δ Γ → For Δ   -- Sub Δ Γ → (For Γ → For Δ) == Γ ⇒ Δ → (For Γ )
    -- because For is a Functor it must preserve the equations
    [∘]F  : ∀{Γ}{K : For Γ}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} → K [ γ ∘ δ ]F ≡ K [ γ ]F [ δ ]F
    [id]F : ∀{Γ}{K : For Γ} → K [ id ]F ≡ K

    -- For Pf, we have additional operations _▸p_ (context extention) 
    -- Pf : For → Prop
    Pf    : (Γ : Con) → For Γ → Prop l -- mivel Propba megy ezért nem kellenek a funktor 
    _[_]p : ∀{Γ K} → Pf Γ K → ∀{Δ} → (γ : Sub Δ Γ) → Pf Δ (K [ γ ]F)
    -- this functor is locally representable
    _▸p_  : (Γ : Con) → For Γ → Con
    _,p_  : ∀{Γ Δ} → (γ : Sub Δ Γ) → ∀{K} → Pf Δ (K [ γ ]F) → Sub Δ (Γ ▸p K)
    pp    : ∀{Γ K} → Sub (Γ ▸p K) Γ
    qp    : ∀{Γ K} → Pf  (Γ ▸p K) (K [ pp ]F)
    ▸pβ₁  : ∀{Γ Δ}{γ : Sub Δ Γ}{K}{k : Pf Δ (K [ γ ]F)} → pp ∘ (γ ,p k) ≡ γ
    -- β₂ nem kell mert Pf propba van
    -- kell η
    ▸pη   : ∀{Γ Δ K}{γp : Sub Δ (Γ ▸p K)}  → (pp ∘ γp) ,p substp (λ K → Pf Δ K) (sym [∘]F) (qp [ γp ]p) ≡ γp
    -- The second half has to be transported because
    -- qp [ γp ]p : Pf Δ (K [ pp ]F [ γp ]F)
    -- but we need ? : Pf Δ (K [ pp ∘ γp ]F)

    -- propositional connectives (they don't depend on the term context)

    -- Then for every operation on For and Pf we can just add them and say how they behave over _[_]
    -- ⊥ : For, exfalso : Pf ⊥ → Pf K
    ⊥    : ∀{Γ} → For Γ
    ⊥[]  : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊥ [ γ ]F ≡ ⊥
    exfalso : ∀{Γ K} → Pf Γ ⊥ → Pf Γ K

    -- ⊤ : For, tt : Pf ⊤
    ⊤    : ∀{Γ} → For Γ
    ⊤[]  : ∀{Γ Δ}{γ : Sub Δ Γ} → ⊤ [ γ ]F ≡ ⊤
    tt   : ∀{Γ} → Pf Γ ⊤

    -- ⊃ : For → For → For, (Pf K → Pf L) ↔ Pf (K ⊃ L)
    _⊃_  : ∀{Γ} → For Γ → For Γ → For Γ
    ⊃[]  : ∀{Γ K L Δ}{γ : Sub Δ Γ} → (K ⊃ L) [ γ ]F ≡ K [ γ ]F ⊃ L [ γ ]F
    ⊃intro  : ∀{Γ K L} → Pf (Γ ▸p K) (L [ pp ]F) → Pf Γ (K ⊃ L)
    ⊃elim  : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf (Γ ▸p K) (L [ pp ]F) -- Pf Γ (K ⊃ L) → Pf Γ K → Pf Γ L -- Pf (Γ ▸p K) (L [ pp ]F)

    _∧_  : ∀{Γ} → For Γ → For Γ → For Γ
    ∧[]  : ∀{Γ K L Δ}{γ : Sub Δ Γ} → (K ∧ L) [ γ ]F ≡ (K [ γ ]F) ∧ (L [ γ ]F)
    ∧intro : ∀{Γ}{K L} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
    ∧elim₁ : ∀{Γ}{K L} → Pf Γ (K ∧ L) → Pf Γ K
    ∧elim₂ : ∀{Γ}{K L} → Pf Γ (K ∧ L) → Pf Γ L

    _∨_  : ∀{Γ} → For Γ → For Γ → For Γ
    ∨[]  : ∀{Γ K L Δ}{γ : Sub Δ Γ} → (K ∨ L) [ γ ]F ≡ (K [ γ ]F) ∨ (L [ γ ]F)
    ∨elim : ∀{Γ}{K L C} → Pf (Γ ▸p K) (C [ pp ]F) → Pf (Γ ▸p L) (C [ pp ]F) → Pf Γ (K ∨ L) → Pf Γ C
    ∨intro₁ : ∀{Γ}{K L} → Pf Γ K → Pf Γ (K ∨ L)
    ∨intro₂ : ∀{Γ}{K L} → Pf Γ L → Pf Γ (K ∨ L)

    -- terms (Tm : Set)
    Tm    : Con → Set j
    _[_]t : ∀{Γ} → Tm Γ → ∀{Δ} → Sub Δ Γ → Tm Δ
    [∘]t  : ∀{Γ}{t : Tm Γ}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} → t [ γ ∘ δ ]t ≡ t [ γ ]t [ δ ]t
    [id]t : ∀{Γ}{t : Tm Γ} → t [ id ]t ≡ t
    _▸t   : Con → Con
    _,t_  : ∀{Γ Δ} → Sub Δ Γ → Tm Δ → Sub Δ (Γ ▸t)
    pt    : ∀{Γ} → Sub (Γ ▸t) Γ
    qt    : ∀{Γ} → Tm (Γ ▸t)
    ▸tβ₁  : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm Δ} → (pt ∘ (γ ,t t)) ≡ γ
    ▸tβ₂  : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm Δ} → (qt [ γ ,t t ]t) ≡ t
    ▸tη   : ∀{Γ Δ}{γt : Sub Δ (Γ ▸t)} → ((pt ∘ γt) ,t (qt [ γt ]t)) ≡ γt
    
    -- Telescopes of terms
    -- They are basically isomorphic to Vectors of Tm-s
    -- Why do we nned them? Its more principled to build these into the theory rather then relaying on out metatheorys Vectors
    -- We only rely on natural numbers from our metatheory
    -- It is also a contravariant functor from Con
    Tms : Con → ℕ → Set m
    -- Action on morphisms
    _[_]ts : ∀{Γ n} → Tms Γ n → ∀{Δ} → Sub Δ Γ → Tms Δ n
    -- Functor laws
    [∘]ts  : ∀{Γ n}{ts : Tms Γ n}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} → ts [ γ ∘ δ ]ts ≡ ts [ γ ]ts [ δ ]ts
    [id]ts : ∀{Γ n}{ts : Tms Γ n} → ts [ id ]ts ≡ ts
    εs     : ∀{Γ} → Tms Γ zero
    ◆sη    : ∀{Γ}(ts : Tms Γ zero) → ts ≡ εs
    _,s_   : ∀{Γ n} → Tms Γ n → Tm Γ → Tms Γ (suc n)
    π₁     : ∀{Γ n} → Tms Γ (suc n) → Tms Γ n
    π₂     : ∀{Γ n} → Tms Γ (suc n) → Tm Γ
    ▸sβ₁   : ∀{Γ n}{ts : Tms Γ n}{t : Tm Γ} → π₁ (ts ,s t) ≡ ts
    ▸sβ₂   : ∀{Γ n}{ts : Tms Γ n}{t : Tm Γ} → π₂ (ts ,s t) ≡ t
    ▸sη    : ∀{Γ n}{ts : Tms Γ (suc n)} → π₁ ts ,s π₂ ts ≡ ts
    ,[]    : ∀{Γ n}{ts : Tms Γ n}{t : Tm Γ}{Δ}{γ : Sub Δ Γ} → (ts ,s t) [ γ ]ts ≡ (ts [ γ ]ts) ,s (t [ γ ]t)

    fun  : ∀{Γ}(n : ℕ) → funar n → Tms Γ n → Tm Γ
    fun[] : ∀{Γ n a ts Δ}{γ : Sub Δ Γ} → (fun n a ts [ γ ]t) ≡ fun n a (ts [ γ ]ts)
    rel  : ∀{Γ}(n : ℕ) → relar n → Tms Γ n → For Γ
    rel[] : ∀{Γ n a ts Δ}{γ : Sub Δ Γ} → ((rel n a ts) [ γ ]F) ≡ rel n a (ts [ γ ]ts)


    -- first order connectives

    -- ∀ : (Tm → For) → For, ((t : Tm) → Pf (K t)) ↔ Pf (∀ K)
    ∀'     : ∀{Γ} → For (Γ ▸t) → For Γ
    ∀[]    : ∀{Γ K Δ}{γ : Sub Δ Γ} → (∀' K) [ γ ]F ≡ ∀' (K [ (γ ∘ pt) ,t qt ]F)
    ∀intro : ∀{Γ K} → Pf (Γ ▸t) K → Pf Γ (∀' K)
    ∀elim  : ∀{Γ K} → Pf Γ (∀' K) → Pf (Γ ▸t) K

    ∃'      : ∀{Γ} → For (Γ ▸t) → For Γ
    ∃[]    : ∀{Γ K Δ}{γ : Sub Δ Γ} → (∃' K) [ γ ]F ≡ ∃' (K [ (γ ∘ pt) ,t qt ]F)
    ∃intro : ∀{Γ K} → (t : Tm Γ) → Pf Γ (K [ id ,t t ]F) → Pf Γ (∃' K)
    --∃intro : ∀{Γ K} → (∃ (Tm Γ) (λ t → Pf Γ (K [ id ,t t ]F))) → Pf Γ (∃' K)
    ∃elim  : ∀{Γ K L} → Pf Γ (∃' K) → Pf ((Γ ▸t) ▸p K) (L [ pt ∘ pp ]F) → Pf Γ L


    -- Eq : Tm → Tm → For, ref : (t : Tm) → Eq t t, subst : (K : Tm → For) → Pf (Eq t t') → Pf (K t) → Pf (K t')
    Eq    : ∀{Γ} → Tm Γ → Tm Γ → For Γ
    Eq[]  : ∀{Γ Δ}{γ : Sub Δ Γ}{t t' : Tm Γ} → (Eq t t') [ γ ]F ≡ Eq (t [ γ ]t) (t' [ γ ]t)
    Eqrefl   : ∀{Γ}{t : Tm Γ} → Pf Γ (Eq t t)
    subst' : ∀{Γ}(K : For (Γ ▸t)){t t' : Tm Γ} → Pf Γ (Eq t t') → Pf Γ (K [ id ,t t ]F) → Pf Γ (K [ id ,t t' ]F)

    dne : ∀{Γ A} → Pf Γ (((A ⊃ ⊥) ⊃ ⊥) ⊃ A)

  ,∘ : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm Δ}{Θ}{δ : Sub Θ Δ} → (γ ,t t) ∘ δ ≡ γ ∘ δ ,t t [ δ ]t
  ,∘ {Γ}{Δ}{γ}{t}{Θ}{δ} = trans (sym ▸tη) (cong (λ z → proj₁ z ,t proj₂ z) (mk,= (trans (sym ass) (cong (_∘ δ) ▸tβ₁)) (trans [∘]t (cong (_[ δ ]t) ▸tβ₂))))
  
  ▸tη' : ∀{Γ} → id {Γ ▸t} ≡ pt ,t qt
  ▸tη' {Γ} = trans (sym ▸tη) (cong (λ z → proj₁ z ,t proj₂ z) (mk,= idr [id]t))

  _$_ : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf Γ K → Pf Γ L
  _$_ {Γ}{K}{L} m k = substp (Pf Γ) (trans (sym [∘]F) (trans (cong (L [_]F) ▸pβ₁) [id]F)) (⊃elim m [ id ,p substp (Pf Γ) (sym [id]F) k ]p)

  un∀' : ∀{Γ K} → Pf Γ (∀' K) → (t : Tm Γ) → Pf Γ (K [ id ,t t ]F)
  un∀' {Γ}{K} k t = (∀elim k) [ id ,t t ]p

  pp⁺ : ∀{Γ Δ}{K} → (γ : Sub Γ Δ) → Sub (Γ ▸p K [ γ ]F) (Δ ▸p K)
  pp⁺ {Γ}{Δ}{K} γ = (γ ∘ pp) ,p substp (Pf (Γ ▸p K [ γ ]F)) (sym [∘]F) qp

  pt⁺ : ∀{Γ Δ} → (γ : Sub Γ Δ) → Sub (Γ ▸t) (Δ ▸t)
  pt⁺ γ = (γ ∘ pt) ,t qt

-- We give the initial model of FOLClassicMinimal
-- We give it as a normal form, meaning its a inductive
-- datatype but we can prove it satisfies the equations
module I where

  infixl 5 _▸t _▸p_
  infixl 5 _,t_ _,p_
  infixr 7 _∘_ _∘p_
  infixl 8 _[_]t _[_]F _[_]C _[_]P _[_]p _[_]v _[_]s _[_]ts
  infixr 6 _⊃_
  infixr 7 _∧_
  infixl 6 _$_

  -- We give the context in two different parts, a context of Tm-s and a context of Pf variable
  -- Then out context will be Con = Σ ConTm ConPf
  -- Along the way we prove all the ass,id, and β,η laws


  -- Contexts for terms
  -- ConTm ≅ ℕ
  data ConTm : Set where
    ◆t : ConTm
    _▸t : ConTm → ConTm

  module V where
    
    --De Bruijn indicies
    data Tm : ConTm → Set where
      vz : ∀{Γ} → Tm (Γ ▸t)
      vs : ∀{Γ} → Tm Γ → Tm (Γ ▸t)

    -- Renaming
    data Sub : ConTm → ConTm → Set where
      εt : ∀{Δt} → Sub Δt ◆t
      _,t_ : ∀{Γt Δt} → Sub Δt Γt → Tm Δt → Sub Δt (Γt ▸t)

    mk,t= : ∀{Γ Δ t t'}{γ γ' : Sub Δ Γ} → γ ≡ γ' → t ≡ t' →  γ ,t t ≡ γ' ,t t'
    mk,t= refl refl = refl

    -- Substitution on terms (Action on morphisms)
    _[_] : ∀{Γ} → Tm Γ → ∀{Δ} → Sub Δ Γ → Tm Δ
    vz [ γ ,t t ] = t
    vs t [ γ ,t _ ] = t [ γ ]

    _∘_ : ∀{Γ Δ} → Sub Δ Γ → ∀{Θ} → Sub Θ Δ → Sub Θ Γ
    εt ∘ γ = εt
    (γ ,t t) ∘ δ = (γ ∘ δ) ,t (t [ δ ])

    [∘] : ∀{Γ}{t : Tm Γ}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} → t [ γ ∘ δ ] ≡ t [ γ ] [ δ ]
    [∘] {t = vz} {γ = γ ,t x} = refl
    [∘] {t = vs t} {γ = γ ,t x} = [∘] {t = t}

    -- Pattern match on Subs
    ass : ∀{Γ Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ}{Ξ}{θ : Sub Ξ Θ} → (γ ∘ δ) ∘ θ ≡ γ ∘ (δ ∘ θ)
    ass {γ = εt} = refl
    ass {γ = γ ,t x} = mk,t= ass (sym ([∘] {t = x}))

    wk : ∀{Γ Δ} → Sub Δ Γ → Sub (Δ ▸t) Γ
    wk εt = εt
    wk (γ ,t t) = wk γ ,t vs t

    id : ∀{Γ} → Sub Γ Γ
    id {◆t} = εt
    id {Γ ▸t} = (wk id) ,t vz

    wk∘ : ∀{Γ Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ}{t : Tm Θ} → (wk γ ∘ (δ ,t t)) ≡ γ ∘ δ
    wk∘ {γ = εt} = refl
    wk∘ {γ = γ ,t x} {δ = δ} = cong (_,t (x [ δ ])) wk∘

    idl : ∀{Γ Δ}{γ : Sub Δ Γ} → id ∘ γ ≡ γ
    idl {γ = εt} = refl
    idl {γ = γ ,t x} = cong (_,t x) (trans wk∘ idl)

    vs[] : ∀{Γ}{t : Tm Γ}{Δ}{γ : Sub Δ Γ} → t [ wk γ ] ≡ vs (t [ γ ])
    vs[] {t = vz} {γ = γ ,t t} = refl
    vs[] {t = vs t}  {γ = γ ,t t'} = vs[] {t = t}
  
    [id] : ∀{Γ}{t : Tm Γ} → t [ id ] ≡ t
    [id] {t = vz} = refl
    [id] {t = vs t} = trans (vs[] {t = t}) (cong vs ([id] {t = t}))

    idr : ∀{Γ Δ}{γ : Sub Δ Γ} → γ ∘ id ≡ γ
    idr {γ = εt} = refl
    idr {γ = γ ,t x} = mk,t= idr [id]

  open V using (vz; vs)

  -- Because we use Tms in our notion of model we have to define Tms and Tm mutually inductively
  -- This is one of the "negatives" of using Tms but this is also the case for substitutions in Tm and Tm ^ n
  data Tm (Γt : ConTm) : Set
  Tms : ConTm → ℕ → Set

  data Tm Γt where
    var  : V.Tm Γt → Tm Γt
    fun  : (n : ℕ) → funar n → Tms Γt n → Tm Γt
  Tms Γt zero = 𝟙
  Tms Γt (suc n) = Tms Γt n × Tm Γt

  --data Tm (Γt : ConTm) : Set where
  --  var  : V.Tm Γt → Tm Γt
  --  fun  : (n : ℕ) → funar n → Tm Γt ^ n → Tm Γt

  data Subt : ConTm → ConTm → Set where
    εt : ∀{Δt} → Subt Δt ◆t
    _,t_ : ∀{Γt Δt} → Subt Δt Γt → Tm Δt → Subt Δt (Γt ▸t)

  mk,t= : ∀{Γ Δ t t'}{γ γ' : Subt Δ Γ} → γ ≡ γ' → t ≡ t' →  γ ,t t ≡ γ' ,t t'
  mk,t= refl refl = refl

  -- Substitution on variables
  _[_]v : ∀{Γt Δt} → V.Tm Γt → Subt Δt Γt → Tm Δt
  vz [ γ ,t t ]v = t
  vs x [ γ ,t t ]v = x [ γ ]v

  -- Substitution on terms and Tm ^ n
  --_[_]ts : ∀{Γt n} → Tm Γt ^ n → ∀{Δt} → Subt Δt Γt → Tm Δt ^ n
  --_[_]t  : ∀{Γt} → Tm Γt → ∀{Δt} → Subt Δt Γt → Tm Δt
  --_[_]ts {n = zero} _ _ = *
  --_[_]ts {n = suc n} (t ,Σ ts) γ = (t [ γ ]t) ,Σ (ts [ γ ]ts)
  --var x [ γ ]t = x [ γ ]v
  --(fun n a ts) [ γ ]t  = fun n a (ts [ γ ]ts)

  -- Substitution on terms
  _[_]t  : ∀{Γt} → Tm Γt → ∀{Δt} → Subt Δt Γt → Tm Δt
  _[_]ts : ∀{Γt n} → Tms Γt n → ∀{Δt} → Subt Δt Γt → Tms Δt n
  var x [ γ ]t = x [ γ ]v
  fun n a ts [ γ ]t = fun n a (ts [ γ ]ts)
  _[_]ts {n = zero}  _         _ = *
  _[_]ts {n = suc n} (ts ,Σ t) γ = ts [ γ ]ts ,Σ t [ γ ]t

  _∘t_ : ∀{Γt Δt} → Subt Δt Γt → ∀{Θt} → Subt Θt Δt → Subt Θt Γt
  εt ∘t _ = εt
  (γ ,t t) ∘t δ = (γ ∘t δ) ,t (t [ δ ]t)

  [∘]v : ∀{Γt}{x : V.Tm Γt}{Δt}{γ : Subt Δt Γt}{Θt}{δ : Subt Θt Δt} → x [ γ ∘t δ ]v ≡ x [ γ ]v [ δ ]t
  [∘]v {x = vz} {γ = γ ,t x} = refl
  [∘]v {x = vs x} {γ = γ ,t t} = [∘]v {x = x}

  [∘]t : ∀{Γt}{t : Tm Γt}{Δt}{γ : Subt Δt Γt}{Θt}{δ : Subt Θt Δt} → t [ γ ∘t δ ]t ≡ t [ γ ]t [ δ ]t
  [∘]ts : ∀{Γt n}{ts : Tms Γt n}{Δt}{γ : Subt Δt Γt}{Θt}{δ : Subt Θt Δt} → ts [ γ ∘t δ ]ts ≡ ts [ γ ]ts [ δ ]ts

  [∘]t {Γt} {var x} {Δt} {γ} {Θt} {δ} = [∘]v {x = x}
  [∘]t {Γt} {fun n a ts} {Δt} {γ} {Θt} {δ} = cong (fun n a) [∘]ts
  [∘]ts {Γt} {zero} {ts} {Δt} {γ} {Θt} {δ} = refl
  [∘]ts {Γt} {suc n} {ts = t ,Σ ts} {Δt} {γ} {Θt} {δ} = mk,= ([∘]ts {ts = t}) ([∘]t {t = ts})

  ass : ∀{Γt Δt}{γ : Subt Δt Γt}{Θt}{δ : Subt Θt Δt}{Ξt}{θ : Subt Ξt Θt} → (γ ∘t δ) ∘t θ ≡ γ ∘t (δ ∘t θ)
  ass {γ = εt} = refl
  ass {γ = γ ,t x} = mk,t= ass (sym ([∘]t {t = x}))

  ⌜_⌝ : ∀{Γt Δt} → V.Sub Δt Γt → Subt Δt Γt
  ⌜ V.εt ⌝ = εt
  ⌜ γ V.,t t ⌝ = ⌜ γ ⌝ ,t (var t)

  idt : ∀{Γt} → Subt Γt Γt
  idt = ⌜ V.id ⌝

  ⌜wk⌝∘ : ∀{Γt Δt}{γv : V.Sub Δt Γt}{Θt}{δ : Subt Θt Δt}{t : Tm Θt} → ⌜ V.wk γv ⌝ ∘t (δ ,t t) ≡ ⌜ γv ⌝ ∘t δ
  ⌜wk⌝∘ {γv = V.εt} = refl
  ⌜wk⌝∘ {γv = γv V.,t x} {δ = δ} = cong (_,t (x [ δ ]v)) ⌜wk⌝∘

  idl : ∀{Γt Δt}{γ : Subt Δt Γt} → idt ∘t γ ≡ γ
  idl {γ = εt} = refl
  idl {γ = γ ,t t} = cong (_,t t) (trans ⌜wk⌝∘ idl)

  [⌜⌝] : ∀{Γt}{x : V.Tm Γt}{Δt}{γv : V.Sub Δt Γt} → x [ ⌜ γv ⌝ ]v ≡ var (x V.[ γv ])
  [⌜⌝] {x = vz} {γv = γv V.,t t} = refl
  [⌜⌝] {x = vs x} {γv = γv V.,t t} = [⌜⌝] {x = x}

  [id]v : ∀{Γt}{x : V.Tm Γt} → x [ idt ]v ≡ var x
  [id]v {x = vz} = refl
  [id]v {x = vs x} = trans ((trans ([⌜⌝] {x = x}) (cong var (V.vs[] {t = x}{γ = V.id})))) (cong (λ z → var (vs z)) V.[id])

  [id]t  : ∀{Γt}{t : Tm Γt} → t [ idt ]t ≡ t
  [id]ts : ∀{Γt n}{ts : Tms Γt n} → (ts [ idt ]ts) ≡ ts

  [id]t {t = var x} = [id]v
  [id]t {t = fun n a ts} = cong (fun n a) ([id]ts {ts = ts})
  [id]ts {n = zero}                = refl
  [id]ts {n = suc n}{ts = t ,Σ ts} = mk,= [id]ts [id]t

  idr : ∀{Γt Δt}{γ : Subt Δt Γt} → γ ∘t idt ≡ γ
  idr {γ = εt} = refl
  idr {γ = γ ,t t} = mk,t= idr [id]t

  pt : ∀{Γt} → Subt (Γt ▸t) Γt
  pt {Γt} = ⌜ V.wk V.id ⌝

  qt : ∀{Γt} → Tm (Γt ▸t)
  qt = var V.vz

  ▸tβ₁ : ∀{Γt Δt}{γ : Subt Δt Γt}{t : Tm Δt} → (pt ∘t (γ ,t t)) ≡ γ
  ▸tβ₁ = trans ⌜wk⌝∘ idl

  ▸tβ₂ : ∀{Γ Δ}{γ : Subt Δ Γ}{t : Tm Δ} → (qt [ γ ,t t ]t) ≡ t
  ▸tβ₂ = refl

  ▸tη : ∀{Γt Δt}{γt : Subt Δt (Γt ▸t)} → ((pt ∘t γt) ,t (qt [ γt ]t)) ≡ γt
  ▸tη {γt = γ ,t t} = cong (_,t t) (trans (⌜wk⌝∘ {γv = V.id}) idl)

  -- Formulas

  data For (Γt : ConTm) : Set where
    ⊥    : For Γt
    ⊤    : For Γt
    _⊃_  : For Γt → For Γt → For Γt
    _∧_  : For Γt → For Γt → For Γt
    _∨_  : For Γt → For Γt → For Γt
    ∀'   : For (Γt ▸t) → For Γt
    ∃'   : For (Γt ▸t) → For Γt
    Eq   : Tm Γt → Tm Γt → For Γt
    rel  : (n : ℕ) → relar n → Tms Γt n → For Γt

  ¬_ : ∀{Γt} → For Γt → For Γt
  ¬ A = A ⊃ ⊥

  _[_]F : ∀{Γt Δt} → For Γt → Subt Δt Γt → For Δt
  ⊥ [ γ ]F = ⊥
  ⊤ [ γ ]F = ⊤
  (K ⊃ L) [ γ ]F = K [ γ ]F ⊃ L [ γ ]F
  (K ∧ L) [ γ ]F = K [ γ ]F ∧ L [ γ ]F
  (K ∨ L) [ γ ]F = (K [ γ ]F) ∨ (L [ γ ]F)
  (∃' K) [ γ ]F = ∃' (K [ (γ ∘t pt) ,t qt ]F)
  ∀' K [ γ ]F = ∀' (K [ γ ∘t pt ,t qt ]F)
  Eq t t' [ γ ]F = Eq (t [ γ ]t) (t' [ γ ]t)
  rel n a ts [ γ ]F = rel n a (ts [ γ ]ts)

  [∘]F : ∀{Γt}{K : For Γt}{Δt}{γ : Subt Δt Γt}{Θt}{δ : Subt Θt Δt} → K [ γ ∘t δ ]F ≡ K [ γ ]F [ δ ]F
  [∘]F {K = ⊥} = refl
  [∘]F {K = ⊤} = refl
  [∘]F {K = K ⊃ L} = cong (λ z → proj₁ z ⊃ proj₂ z) (mk,= [∘]F [∘]F)
  [∘]F {K = K ∧ L} = cong (λ z → proj₁ z ∧ proj₂ z) (mk,= [∘]F [∘]F)
  [∘]F {K = K ∨ L} = cong (λ z → proj₁ z ∨ proj₂ z) (mk,= [∘]F [∘]F)
  [∘]F {K = ∀' K}{γ = γ}{δ = δ} = cong ∀' (trans (cong (K [_]F) (cong (_,t var vz) (trans (trans ass (cong (γ ∘t_) (sym (▸tβ₁ {γ = δ ∘t pt})))) (sym ass)))) [∘]F)
  [∘]F {K = ∃' K}{γ = γ}{δ = δ} = cong ∃' (trans (cong (K [_]F) (cong (_,t var vz) (trans (trans ass (cong (γ ∘t_) (sym (▸tβ₁ {γ = δ ∘t pt})))) (sym ass)))) [∘]F)
  [∘]F {K = Eq t t'} = cong (λ z → Eq (proj₁ z) (proj₂ z)) (mk,= ([∘]t {t = t}) ([∘]t {t = t'}))
  [∘]F {K = rel n a ts} = cong (rel n a) ([∘]ts {ts = ts})

  [id]F : ∀{Γt}{K : For Γt} → K [ idt ]F ≡ K
  [id]F {K = ⊥} = refl
  [id]F {K = ⊤} = refl
  [id]F {K = K ⊃ L} = cong (λ z → proj₁ z ⊃ proj₂ z) (mk,= ([id]F {K = K}) ([id]F {K = L}))
  [id]F {K = K ∧ L} = cong (λ z → proj₁ z ∧ proj₂ z) (mk,= ([id]F {K = K}) ([id]F {K = L}))
  [id]F {K = K ∨ L} = cong (λ z → proj₁ z ∨ proj₂ z) (mk,= ([id]F {K = K}) ([id]F {K = L}))
  [id]F {K = ∀' K} = cong ∀' (trans (cong (K [_]F) (cong (_,t var vz) idl)) ([id]F {K = K}))
  [id]F {K = ∃' K} = cong ∃' (trans (cong (K [_]F) (cong (_,t var vz) idl)) ([id]F {K = K}))
  [id]F {K = Eq t t'} = cong (λ z → Eq (proj₁ z) (proj₂ z)) (mk,= ([id]t {t = t}) ([id]t {t = t'}))
  [id]F {K = rel n a ts} = cong (rel n a) ([id]ts {ts = ts})

  data ConPf (Γt : ConTm) : Set where
    ◆p   : ConPf Γt
    _▸p_ : ConPf Γt → For Γt → ConPf Γt
  
  _[_]C : ∀{Γt} → ConPf Γt → ∀{Δt} → Subt Δt Γt → ConPf Δt
  ◆p [ γ ]C = ◆p
  (Γp ▸p K) [ γ ]C = Γp [ γ ]C ▸p K [ γ ]F

  [∘]C  : ∀{Γt}{Γp : ConPf Γt}{Δt}{γ : Subt Δt Γt}{Θt}{δ : Subt Θt Δt} → Γp [ γ ∘t δ ]C ≡ Γp [ γ ]C [ δ ]C
  [∘]C {Γp = ◆p}      = refl
  [∘]C {Γp = Γp ▸p K} = cong (λ z → proj₁ z ▸p proj₂ z) (mk,= ([∘]C {Γp = Γp}) ([∘]F {K = K}))

  [id]C : ∀{Γt}{Γp : ConPf Γt} → Γp [ idt ]C ≡ Γp
  [id]C {Γp = ◆p}      = refl
  [id]C {Γp = Γp ▸p K} = cong (λ z → proj₁ z ▸p proj₂ z) (mk,= ([id]C {Γp = Γp}) ([id]F {K = K}))

  data Pf : {Γt : ConTm} → ConPf Γt → For Γt → Prop

  data Subp : {Γt : ConTm} → ConPf Γt → ConPf Γt → Prop where
    εp  : ∀{Γt}{Γp : ConPf Γt} → Subp Γp ◆p
    idp : ∀{Γt}{Γp : ConPf Γt} → Subp Γp Γp
    _∘p_ : ∀{Γt}{Γp Γp' Γp'' : ConPf Γt} → Subp Γp' Γp → Subp Γp'' Γp' → Subp Γp'' Γp
    pp :  ∀{Γt}{Γp : ConPf Γt}{K} → Subp (Γp ▸p K) Γp
    _,p_ : ∀{Γt}{Γp Γp' : ConPf Γt}{K} → Subp Γp' Γp → Pf Γp' K → Subp Γp' (Γp ▸p K)
    _[_]s : ∀{Γt}{Δt}{Γp Γp' : ConPf Γt} → Subp Γp' Γp → (γ : Subt Δt Γt) → Subp (Γp' [ γ ]C) (Γp [ γ ]C)

  data Pf where
    exfalso : ∀{Γt}{Γp : ConPf Γt}{K} → Pf Γp ⊥ → Pf Γp K
    tt   : ∀{Γt}{Γp : ConPf Γt} → Pf Γp ⊤
    ⊃intro  : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf (Γp ▸p K) L → Pf Γp (K ⊃ L)
    _$_  : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf Γp (K ⊃ L) → Pf Γp K → Pf Γp L
    ∧intro : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf Γp K → Pf Γp L → Pf Γp (K ∧ L)
    ∧elim₁  : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf Γp (K ∧ L) → Pf Γp K
    ∧elim₂  : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf Γp (K ∧ L) → Pf Γp L

    ∨elim : ∀{Γt}{K L C}{Γp : ConPf Γt} → Pf (Γp ▸p K) C → Pf (Γp ▸p L) C → Pf Γp (K ∨ L) → Pf Γp C
    ∨intro₁ : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf Γp K → Pf Γp (K ∨ L)
    ∨intro₂ : ∀{Γt}{K L}{Γp : ConPf Γt} → Pf Γp L → Pf Γp (K ∨ L)

    ∀intro  : ∀{Γt}{K Γp} → Pf {Γt ▸t} (Γp [ pt ]C) K → Pf {Γt} Γp (∀' K)
    un∀ : ∀{Γt}{K Γp} → Pf Γp (∀' K) → (t : Tm Γt) → Pf Γp (K [ idt ,t t ]F)

    ∃intro : ∀{Γt K}{Γp : ConPf Γt} → (t : Tm Γt) → Pf Γp (K [ idt ,t t ]F) → Pf Γp (∃' K)
    ∃elim  : ∀{Γt K L}{Γp : ConPf Γt}{Γp' : ConPf (Γt ▸t)} → Pf Γp (∃' K) → Pf (Γp' ▸p K) (L [ pt ]F) → Pf Γp L

    ref  : ∀{Γt}{a}{Γp : ConPf Γt} → Pf Γp (Eq a a)
    subst' : ∀{Γt}(K : For (Γt ▸t)){t t' : Tm Γt}{Γp} → Pf Γp (Eq t t') → Pf Γp (K [ idt ,t t ]F) → Pf Γp (K [ idt ,t t' ]F)
    _[_]P : ∀{Γt}{K}{Γp : ConPf Γt} → Pf Γp K → ∀{Δt : ConTm} → (γ : Subt Δt Γt) → Pf (Γp [ γ ]C) (K [ γ ]F)
    _[_]p : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf Γp K → ∀{Γp'} → Subp Γp' Γp → Pf Γp' K
    qp : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf (Γp ▸p K) K

    dne : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf Γp (((K ⊃ ⊥) ⊃ ⊥) ⊃ K) 

  ⊃elim : ∀{Γ K L}{Γp : ConPf Γ} → Pf Γp (K ⊃ L) → Pf (Γp ▸p K) L
  ⊃elim m = (m [ pp ]p) $ qp

  ∀elim : ∀{Γ K Γp} → Pf {Γ} Γp (∀' K) → Pf {Γ ▸t} (Γp [ pt ]C) K
  ∀elim {K = K}{Γp} k = substp (Pf (Γp [ pt ]C))
    (trans (trans (sym [∘]F) (cong (λ z → K [ z ,t var vz ]F) (trans ass (trans (cong (pt ∘t_) ▸tβ₁) idr)))) [id]F)
    (un∀ (k [ pt ]P) (var vz))

  Con : Set
  Con = Σ ConTm ConPf

  Sub : Con → Con → Set
  Sub (Δt ,Σ Δp) (Γt ,Σ Γp) = Σsp (Subt Δt Γt) λ γt → Subp Δp (Γp [ γt ]C)

  _∘_ : {Γ Δ Θ : Con} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  (γt ,Σ γp) ∘ (δt ,Σ δp) = (γt ∘t δt) ,Σ substp (Subp _) (sym [∘]C) (γp [ δt ]s ∘p δp)

  id : {Γ : Con} → Sub Γ Γ
  id {Γt ,Σ Γp} = idt ,Σ substp (Subp Γp) (sym [id]C) idp

  ◆ : Con
  ◆ = ◆t ,Σ ◆p

  ε : {Γ : Con} → Sub Γ ◆
  ε {Γt ,Σ Γp} = εt ,Σ εp

  ◆η : {Γ : Con} (σ : Sub Γ ◆) → σ ≡ ε {Γ}
  ◆η {Γt ,Σ Γp} (εt ,Σ _) = refl

  -- We give db indexes in the syntax

  db0 : ∀{Γt Γp K} → Pf {Γt} (Γp ▸p K) K
  db0 = qp

  db1 : ∀{Γt Γp K L} → Pf {Γt} (Γp ▸p K ▸p L) K
  db1 = qp [ pp ]p

  db2 : ∀{Γt Γp K L M} → Pf {Γt} (Γp ▸p K ▸p L ▸p M) K
  db2 = (qp [ pp ]p) [ pp ]p

  -- We prove that ¬¬_ is a monad
  join¬¬ : ∀{Γt Γp}{K} → Pf {Γt} Γp (¬ ¬ (¬ ¬ K)) → Pf {Γt} Γp (¬ ¬ K)
  join¬¬ x = ⊃intro ((x [ pp ]p) $ (⊃intro (db0 $ db1)))

  pp⁺ : ∀{Γt}{Γp Δp}{K} → (γ : Subp {Γt} Γp Δp) → Subp {Γt} (Γp ▸p K) (Δp ▸p K)
  pp⁺ γ = (γ ∘p pp) ,p qp

  pt⁺ : ∀{Γt Δt} → (γ : Subt Γt Δt) → Subt (Γt ▸t) (Δt ▸t)
  pt⁺ γ = (γ ∘t pt) ,t qt

IM : Model _ _ _ _ _
IM = record
  { Con = Con
  ; Sub = Sub
  ; _∘_ = _∘_
  ; id = id
  ; ass = mk,sp= ass
  ; idl = mk,sp= idl
  ; idr = mk,sp= idr
  ; ◆ = ◆
  ; ε = ε
  ; ◆η = ◆η
  ; For = λ (Γt ,Σ Γp) → For Γt
  ; _[_]F = λ K (γt ,Σ γp) → K [ γt ]F
  ; [∘]F = [∘]F
  ; [id]F = [id]F
  ; Pf = λ (Γt ,Σ Γp) K → Pf {Γt} Γp K
  ; _[_]p = λ Pk (γt ,Σ γp) → (Pk [ γt ]P) [ γp ]p
  ; _▸p_ = λ (Γt ,Σ Γp) K → (Γt ,Σ (Γp ▸p K))
  ; _,p_ = λ (Γt ,Σ Γp) Pk → Γt ,Σ (Γp ,p Pk)
  ; pp = λ {Γ@(Γt ,Σ Γp)} {K} → (proj₁ (id {Γ})) ,Σ substp (λ x → Subp (Γp ▸p K) x) (sym [id]C) (pp {Γt} {Γp} {K})
  ; qp = λ {Γ@(Γt ,Σ Γp)} {K} → substp (λ x → Pf (Γp ▸p K) x) (sym [id]F) (qp {Γt} {Γp} {K})
  ; ▸pβ₁ = mk,sp= idl
  ; ▸pη  = mk,sp= idl
  ; ⊥ = ⊥
  ; ⊥[] = refl
  ; exfalso = exfalso
  ; ⊤ = ⊤
  ; ⊤[] = refl
  ; tt = tt
  ; _⊃_ = _⊃_
  ; ⊃[] = refl
  ; ⊃intro = λ {Γ}{K} x → substp (Pf (proj₂ Γ)) (cong (K ⊃_) [id]F) (⊃intro x)
  ; ⊃elim = λ {Γ}{K}{L} pf → substp (Pf (proj₂ Γ ▸p K)) (sym [id]F) (⊃elim {proj₁ Γ} {K}{L} {proj₂ Γ} pf)
  ; _∧_    = _∧_
  ; ∧[]    = refl
  ; ∧intro = ∧intro
  ; ∧elim₁ = ∧elim₁
  ; ∧elim₂ = ∧elim₂
  ; _∨_    = _∨_
  ; ∨[]    = refl
  ; ∨elim = λ {Γ}{K}{L}{C} PfK PfL PfKL → substp (Pf (proj₂ Γ)) [id]F (∨elim PfK PfL PfKL)
  ; ∨intro₁ = ∨intro₁
  ; ∨intro₂ = ∨intro₂
  ; Tm      = λ (Γt ,Σ Γp) → Tm Γt
  ; _[_]t   = λ t (γt ,Σ γp) → t [ γt ]t
  ; [∘]t    = λ {(Γt ,Σ Γp)} {t} → [∘]t {Γt} {t}
  ; [id]t   = [id]t
  ; _▸t     = λ (Γt ,Σ Γp) → (Γt ▸t) ,Σ Γp [ pt ]C
  ; _,t_    = λ {Γ} {Δ} (γt ,Σ γp) t → (γt ,t t) ,Σ substp (λ x → Subp (proj₂ Δ) x) (sym (trans (sym [∘]C) (cong (λ x → (proj₂ Γ) [ x ]C) ▸tβ₁))) γp
  ; pt      = λ {(Γt ,Σ Γp)} → pt {Γt} ,Σ (idp {Γt ▸t} {Γp [ pt ]C })
  ; qt      = λ {(Γt ,Σ Γp)} → qt {Γt}
  ; ▸tβ₁    = mk,sp= ▸tβ₁
  ; ▸tβ₂    = refl
  ; ▸tη     = mk,sp= ▸tη
  ; Tms = λ (Γt ,Σ Γp) → Tms Γt -- Tms
  ; _[_]ts = λ ts (γt ,Σ γp) → ts [ γt ]ts
  ; [∘]ts = [∘]ts
  ; [id]ts = [id]ts
  ; εs = *
  ; ◆sη = λ _ → refl
  ; _,s_ = _,Σ_
  ; π₁ = proj₁
  ; π₂ = proj₂
  ; ▸sβ₁ = refl
  ; ▸sβ₂ = refl
  ; ▸sη = refl
  ; ,[] = refl
  ; fun = fun
  ; fun[] = refl
  ; rel = rel
  ; rel[] = refl
  ; ∀' = ∀'
  ; ∀[] = refl
  ; ∀intro = ∀intro
  ; ∀elim = ∀elim
  ; ∃' = ∃'
  ; ∃[] = refl
  ; ∃intro = ∃intro
  ; ∃elim = λ {Γ}{K}{L} Pf∃K PfL → ∃elim Pf∃K (substp (Pf (proj₂ Γ [ ⌜ V.wk V.id ⌝ ]C ▸p K) ) (cong (L [_]F) ▸tβ₁) PfL)
  ; Eq = Eq
  ; Eq[] = refl
  ; Eqrefl = ref
  ; subst' = λ K → subst' K
  ; dne = dne
  }
  where
    open I