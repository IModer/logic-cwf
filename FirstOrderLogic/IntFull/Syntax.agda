{-# OPTIONS --prop #-}

open import FirstOrderLogic.IntFull.Model
open import lib

-- We give the initial model of FOLClassicMinimal
-- We give it as a normal form, meaning its a inductive
-- datatype but we can prove it satisfies the equations
module FirstOrderLogic.IntFull.Syntax
    (funar : ℕ → Set)
    (relar : ℕ → Set)
    where

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

        ∀intro  : ∀{Γt}{K Γp} → 
            Pf {Γt ▸t} (Γp [ pt ]C) K → 
            -----------------------------
            Pf {Γt} Γp (∀' K)
        
        un∀ : ∀{Γt}{K Γp} → 
            Pf Γp (∀' K) → (t : Tm Γt) → 
            -----------------------------
                Pf Γp (K [ idt ,t t ]F)

        ∃intro : ∀{Γt K}{Γp : ConPf Γt} → (t : Tm Γt) → 
            Pf Γp (K [ idt ,t t ]F) → 
            -----------------------------
            Pf Γp (∃' K)
        
        ∃elim  : ∀{Γt K L}{Γp : ConPf Γt}{Γp' : ConPf (Γt ▸t)} → 
            Pf Γp (∃' K) → Pf (Γp' ▸p K) (L [ pt ]F) → 
            ----------------------------------------------
                        Pf Γp L

        -- ∃intro : ∀{Γt K}{Γp : ConPf Γt} → (∃ (Tm Γt) (λ t → Pf Γp (K [ idt ,t t ]F))) → Pf Γp (∃' K)
        
        ref  : ∀{Γt}{a}{Γp : ConPf Γt} → Pf Γp (Eq a a)
        subst' : ∀{Γt}(K : For (Γt ▸t)){t t' : Tm Γt}{Γp} → Pf Γp (Eq t t') → Pf Γp (K [ idt ,t t ]F) → Pf Γp (K [ idt ,t t' ]F)
        _[_]P : ∀{Γt}{K}{Γp : ConPf Γt} → Pf Γp K → ∀{Δt : ConTm} → (γ : Subt Δt Γt) → Pf (Γp [ γ ]C) (K [ γ ]F)
        _[_]p : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf Γp K → ∀{Γp'} → Subp Γp' Γp → Pf Γp' K
        qp : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf (Γp ▸p K) K

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

    -- We also dont need any of these proofs to prove substitution of Tm ^ n if we use Tms
    --ts[] : ∀{Γ}{Δ}{n : ℕ}{γ : Sub Δ Γ}{ts : Tm (proj₁ Γ) ^ n} → ts [ proj₁ γ ]ts ≡ ind^ {T = Tm (proj₁ Γ)}{C = Tm (proj₁ Δ) ^_} (λ _ → *) (λ _ t ts' → t [ proj₁ γ ]t ,Σ ts') ts
    --ts[] {Γ} {Δ} {zero} {γ} {ts} = refl
    --ts[] {Γ} {Δ} {suc n} {γ} {t ,Σ ts} = cong (t [ proj₁ γ ]t ,Σ_) (ts[] {Γ} {Δ} {n} {γ} {ts})


    --funLemma : ∀{Γ}{n : ℕ}{a : funar n}{ts : Tm (proj₁ Γ) ^ n}{Δ}{γ : Sub Δ Γ} →
    --  fun n a (ts [ proj₁ γ ]ts)
    --  ≡
    --  fun n a (ind^ {T = Tm (proj₁ Γ)}{C = Tm (proj₁ Δ) ^_} (λ _ → *) (λ _ t ts' → t [ proj₁ γ ]t ,Σ ts') ts)
    --funLemma {Γ} {zero} {a} {ts} {Δ} {γt ,Σ γp} = refl
    --funLemma {Γ} {suc n} {a} {t ,Σ ts} {Δ} {γt ,Σ γp} = cong (λ x → fun (suc n) a x) (mk,= refl (ts[] {Γ} {Δ} {n} {γt ,Σ γp} {ts}))

    --relLemma : ∀{Γ}{n : ℕ}{a : relar n}{ts : Tm (proj₁ Γ) ^ n}{Δ}{γ : Sub Δ Γ} →
    --  rel n a (ts [ proj₁ γ ]ts)
    --  ≡
    --  rel n a (ind^ {T = Tm (proj₁ Γ)} {C = Tm (proj₁ Δ) ^_} (λ _ → *) (λ _ t ts₁ → t [ proj₁ γ ]t ,Σ ts₁) ts)
    --relLemma {Γ} {zero} {a} {ts} {Δ} {γt ,Σ γp} = refl
    --relLemma {Γ} {suc n} {a} {t ,Σ ts} {Δ} {γt ,Σ γp} = cong (λ x → rel (suc n) a x) (mk,= refl (ts[] {Γ} {Δ} {n} {γt ,Σ γp} {ts}))

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

    I : Model funar relar _ _ _ _ _
    I = record
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
        }