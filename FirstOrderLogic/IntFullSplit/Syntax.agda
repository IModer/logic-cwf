{-# OPTIONS --prop #-}

open import FirstOrderLogic.IntFullSplit.Model
open import lib

-- We give the initial model of FOLClassicMinimal
-- We give it as a normal form, meaning its a inductive
-- datatype but we can prove it satisfies the equations
module FirstOrderLogic.IntFullSplit.Syntax
    (funar : ℕ → Set)
    (relar : ℕ → Set)
    where

    infixl 5 _▸t _▸p_
    infixl 5 _,t_ _,p_
    infixr 7 _∘t_ _∘p_
    infixl 8 _[_]t _[_]F _[_]C _[_]P _[_]p _[_]v _[_]s _[_]ts
    infixr 6 _⊃_
    infixr 7 _∧_ _∨_
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

    ◆tη : {Γ : ConTm} (σ : Subt Γ ◆t) → σ ≡ εt
    ◆tη εt = refl

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

    test : ∀{Γt} -> (Γp : ConPf Γt) -> ConPf (Γt ▸t)
    test {◆t} Γp = ◆p
    test {Γt ▸t} Γp = ◆p

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

        ∃intro : ∀{Γt K}{Γp : ConPf Γt} → 
            (t : Tm Γt) → Pf Γp (K [ idt ,t t ]F) →
            ------------------------------------------
            Pf Γp (∃' K)

        -- ∃intro : ∃ (t : Tm) (Pf (K t))  -> Pf ∃' K
        -- ∃intro : (t : Tm) -> (Pf (K t)) -> Pf ∃' K
        -- ∃elim  : Pf ∃' K -> ∃ (t : Tm) (Pf (K t))
        -- ∃elim  : Pf ∃' K -> (∃ (t : Tm) (Pf (K t)) -> Pf C) -> Pf C
        -- ∃elim  : Pf ∃' K -> ((t : Tm) -> (Pf (K t)) -> Pf C) -> Pf C

        ∃elim  : ∀{Γt}{K : For (Γt ▸t)}{Γp : ConPf Γt}{L : For Γt} ->
          Pf Γp (∃' K) -> Pf ((Γp [ pt ]C) ▸p K [ pt ,t qt ]F) (L [ pt ]F) -> Pf Γp L
        -- ∃elim  : ∀{Γt : ConTm}{K : For (Γt ▸t)}{Γp : ConPf Γt} -> 
        --    Pf Γp (∃' K) -> {!   !}
            {-
            ∀{Γt : ConTm}{K : For (Γt ▸t)}{Γp : ConPf Γt}{Γp' : ConPf (Γt ▸t)}{L : For Γt} → 
            Pf Γp (∃' K) → Pf (Γp' ▸p (K [ idt ,t qt ]F)) (L ) {-Pf (Γ ▸p K [ idt ,t qt ]F) L-} -> 
            ------------------------------------------
            Pf Γp L
            -} 

          {-
          ∀{Γt : ConTm}{K : For (Γt ▸t)}{L : For Γt}{Γp : ConPf Γt} → 
            Pf Γp (∃' K) → Pf {!   !} L → 
            ---------------------------------------------
                        Pf Γp L
          -}
        
        ref  : ∀{Γt}{a}{Γp : ConPf Γt} → Pf Γp (Eq a a)
        subst' : ∀{Γt}(K : For (Γt ▸t)){t t' : Tm Γt}{Γp} → Pf Γp (Eq t t') → Pf Γp (K [ idt ,t t ]F) → Pf Γp (K [ idt ,t t' ]F)
        _[_]p : ∀{Γt}{K}{Γp : ConPf Γt} → Pf Γp K → ∀{Δt : ConTm} → (γ : Subt Δt Γt) → Pf (Γp [ γ ]C) (K [ γ ]F)
        _[_]P : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf Γp K → ∀{Γp'} → Subp Γp' Γp → Pf Γp' K
        qp : ∀{Γt}{Γp : ConPf Γt}{K : For Γt} → Pf (Γp ▸p K) K

    ⊃elim : ∀{Γ K L}{Γp : ConPf Γ} → Pf Γp (K ⊃ L) → Pf (Γp ▸p K) L
    ⊃elim m = (m [ pp ]P) $ qp

    ∀elim : ∀{Γ K Γp} → Pf {Γ} Γp (∀' K) → Pf {Γ ▸t} (Γp [ pt ]C) K
    ∀elim {K = K}{Γp} k = substp (Pf (Γp [ pt ]C))
        (trans (trans (sym [∘]F) (cong (λ z → K [ z ,t var vz ]F) (trans ass (trans (cong (pt ∘t_) ▸tβ₁) idr)))) [id]F)
        (un∀ (k [ pt ]p) (var vz))

    -- ∀x P ∧ ∀x Q -> ∀ x (P ∧ Q)
    example1F : (P Q : For (◆t ▸t)) -> For ◆t
    example1F P Q = ((∀' P) ∧ (∀' Q)) ⊃ (∀' (P ∧ Q))

    example1P : (P Q : For (◆t ▸t)) -> Pf (◆p) (example1F P Q)
    example1P P Q = ⊃intro (∀intro (∧intro (∀elim (∧elim₁ qp)) (∀elim (∧elim₂ qp))))

    example2F : {A B C : For ◆t} -> For ◆t
    example2F {A}{B}{C} = (A ∨ B) ∧ C ⊃ (A ∧ C) ∨ (B ∧ C)

    example2P : {A B C : For ◆t} -> Pf ◆p (example2F {A}{B}{C})
    example2P = ⊃intro (∨elim 
        (∨intro₁ (∧intro qp (∧elim₂ (qp [ pp ]P)))) 
        (∨intro₂ (∧intro qp (∧elim₂ (qp [ pp ]P)))) 
        (∧elim₁ qp))

    example2F' : {A B C : For ◆t} -> For ◆t
    example2F' {A}{B}{C} = (A ∧ C) ∨ (B ∧ C) ⊃ (A ∨ B) ∧ C

    example2P' : {A B C : For ◆t} -> Pf ◆p (example2F' {A}{B}{C})
    example2P' = ⊃intro (∨elim 
        (∧intro (∨intro₁ (∧elim₁ qp)) (∧elim₂ qp)) 
        (∧intro (∨intro₂ (∧elim₁ qp)) (∧elim₂ qp)) 
        qp)

    -- ∃x (P ∧ Q) -> ∃x P ∧ ∃x Q
    example3F : (P Q : For (◆t ▸t)) -> For ◆t
    example3F P Q = ∃' (P ∧ Q) ⊃ (∃' P ∧ ∃' Q)
    -- ∃intro {◆t} {P} {◆p ▸p ∃' (P ∧ Q)} {!   !} {!   !}
    example3P : (P Q : For (◆t ▸t)) -> Pf (◆p) (example3F P Q)
    example3P P Q = ⊃intro (∃elim qp 
      (∧intro 
        (∃intro qt (substp (Pf _) [∘]F (∧elim₁ qp))) 
        (∃intro qt (substp (Pf _) [∘]F (∧elim₂ qp)))))

    I : Model funar relar _ _ _ _ _
    I = record
      { Cont = ConTm
      ; Subt = Subt
      ; _∘t_ = λ γ -> _∘t_ γ
      ; idt = idt
      ; asst = ass
      ; idlt = idl
      ; idrt = idr
      ; ◆t = ◆t
      ; εt = εt
      ; ◆tη = ◆tη
      ; For = For
      ; _[_]F = _[_]F
      ; [∘]F = [∘]F
      ; [id]F = [id]F
      ; Tm = Tm
      ; _[_]t = _[_]t
      ; [∘]t = λ {Γ}{t} -> [∘]t {Γ}{t}
      ; [id]t = [id]t
      ; _▸t = _▸t
      ; _,t_ = _,t_
      ; pt = pt
      ; qt = qt
      ; ▸tβ₁ = ▸tβ₁
      ; ▸tβ₂ = refl
      ; ▸tη = refl
      ; Tms = Tms
      ; _[_]ts = _[_]ts
      ; [∘]ts = [∘]ts
      ; [id]ts = [id]ts
      ; εs = *
      ; ◆sη = λ ts → refl
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
      ; Conp = ConPf
      ; _[_]C = λ γ -> _[_]C γ
      ; [id]C = [id]C
      ; [∘]C = [∘]C
      ; Subp = Subp
      ; _∘p_ = _∘p_
      ; idp = idp
      ; ◆p = ◆p
      ; εp = εp
      ; Pf = Pf
      ; _[_]P = _[_]P
      ; _[_]p = _[_]p
      ; _▸p_ = _▸p_
      ; _,p_ = λ γ -> _,p_ γ
      ; pp = pp
      ; qp = qp
      ; ⊥ = ⊥
      ; ⊥[] = refl
      ; exfalso = exfalso
      ; ⊤ = ⊤
      ; ⊤[] = refl
      ; tt = tt
      ; _⊃_ = _⊃_
      ; ⊃[] = refl
      ; ⊃intro = ⊃intro
      ; ⊃elim = ⊃elim
      ; _∧_ = _∧_
      ; ∧[] = refl
      ; ∧intro = ∧intro
      ; ∧elim₁ = ∧elim₁
      ; ∧elim₂ = ∧elim₂
      ; _∨_ = _∨_
      ; ∨[] = refl
      ; ∨elim = ∨elim
      ; ∨intro₁ = ∨intro₁
      ; ∨intro₂ = ∨intro₂
      ; ∀' = ∀'
      ; ∀[] = refl
      ; ∀intro = ∀intro
      ; ∀elim = ∀elim
      ; ∃' = ∃'
      ; ∃[] = refl
      ; ∃intro = λ t -> ∃intro t
      ; ∃elim = ∃elim
      ; Eq = Eq
      ; Eq[] = refl
      ; Eqrefl = ref
      ; subst' = subst'
      }  