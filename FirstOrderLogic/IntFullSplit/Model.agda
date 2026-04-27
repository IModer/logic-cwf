open import lib

module FirstOrderLogic.IntFullSplit.Model
    (funar : ℕ → Set)
    (relar : ℕ → Set)
    where

record Model (i j k l m : Level) : Set (lsuc (i ⊔ j ⊔ k ⊔ l ⊔ m)) where
    infixl 5 _▸t _▸p_
    infixl 5 _,t_ _,p_ _,s_
    infixr 7 _∘t_ _∘p_
    infixl 8 _[_]t _[_]ts _[_]F _[_]P _[_]p _[_]C
    infixr 6 _⊃_
    field

        Cont : Set i
        Subt : Cont → Cont → Set j
        _∘t_ : ∀{Γ Δ Θ} → Subt Δ Γ → Subt Θ Δ → Subt Θ Γ
        idt  : ∀{Γ} → Subt Γ Γ
        asst : ∀{Γ Δ}{γ : Subt Δ Γ}{Θ}{δ : Subt Θ Δ}{Ξ}{θ : Subt Ξ Θ} → (γ ∘t δ) ∘t θ ≡ γ ∘t (δ ∘t θ)
        idlt : ∀{Γ Δ}{γ : Subt Δ Γ} → idt ∘t γ ≡ γ
        idrt : ∀{Γ Δ}{γ : Subt Δ Γ} → γ ∘t idt ≡ γ
        ◆t   : Cont
        εt   : ∀{Γ} → Subt Γ ◆t
        ◆tη  : ∀{Γ}(σ : Subt Γ ◆t) → σ ≡ εt

        For : Cont -> Set k
        _[_]F : ∀{Γ Δ} → For Γ → Subt Δ Γ → For Δ
        [∘]F  : ∀{Γ}{K : For Γ}{Δ}{γ : Subt Δ Γ}{Θ}{δ : Subt Θ Δ} → K [ γ ∘t δ ]F ≡ K [ γ ]F [ δ ]F
        [id]F : ∀{Γ}{K : For Γ} → K [ idt ]F ≡ K

        Tm    : Cont → Set j
        _[_]t : ∀{Γ} → Tm Γ → ∀{Δ} → Subt Δ Γ → Tm Δ
        [∘]t  : ∀{Γ}{t : Tm Γ}{Δ}{γ : Subt Δ Γ}{Θ}{δ : Subt Θ Δ} → t [ γ ∘t δ ]t ≡ t [ γ ]t [ δ ]t
        [id]t : ∀{Γ}{t : Tm Γ} → t [ idt ]t ≡ t
        _▸t   : Cont → Cont
        _,t_  : ∀{Γ Δ} → Subt Δ Γ → Tm Δ → Subt Δ (Γ ▸t)
        pt    : ∀{Γ} → Subt (Γ ▸t) Γ
        qt    : ∀{Γ} → Tm (Γ ▸t)
        ▸tβ₁  : ∀{Γ Δ}{γ : Subt Δ Γ}{t : Tm Δ} → (pt ∘t (γ ,t t)) ≡ γ
        ▸tβ₂  : ∀{Γ Δ}{γ : Subt Δ Γ}{t : Tm Δ} → (qt [ γ ,t t ]t) ≡ t
        ▸tη   : ∀{Γ Δ}{γ : Subt Δ (Γ ▸t)} -> ((pt ∘t γ) ,t (qt [ γ ]t)) ≡ γ -- ∈ (Subt (Γ ▸t) (Γ ▸t))

        Tms    : Cont → ℕ → Set m
        _[_]ts : ∀{Γ n} → Tms Γ n → ∀{Δ} → Subt Δ Γ → Tms Δ n
        [∘]ts  : ∀{Γ n}{ts : Tms Γ n}{Δ}{γ : Subt Δ Γ}{Θ}{δ : Subt Θ Δ} → ts [ γ ∘t δ ]ts ≡ ts [ γ ]ts [ δ ]ts
        [id]ts : ∀{Γ n}{ts : Tms Γ n} → ts [ idt ]ts ≡ ts
        εs     : ∀{Γ} → Tms Γ zero
        ◆sη    : ∀{Γ}(ts : Tms Γ zero) → ts ≡ εs
        _,s_   : ∀{Γ n} → Tms Γ n → Tm Γ → Tms Γ (suc n)
        π₁     : ∀{Γ n} → Tms Γ (suc n) → Tms Γ n
        π₂     : ∀{Γ n} → Tms Γ (suc n) → Tm Γ
        ▸sβ₁   : ∀{Γ n}{ts : Tms Γ n}{t : Tm Γ} → π₁ (ts ,s t) ≡ ts
        ▸sβ₂   : ∀{Γ n}{ts : Tms Γ n}{t : Tm Γ} → π₂ (ts ,s t) ≡ t
        ▸sη    : ∀{Γ n}{ts : Tms Γ (suc n)} → π₁ ts ,s π₂ ts ≡ ts
        ,[]    : ∀{Γ n}{ts : Tms Γ n}{t : Tm Γ}{Δ}{γ : Subt Δ Γ} → (ts ,s t) [ γ ]ts ≡ (ts [ γ ]ts) ,s (t [ γ ]t)

        fun  : ∀{Γ}(n : ℕ) → funar n → Tms Γ n → Tm Γ
        fun[] : ∀{Γ n a ts Δ}{γ : Subt Δ Γ} → ((fun n a ts) [ γ ]t) ≡ fun n a (ts [ γ ]ts)
        rel  : ∀{Γ}(n : ℕ) → relar n → Tms Γ n → For Γ
        rel[] : ∀{Γ n a ts Δ}{γ : Subt Δ Γ} → ((rel n a ts) [ γ ]F) ≡ rel n a (ts [ γ ]ts)

        Conp  : Cont -> Set i
        _[_]C : ∀{Γt Δt} -> Conp Γt -> Subt Δt Γt -> Conp Δt
        [id]C : ∀{Γt}{Γ : Conp Γt} -> Γ [ idt ]C ≡ Γ
        [∘]C  : ∀{Γt Δt Θt}{Γ : Conp Γt}{γ : Subt Δt Γt}{δ : Subt Θt Δt} -> Γ [ γ ∘t δ ]C ≡ Γ [ γ ]C [ δ ]C

        Subp : ∀{Γt} -> Conp Γt → Conp Γt → Prop j
        _∘p_ : ∀{Γt}{Γ Δ Θ : Conp Γt} → Subp Δ Γ → Subp Θ Δ → Subp Θ Γ
        idp  : ∀{Γt}{Γ : Conp Γt} → Subp Γ Γ
        --assp : ∀{Γt}{Γ Δ : Conp Γt}{γ : Subp Δ Γ}{Θ}{δ : Subp Θ Δ}{Ξ}{θ : Subp Ξ Θ} → (γ ∘p δ) ∘p θ ≡ γ ∘p (δ ∘p θ)
        --idlp : ∀{Γt}{Γ Δ : Conp Γt}{γ : Subp Δ Γ} → idp ∘p γ ≡ γ
        --idrp : ∀{Γt}{Γ Δ : Conp Γt}{γ : Subp Δ Γ} → γ ∘p idp ≡ γ
        ◆p   : ∀{Γt} -> Conp Γt 
        -- ◆p[] : ∀{Γt Δt}{γt : Subt Δt Γt} -> ◆p [ γt ]C ≡ ◆p
        εp   : ∀{Γt}{Γ : Conp Γt} → Subp Γ ◆p
        -- ◆pη  : ∀{Γt}{Γ : Conp Γt}(σ : Subp Γ ◆p) → σ ≡ εp


        Pf    : {Γt : Cont} → Conp Γt -> For Γt → Prop l
        _[_]p : ∀{Γt}{Γ : Conp Γt}{K} → Pf Γ K → ∀{Δt} → (γt : Subt Δt Γt) → Pf (Γ [ γt ]C) (K [ γt ]F)
        _[_]P : ∀{Γt}{Γ : Conp Γt}{K} → Pf Γ K → ∀{Δ} → (γ : Subp Δ Γ) → Pf Δ K
        _▸p_  : ∀{Γt} -> Conp Γt → For Γt → Conp Γt
        _,p_  : ∀{Γt}{Γ Δ : Conp Γt} → (γ : Subp Δ Γ) → ∀{K : For Γt} → Pf Δ K → Subp Δ (Γ ▸p K)
        pp    : ∀{Γt}{Γ : Conp Γt}{K} → Subp (Γ ▸p K) Γ
        qp    : ∀{Γt}{Γ : Conp Γt}{K} → Pf   (Γ ▸p K) K
        ◆p[] : ∀{Γt Δt}{γt : Subt Δt Γt} -> ◆p [ γt ]C ≡ ◆p
        ▸p[] : ∀{Γt Δt}{Γp : Conp Γt}{K : For Γt}{γt : Subt Δt Γt} -> (Γp ▸p K) [ γt ]C ≡ (Γp [ γt ]C ▸p K [ γt ]F) 
        --▸pβ₁  : ∀{Γt}{Γ Δ : Conp Γt}{γ : Subp Δ Γ}{K}{k : Pf Δ K} → pp ∘p (γ ,p k) ≡ γ
        --▸pη   : ∀{Γt}{Γ : Conp Γt}{K} -> idp ≡ (pp ,p qp) ∈ Subp (Γ ▸p K) (Γ ▸p K)
        
        ⊥    : ∀{Γt} → For Γt
        ⊥[]  : ∀{Γt Δt}{γ : Subt Δt Γt} → ⊥ [ γ ]F ≡ ⊥
        exfalso : ∀{Γt K}{Γ : Conp Γt} → Pf Γ ⊥ → Pf Γ K

        ⊤    : ∀{Γt} → For Γt
        ⊤[]  : ∀{Γt Δt}{γt : Subt Δt Γt} → ⊤ [ γt ]F ≡ ⊤
        tt   : ∀{Γt}{Γ : Conp Γt} → Pf Γ ⊤

        _⊃_    : ∀{Γt} → For Γt → For Γt → For Γt
        ⊃[]    : ∀{Γt K L Δt}{γt : Subt Δt Γt} → (K ⊃ L) [ γt ]F ≡ K [ γt ]F ⊃ L [ γt ]F
        ⊃intro : ∀{Γt K L}{Γ : Conp Γt} → Pf (Γ ▸p K) L → Pf Γ (K ⊃ L)
        ⊃elim  : ∀{Γt K L}{Γ : Conp Γt} → Pf Γ (K ⊃ L) → Pf (Γ ▸p K) L

        _∧_    : ∀{Γt} → For Γt → For Γt → For Γt
        ∧[]    : ∀{Γt K L Δt}{γt : Subt Δt Γt} → (K ∧ L) [ γt ]F ≡ (K [ γt ]F) ∧ (L [ γt ]F)
        ∧intro : ∀{Γt}{K L}{Γ : Conp Γt} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
        ∧elim₁ : ∀{Γt}{K L}{Γ : Conp Γt} → Pf Γ (K ∧ L) → Pf Γ K
        ∧elim₂ : ∀{Γt}{K L}{Γ : Conp Γt} → Pf Γ (K ∧ L) → Pf Γ L

        _∨_     : ∀{Γt} → For Γt → For Γt → For Γt
        ∨[]     : ∀{Γt K L Δt}{γt : Subt Δt Γt} → (K ∨ L) [ γt ]F ≡ (K [ γt ]F) ∨ (L [ γt ]F)
        ∨elim   : ∀{Γt}{K L C}{Γ : Conp Γt} → Pf (Γ ▸p K) C → Pf (Γ ▸p L) C → Pf Γ (K ∨ L) → Pf Γ C
        ∨intro₁ : ∀{Γt}{K L}{Γ : Conp Γt} → Pf Γ K → Pf Γ (K ∨ L)
        ∨intro₂ : ∀{Γt}{K L}{Γ : Conp Γt} → Pf Γ L → Pf Γ (K ∨ L)

        ∀'     : ∀{Γt} → For (Γt ▸t) → For Γt
        ∀[]    : ∀{Γt K Δt}{γt : Subt Δt Γt} → (∀' K) [ γt ]F ≡ ∀' (K [ γt ∘t pt ,t qt ]F)
        ∀intro : ∀{Γt}{K}{Γ : Conp Γt} → Pf (Γ [ pt ]C) K → Pf Γ (∀' K)
        ∀elim  : ∀{Γt}{K : For (Γt ▸t)}{Γ : Conp Γt} → Pf Γ (∀' K) → Pf (Γ [ pt ]C) K
        
        ∃'     : ∀{Γt} → For (Γt ▸t) → For Γt
        ∃[]    : ∀{Γt K Δt}{γt : Subt Δt Γt} → (∃' K) [ γt ]F ≡ ∃' (K [ (γt ∘t pt) ,t qt ]F) 
        -- ∃ : (Tm -> For) -> For
        -- ∃intro : (t : Tm) -> Pf (K t) -> Pf (∃ K)
        -- ∃elim  : Pf (∃ K) -> ∃ (t : Tm) Pf (K t)
        ∃intro : ∀{Γt K} → (t : Tm Γt){Γ : Conp Γt} → Pf Γ (K [ idt ,t t ]F) → Pf Γ (∃' K)
        ∃elim : ∀{Γt}{K : For (Γt ▸t)}{Γp : Conp Γt}{L : For Γt} ->
            Pf Γp (∃' K) -> Pf ((Γp [ pt ]C) ▸p K [ pt ,t qt ]F) (L [ pt ]F) -> Pf Γp L
        Eq     : ∀{Γt} → Tm Γt → Tm Γt → For Γt
        Eq[]   : ∀{Γt Δt}{γt : Subt Δt Γt}{t t' : Tm Γt} → (Eq t t') [ γt ]F ≡ Eq (t [ γt ]t) (t' [ γt ]t)
        Eqrefl : ∀{Γt}{t : Tm Γt}{Γ : Conp Γt} → Pf Γ (Eq t t)
        subst' : ∀{Γt}(K : For (Γt ▸t)){t t' : Tm Γt}{Γ : Conp Γt} → Pf Γ (Eq t t') → Pf Γ (K [ idt ,t t ]F) → Pf Γ (K [ idt ,t t' ]F)

    ,t∘t : ∀{Γt Δt Θt}{γt : Subt Δt Γt}{δt : Subt Θt Δt}{t : Tm Δt} -> (γt ,t t) ∘t δt ≡ (γt ∘t δt) ,t (t [ δt ]t)
    ,t∘t {Γt} {Δt} {Θt} {γt} {δt} {t} =
        trans (sym ▸tη) (cong (λ z → proj₁ z ,t proj₂ z) (mk,= (trans (sym asst) (cong (_∘t δt) ▸tβ₁)) (trans [∘]t (cong (_[ δt ]t) ▸tβ₂)))) 

    ▸tη' : ∀{Γt} -> pt ,t qt ≡ (idt {Γt ▸t})
    ▸tη' = trans (cong (λ z → proj₁ z ,t proj₂ z) (mk,= (sym idrt) (sym [id]t))) ▸tη