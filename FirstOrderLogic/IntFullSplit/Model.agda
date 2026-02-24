{-# OPTIONS --prop #-}

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
    ▸tη   : ∀{Γ} → idt ≡ (pt ,t qt) ∈ (Subt (Γ ▸t) (Γ ▸t))

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
    εp   : ∀{Γt}{Γ : Conp Γt} → Subp Γ ◆p
    --◆pη  : ∀{Γt}{Γ : Conp Γt}(σ : Subp Γ ◆p) → σ ≡ εp

    Pf    : {Γt : Cont} → Conp Γt -> For Γt → Prop l
    _[_]p : ∀{Γt}{Γ : Conp Γt}{K} → Pf Γ K → ∀{Δt} → (γt : Subt Δt Γt) → Pf (Γ [ γt ]C) (K [ γt ]F)
    _[_]P : ∀{Γt}{Γ : Conp Γt}{K} → Pf Γ K → ∀{Δ} → (γ : Subp Δ Γ) → Pf Δ K
    _▸p_  : ∀{Γt} -> Conp Γt → For Γt → Conp Γt
    _,p_  : ∀{Γt}{Γ Δ : Conp Γt} → (γ : Subp Δ Γ) → ∀{K : For Γt} → Pf Δ K → Subp Δ (Γ ▸p K)
    pp    : ∀{Γt}{Γ : Conp Γt}{K} → Subp (Γ ▸p K) Γ
    qp    : ∀{Γt}{Γ : Conp Γt}{K} → Pf   (Γ ▸p K) K
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
    -- ∃elim₁ : Pf (∃ K) -> ((t : Tm) -> Pf (K t) -> Pf L) -> Pf L
    ∃intro : ∀{Γt K} → (t : Tm Γt){Γ : Conp Γt} → Pf Γ (K [ idt ,t t ]F) → Pf Γ (∃' K)
--    ∃elim  : ∀{Γt K L}{Γ : Conp (Γt ▸t)} → Pf Γ (∃' K) → Pf (Γ ▸p K [ idt ,t qt ]F) L -> Pf Γ L
    ∃elim : ∀{Γt}{K : For (Γt ▸t)}{Γp : Conp Γt}{L : For Γt} ->
          Pf Γp (∃' K) -> Pf ((Γp [ pt ]C) ▸p K [ pt ,t qt ]F) (L [ pt ]F) -> Pf Γp L
    Eq     : ∀{Γt} → Tm Γt → Tm Γt → For Γt
    Eq[]   : ∀{Γt Δt}{γt : Subt Δt Γt}{t t' : Tm Γt} → (Eq t t') [ γt ]F ≡ Eq (t [ γt ]t) (t' [ γt ]t)
    Eqrefl : ∀{Γt}{t : Tm Γt}{Γ : Conp Γt} → Pf Γ (Eq t t)
    subst' : ∀{Γt}(K : For (Γt ▸t)){t t' : Tm Γt}{Γ : Conp Γt} → Pf Γ (Eq t t') → Pf Γ (K [ idt ,t t ]F) → Pf Γ (K [ idt ,t t' ]F)
{-
record DepModel (i j k l m : Level)(M : Model i j k l m) : Set (lsuc (i ⊔ j ⊔ k ⊔ l ⊔ m)) where
    infixl 5 _▸t _▸p_
    infixl 5 _,t_ _,p_
    infixr 7 _∘_
    infixl 8 _[_]t _[_]ts _[_]F _[_]p
    infixr 6 _⊃_

    private module M = Model M
    
    field
        Con : (Γm : M.Con) -> Set i
        Sub : {Γm Δm : M.Con} -> Con Δm -> Con Γm -> M.Sub Δm Γm -> Set j
        id  : {Γm : M.Con}{Γ : Con Γm} -> Sub Γ Γ M.id
        _∘_ : {Γm Δm Θm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Θ : Con Θm} ->
              {γm : M.Sub Δm Γm}{δm : M.Sub Θm Δm} ->
              Sub Δ Γ γm -> Sub Θ Δ δm -> Sub Θ Γ (γm M.∘ δm)
        idl : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} -> id ∘ γ ≡ transport (Sub Δ Γ) (sym M.idl) γ
        idr : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} -> γ ∘ id ≡ transport (Sub Δ Γ) (sym M.idr) γ
        ass : {Γm Δm Θm Ξm : M.Con} ->
              {Γ : Con Γm}{Δ : Con Δm}{Θ : Con Θm}{Ξ : Con Ξm} ->
              {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
              {δm : M.Sub Θm Δm}{δ : Sub Θ Δ δm} ->
              {θm : M.Sub Ξm Θm}{θ : Sub Ξ Θ θm} -> 
              (γ ∘ δ) ∘ θ ≡ transport (Sub Ξ Γ) (sym M.ass) (γ ∘ (δ ∘ θ))
            
        ◆  : Con M.◆
        ε  : {Γm : M.Con}{Γ : Con Γm} -> Sub Γ ◆ M.ε
        ◆η : {Γm : M.Con}{Γ : Con Γm}{σm : M.Sub Γm M.◆} -> (σ : Sub Γ ◆ σm) -> σ ≡ transport (Sub Γ ◆) (sym (M.◆η σm)) ε

        For   : {Γm : M.Con} -> Con Γm -> M.For Γm -> Set k
        _[_]F : ∀{Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Am : M.For Γm}{γm : M.Sub Δm Γm} → For Γ Am → Sub Δ Γ γm → For Δ (Am M.[ γm ]F)
        [id]F  : {Γm : M.Con}{Γ : Con Γm}{Am : M.For Γm}{A : For Γ Am} -> A [ id ]F ≡ transport (For Γ) (sym M.[id]F) A
        [∘]F  : {Γm Δm Θm Ξm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Θ : Con Θm}{Ξ : Con Ξm} ->
                {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
                {δm : M.Sub Θm Δm}{δ : Sub Θ Δ δm} ->
                {Am : M.For Γm}{A : For Γ Am} -> 
                A [ γ ∘ δ ]F ≡ transport (For Θ) (sym M.[∘]F) (A [ γ ]F [ δ ]F)
        
        Pf : {Γm : M.Con} -> (Γ : Con Γm) -> ∀{Am} -> (A : For Γ Am) -> M.Pf Γm Am -> Prop l
        _[_]p : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Am : M.For Γm}{A : For Γ Am}{PfAm : M.Pf Γm Am} -> 
                Pf Γ A PfAm -> 
                {γm : M.Sub Δm Γm}(γ : Sub Δ Γ γm) -> 
                Pf Δ (A [ γ ]F) (PfAm M.[ γm ]p)
        
        _▸p_  : {Γm : M.Con}(Γ : Con Γm) -> ∀{Am} -> For Γ Am -> Con (Γm M.▸p Am)
        _,p_  : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Am : M.For Γm}{γm : M.Sub Δm Γm}{A : For Γ Am}{PfAm : M.Pf Δm (Am M.[ γm ]F)} -> (γ : Sub Δ Γ γm) → Pf Δ (A [ γ ]F) PfAm → Sub Δ (Γ ▸p A) (γm M.,p PfAm)
        pp    : {Γm : M.Con}{Γ : Con Γm}{Am : M.For Γm}{A : For Γ Am} -> 
                Sub {Γm} {Γm M.▸p Am} (Γ ▸p A) Γ M.pp 
        qp    : {Γm : M.Con}{Γ : Con Γm}{Am : M.For Γm}{A : For Γ Am} -> 
                Pf (Γ ▸p A) (A [ pp ]F) M.qp
        ▸pβ₁  : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
                {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
                {Am : M.For Γm}{A : For Γ Am} -> 
                {PfAm : M.Pf Δm (Am M.[ γm ]F)}{PfA : Pf Δ (A [ γ ]F) PfAm} -> 
                pp ∘ (γ ,p PfA) ≡ transport (Sub Δ Γ) (sym M.▸pβ₁) γ
        ▸pη   : {Γm : M.Con}{Γ : Con Γm} ->
                {Am : M.For Γm}{A : For Γ Am} ->
                {γm : M.Sub (Γm M.▸p Am) (Γm M.▸p Am)}{γ : Sub (Γ ▸p A) (Γ ▸p A) γm} ->
                id ≡ transport (Sub (Γ ▸p A) (Γ ▸p A)) (sym M.▸pη) (pp ,p qp)
                {-
                {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
                {Am : M.For Γm}{A : For Γ Am} -> 
                {γpm : M.Sub Δm (Γm M.▸p Am)}{γp : Sub Δ (Γ ▸p A) γpm} ->
                {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
                {PfAm : M.Pf (Γm M.▸p Am) (Am M.[ M.pp ]F)} ->
                -}
                -- (pp ∘ γp) ,p {! substp (λ z -> Pf Δ z _) ? (qp [ γp ]p) !}  ≡ transport (Sub Δ (Γ ▸p A)) (sym M.▸pη) γp
                
                --                         _ = (substp (M.Pf Δm) (sym M.[∘]F) (M.qp M.[ γpm ]p)
                --                         ? = (sym [∘]F)
        
        ⊥   : {Γm : M.Con}{Γ : Con Γm} -> For Γ M.⊥
        ⊥[] : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
              {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
              ⊥ [ γ ]F ≡ transport (For Δ) (sym M.⊥[]) ⊥
        exfalso : {Γm : M.Con}{Γ : Con Γm} ->
                  {Km : M.For Γm}{K : For Γ Km} ->
                  {pf⊥ : M.Pf Γm M.⊥} ->
                  Pf Γ ⊥ pf⊥ -> Pf Γ K (M.exfalso pf⊥)

        ⊤   : {Γm : M.Con}{Γ : Con Γm} -> For Γ M.⊤
        ⊤[] : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
              {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
              ⊤ [ γ ]F ≡ transport (For Δ) (sym M.⊤[]) ⊤
        tt  : {Γm : M.Con}{Γ : Con Γm} ->
              Pf Γ ⊤ M.tt

        _⊃_ : {Γm : M.Con}{Γ : Con Γm} ->
              {Am : M.For Γm}{Bm : M.For Γm} ->
              For Γ Am -> For Γ Bm -> For Γ (Am M.⊃ Bm)
        ⊃[] : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
              {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
              {Am : M.For Γm}{Bm : M.For Γm} ->
              {A : For Γ Am}{B : For Γ Bm} ->
              (A ⊃ B)[ γ ]F ≡ transport (For Δ) (sym M.⊃[]) ((A [ γ ]F) ⊃ (B [ γ ]F))
        ⊃intro : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfab : M.Pf (Γm M.▸p Am) (Bm M.[ M.pp ]F) } ->
            Pf (Γ ▸p A) (B [ pp ]F) pfab -> Pf Γ (A ⊃ B) (M.⊃intro pfab)
        ⊃elim : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfab : M.Pf Γm (Am M.⊃ Bm) } ->
            Pf Γ (A ⊃ B) pfab ->
            Pf (Γ ▸p A) (B [ pp ]F) (M.⊃elim pfab)  



        _∧_ : {Γm : M.Con}{Γ : Con Γm} ->
              {Am : M.For Γm}{Bm : M.For Γm} ->
              For Γ Am -> For Γ Bm -> For Γ (Am M.∧ Bm)
        ∧[] : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
              {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
              {Am : M.For Γm}{Bm : M.For Γm} ->
              {A : For Γ Am}{B : For Γ Bm} ->
              (A ∧ B)[ γ ]F ≡ transport (For Δ) (sym M.∧[]) ((A [ γ ]F) ∧ (B [ γ ]F))
        ∧intro : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfa : M.Pf Γm Am}{pfb : M.Pf Γm Bm} ->  
            Pf Γ A pfa -> Pf Γ B pfb -> Pf Γ (A ∧ B) (M.∧intro pfa pfb)
        ∧elim₁ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfa∧b : M.Pf Γm (Am M.∧ Bm)} ->  
            Pf Γ (A ∧ B) pfa∧b -> Pf Γ A (M.∧elim₁ pfa∧b)
        ∧elim₂ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfa∧b : M.Pf Γm (Am M.∧ Bm)}->  
            Pf Γ (A ∧ B) pfa∧b -> Pf Γ B (M.∧elim₂ pfa∧b)

        _∨_ : {Γm : M.Con}{Γ : Con Γm} ->
              {Am : M.For Γm}{Bm : M.For Γm} ->
              For Γ Am -> For Γ Bm -> For Γ (Am M.∨ Bm)
        ∨[] : {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
              {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
              {Am : M.For Γm}{Bm : M.For Γm} ->
              {A : For Γ Am}{B : For Γ Bm} ->
              (A ∨ B)[ γ ]F ≡ transport (For Δ) (sym M.∨[]) ((A [ γ ]F) ∨ (B [ γ ]F))
        ∨intro₁ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfa : M.Pf Γm Am} ->  
            Pf Γ A pfa -> Pf Γ (A ∨ B) (M.∨intro₁ pfa) 
        ∨intro₂ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {Am : M.For Γm}{Bm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm} ->
            {pfb : M.Pf Γm Bm} ->  
            Pf Γ B pfb -> Pf Γ (A ∨ B) (M.∨intro₂ pfb)
        ∨elim : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {Am : M.For Γm}{Bm : M.For Γm}{Cm : M.For Γm} ->
            {A : For Γ Am}{B : For Γ Bm}{C : For Γ Cm} ->
            {pfac : M.Pf (Γm M.▸p Am) (Cm M.[ M.pp ]F)}{pfbc : M.Pf (Γm M.▸p Bm) (Cm M.[ M.pp ]F)}{pfa∨b : M.Pf Γm (Am M.∨ Bm)} ->  
            Pf (Γ ▸p A) (C [ pp ]F) pfac -> Pf (Γ ▸p B) (C [ pp ]F) pfbc -> Pf Γ (A ∨ B) pfa∨b -> Pf Γ C (M.∨elim pfac pfbc pfa∨b)

        Tm : {Γm : M.Con} -> Con Γm -> M.Tm Γm -> Set j
        _[_]t : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm}{tm : M.Tm Γm} ->
            Tm Γ tm -> Sub Δ Γ γm -> Tm Δ (tm M.[ γm ]t)
        [id]t :
            {Γm : M.Con}{Γ : Con Γm} -> 
            {tm : M.Tm Γm}{t : Tm Γ tm} ->
            t [ id ]t ≡ transport (Tm Γ) (sym M.[id]t) t
        [∘]t : 
            {Γm Δm Θm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Θ : Con Θm} -> 
            {γm : M.Sub Δm Γm}{δm : M.Sub Θm Δm} ->
            {γ : Sub Δ Γ γm}{δ : Sub Θ Δ δm} ->
            {tm : M.Tm Γm}{t : Tm Γ tm} ->
            t [ γ ∘ δ ]t ≡ transport (Tm Θ) (sym M.[∘]t) ((t [ γ ]t) [ δ ]t) 
        _▸t  :
            {Γm : M.Con} ->
            Con Γm -> Con (Γm M.▸t)
        _,t_ : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm} ->
            {tm : M.Tm Δm} ->
            Sub Δ Γ γm -> Tm Δ tm -> Sub Δ (Γ ▸t) (γm M.,t tm)
        pt : {Γm : M.Con}{Γ : Con Γm} -> Sub (Γ ▸t) Γ M.pt
        qt : {Γm : M.Con}{Γ : Con Γm} -> Tm (Γ ▸t) M.qt
        
        ▸tβ₁  : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {tm : M.Tm Δm}{t : Tm Δ tm} -> 
            (pt ∘ (γ ,t t)) ≡ transport (Sub Δ Γ) (sym M.▸tβ₁) γ
        ▸tβ₂  : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {tm : M.Tm Δm}{t : Tm Δ tm} -> 
            (qt [ γ ,t t ]t) ≡ transport (Tm Δ) (sym M.▸tβ₂) t
        ▸tη   : 
            {Γm : M.Con}{Γ : Con Γm} ->
            id ≡ transport (Sub (Γ ▸t) (Γ ▸t)) (sym M.▸tη) (pt ,t qt)
        
        Tms : {Γm : M.Con} -> (Γ : Con Γm) -> (n : ℕ) -> M.Tms Γm n -> Set m
        _[_]ts : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} -> 
            {γm : M.Sub Δm Γm}{n : ℕ}{tmsm : M.Tms Γm n} ->
            Tms Γ n tmsm -> Sub Δ Γ γm -> Tms Δ n (tmsm M.[ γm ]ts)
        [∘]ts : 
            {Γm Δm Θm : M.Con}{Γ : Con Γm}{Δ : Con Δm}{Θ : Con Θm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {δm : M.Sub Θm Δm}{δ : Sub Θ Δ δm} ->
            {n : ℕ}{tmsm : M.Tms Γm n}{tms : Tms Γ n tmsm} -> 
            tms [ γ ∘ δ ]ts ≡ transport (Tms Θ n) (sym M.[∘]ts) (tms [ γ ]ts [ δ ]ts)
        [id]ts : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {n : ℕ}{tmsm : M.Tms Γm n}{tms : Tms Γ n tmsm} ->
            tms [ id ]ts ≡ transport (Tms Γ n) (sym M.[id]ts) tms
        εs : 
            {Γm : M.Con}{Γ : Con Γm} ->
            Tms Γ zero M.εs
        ◆sη : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {tsm : M.Tms Γm zero}{ts : Tms Γ zero tsm} ->
            ts ≡ transport (Tms Γ zero) (sym (M.◆sη tsm)) εs
        _,s_ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {n : ℕ}{tmsm : M.Tms Γm n}{tm : M.Tm Γm} ->
            Tms Γ n tmsm -> Tm Γ tm -> Tms Γ (suc n) (tmsm M.,s tm)
        π₁ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {n : ℕ}{tmsm : M.Tms Γm (suc n)} ->
            Tms Γ (suc n) tmsm -> Tms Γ n (M.π₁ tmsm)
        π₂ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {n : ℕ}{tmsm : M.Tms Γm (suc n)} ->
            Tms Γ (suc n) tmsm -> Tm Γ (M.π₂ tmsm)
        ▸sβ₁ : 
            {Γm : M.Con}{Γ : Con Γm} -> 
            {n : ℕ}{tmsm : M.Tms Γm n}{tm : M.Tm Γm} ->
            {ts : Tms Γ n tmsm}{t : Tm Γ tm} ->
            π₁ (ts ,s t) ≡ transport (Tms Γ n) (sym M.▸sβ₁) ts
        ▸sβ₂ : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {n : ℕ}{tmsm : M.Tms Γm n}{tm : M.Tm Γm} ->
            {ts : Tms Γ n tmsm}{t : Tm Γ tm} ->
            π₂ (ts ,s t) ≡ transport (Tm Γ) (sym M.▸sβ₂) t
        ▸sη : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {n : ℕ}{tmsm : M.Tms Γm (suc n)} ->
            {ts : Tms Γ (suc n) tmsm} ->
            π₁ ts ,s  π₂ ts ≡ transport (Tms Γ (suc n)) (sym M.▸sη) ts
        ,[] : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {n : ℕ}{tmsm : M.Tms Γm n}{ts : Tms Γ n tmsm} ->
            {tm : M.Tm Γm}{t : Tm Γ tm} ->
            (ts ,s t) [ γ ]ts ≡ transport (Tms Δ (suc n)) (sym M.,[]) ((ts [ γ ]ts) ,s (t [ γ ]t))
        
        fun : 
            {Γm : M.Con}{Γ : Con Γm} ->
            (n : ℕ) -> (a : funar n) -> {tmsm : M.Tms Γm n} -> Tms Γ n tmsm -> Tm Γ (M.fun n a tmsm)
        fun[] : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {n : ℕ}{a : funar n} ->
            {tmsm : M.Tms Γm n}{ts : Tms Γ n tmsm} ->
            (fun n a ts) [ γ ]t ≡ transport (Tm Δ) (sym M.fun[]) (fun n a (ts [ γ ]ts))
        rel : 
            {Γm : M.Con}{Γ : Con Γm} ->
            (n : ℕ) -> (a : relar n) -> {tmsm : M.Tms Γm n} -> Tms Γ n tmsm -> For Γ (M.rel n a tmsm)
        rel[] : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {n : ℕ}{a : relar n} ->
            {tmsm : M.Tms Γm n}{ts : Tms Γ n tmsm} ->
            (rel n a ts) [ γ ]F ≡ transport (For Δ) (sym M.rel[]) (rel n a (ts [ γ ]ts))
        ∀' : 
            {Γm : M.Con}{Γ : Con Γm}{Am : M.For (Γm M.▸t)} ->
            For (Γ ▸t) Am -> For Γ (M.∀' Am)
        ∀[] : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {Am : M.For (Γm M.▸t)}{A : For (Γ ▸t) Am} ->
            (∀' A) [ γ ]F  ≡ transport (For Δ) (sym M.∀[]) (∀' (A [ (γ ∘ pt) ,t qt ]F))
        ∀intro : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {Am : M.For (Γm M.▸t)}{A : For (Γ ▸t) Am}{pfa : M.Pf (Γm M.▸t) Am} ->
            Pf (Γ ▸t) A pfa -> Pf Γ (∀' A) (M.∀intro pfa)
        ∀elim : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {Am : M.For (Γm M.▸t)}{A : For (Γ ▸t) Am}{pfa : M.Pf Γm (M.∀' Am)} ->
            Pf Γ (∀' A) pfa -> Pf (Γ ▸t) A (M.∀elim pfa)
        
        ∃' : 
            {Γm : M.Con}{Γ : Con Γm}{Am : M.For (Γm M.▸t)} ->
            For (Γ ▸t) Am -> For Γ (M.∃' Am)
        ∃[] : 
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {Am : M.For (Γm M.▸t)}{A : For (Γ ▸t) Am} ->
            (∃' A) [ γ ]F  ≡ transport (For Δ) (sym M.∃[]) (∃' (A [ (γ ∘ pt) ,t qt ]F))
        ∃intro : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {Am : M.For (Γm M.▸t)}{tm : M.Tm Γm}{A : For (Γ ▸t) Am}{pfa : M.Pf Γm (Am M.[ M.id M.,t tm ]F)} ->
            (t : Tm Γ tm) -> Pf Γ (A [ id ,t t ]F) pfa -> Pf Γ (∃' A) (M.∃intro tm pfa)
        ∃elim :
            {Γm : M.Con}{Γ : Con Γm} ->
            {Am : M.For (Γm M.▸t)}{A : For (Γ ▸t) Am} ->
            {Bm : M.For Γm}{B : For Γ Bm} ->
            {pfa : M.Pf Γm (M.∃' Am)}{pfab : M.Pf ((Γm M.▸t) M.▸p Am) (Bm M.[ M.pt M.∘ M.pp ]F)} ->
            Pf Γ (∃' A) pfa -> Pf ((Γ ▸t) ▸p A) (B [ pt ∘ pp ]F) pfab -> Pf Γ B (M.∃elim pfa pfab)
        
        Eq :
            {Γm : M.Con}{Γ : Con Γm} ->
            {tm tm' : M.Tm Γm} -> 
            Tm Γ tm -> Tm Γ tm' -> For Γ (M.Eq tm tm')
        Eq[] :
            {Γm Δm : M.Con}{Γ : Con Γm}{Δ : Con Δm} ->
            {γm : M.Sub Δm Γm}{γ : Sub Δ Γ γm} ->
            {tm tm' : M.Tm Γm}{t : Tm Γ tm}{t' : Tm Γ tm'} -> 
            (Eq t t') [ γ ]F ≡ transport (For Δ) (sym M.Eq[]) (Eq (t [ γ ]t) (t' [ γ ]t))  
        Eqrefl :
            {Γm : M.Con}{Γ : Con Γm} ->
            {tm : M.Tm Γm}{t : Tm Γ tm} -> 
            Pf Γ (Eq t t) M.Eqrefl
        subst' : 
            {Γm : M.Con}{Γ : Con Γm} ->
            {tm tm' : M.Tm Γm}{t : Tm Γ tm}{t' : Tm Γ tm'} ->
            {Am : M.For (Γm M.▸t)}{pfeq : M.Pf Γm (M.Eq tm tm')}{pfa : M.Pf Γm (Am M.[ M.id M.,t tm ]F)} ->
            (A : For (Γ ▸t) Am) -> Pf Γ (Eq t t') (pfeq) -> Pf Γ (A [ id ,t t ]F) pfa -> Pf Γ (A [ id ,t t' ]F) (M.subst' Am pfeq pfa)
-}      