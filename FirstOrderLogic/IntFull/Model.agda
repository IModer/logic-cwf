{-# OPTIONS --prop #-}

open import lib

module FirstOrderLogic.IntFull.Model
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
    ▸pη   : ∀{Γ K} -> id ≡ (pp ,p qp) ∈ Sub (Γ ▸p K) (Γ ▸p K)
    -- ∀{Γ Δ K}{γp : Sub Δ (Γ ▸p K)}  → (pp ∘ γp) ,p substp (λ K → Pf Δ K) (sym [∘]F) (qp [ γp ]p) ≡ γp
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
    ▸tη   : ∀{Γ} → id ≡ (pt ,t qt) ∈ (Sub (Γ ▸t) (Γ ▸t))
    
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

    -- function and relation symbols (fun : (n : ℕ) → funar n → Tms n → Tm, rel : (n : ℕ) → relar n → Tms n → For)
    -- kell helyettesítési szabály
    --fun  : ∀{Γ}(n : ℕ) → funar n → (Tm Γ) ^ n → Tm Γ
    --fun[] : ∀{Γ n a ts Δ}{γ : Sub Δ Γ} → fun n a ts [ γ ]t ≡ fun n a (ind^ {C = ((Tm Δ) ^_)} (λ _ → *) (λ _ t ts → t [ γ ]t ,Σ ts) ts)
    --rel  : ∀{Γ}(n : ℕ) → relar n → (Tm Γ) ^ n → For Γ
    --rel[] : ∀{Γ n a ts Δ}{γ : Sub Δ Γ} → (rel n a ts) [ γ ]F ≡ rel n a (ind^ {C = ((Tm Δ) ^_)} (λ _ → *) (λ _ t ts → t [ γ ]t ,Σ ts) ts)

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

  -- ,∘ : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm Δ}{Θ}{δ : Sub Θ Δ} → (γ ,t t) ∘ δ ≡ γ ∘ δ ,t t [ δ ]t
  -- ,∘ {Γ}{Δ}{γ}{t}{Θ}{δ} = trans (sym ▸tη) (cong (λ z → proj₁ z ,t proj₂ z) (mk,= (trans (sym ass) (cong (_∘ δ) ▸tβ₁)) (trans [∘]t (cong (_[ δ ]t) ▸tβ₂))))
  
  -- ▸tη' : ∀{Γ} → id {Γ ▸t} ≡ pt ,t qt
  -- ▸tη' {Γ} = trans (sym ▸tη) (cong (λ z → proj₁ z ,t proj₂ z) (mk,= idr [id]t))

  _$_ : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf Γ K → Pf Γ L
  _$_ {Γ}{K}{L} m k = substp (Pf Γ) (trans (sym [∘]F) (trans (cong (L [_]F) ▸pβ₁) [id]F)) (⊃elim m [ id ,p substp (Pf Γ) (sym [id]F) k ]p)

  un∀' : ∀{Γ K} → Pf Γ (∀' K) → (t : Tm Γ) → Pf Γ (K [ id ,t t ]F)
  un∀' {Γ}{K} k t = (∀elim k) [ id ,t t ]p

  pp⁺ : ∀{Γ Δ}{K} → (γ : Sub Γ Δ) → Sub (Γ ▸p K [ γ ]F) (Δ ▸p K)
  pp⁺ {Γ}{Δ}{K} γ = (γ ∘ pp) ,p substp (Pf (Γ ▸p K [ γ ]F)) (sym [∘]F) qp

  pt⁺ : ∀{Γ Δ} → (γ : Sub Γ Δ) → Sub (Γ ▸t) (Δ ▸t)
  pt⁺ γ = (γ ∘ pt) ,t qt

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
        ε   : {Γm : M.Con}{Γ : Con Γm} -> Sub Γ ◆ M.ε
        ◆η  : {Γm : M.Con}{Γ : Con Γm}{σm : M.Sub Γm M.◆} -> (σ : Sub Γ ◆ σm) -> σ ≡ transport (Sub Γ ◆) (sym (M.◆η σm)) ε

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