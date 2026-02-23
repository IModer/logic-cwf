{-# OPTIONS --prop #-}

open import lib
open import FirstOrderLogic.IntFullSplit.Model

module FirstOrderLogic.IntFullSplit.KripkeModel
    (funar : ℕ → Set)
    (relar : ℕ → Set)
    where

record Category : Set₁ where
    field
        Ob   : Set
        Hom  : Ob -> Ob -> Set
        idC  : ∀{A} -> Hom A A
        -- A --> B --> C
        --    f     g
        -- A --------> C
        --     g ∘ f
        _∘C_ : ∀{A B C} -> Hom B C -> Hom A B -> Hom A C
        assC : ∀{A B C D}{f : Hom C D}{g : Hom B C}{h : Hom A B} -> (f ∘C g) ∘C h ≡ f ∘C (g ∘C h)
        idlC : ∀{A B}{f : Hom A B} -> idC ∘C f ≡ f
        idrC : ∀{A B}{f : Hom A B} -> f ∘C idC ≡ f

module Kripke
    (C : Category)
    (D : Set)
    where

    open Category C

    record Cont : Set₁ where
        constructor mk
        field
            A    : Ob -> Set
            _⟨_⟩ : ∀{I J} -> A I -> Hom J I -> A J
            ⟨id⟩ : ∀{I}{a : A I} -> a ⟨ idC ⟩ ≡ a
            ⟨∘⟩  : ∀{I J K}{a : A I}{g : Hom K J}{f : Hom J I} -> a ⟨ f ∘C g ⟩ ≡ (a ⟨ f ⟩) ⟨ g ⟩
    open Cont public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩; ⟨id⟩ to _∶⟨id⟩; ⟨∘⟩ to _∶⟨∘⟩)

    record Subt(Δ Γ : Cont) : Set where
        constructor mk
        field
            α   : ∀{I} -> ∣ Δ ∣ I -> ∣ Γ ∣ I
            nat : ∀{I J : Ob}{a : ∣ Δ ∣ I}{f : Hom J I} -> (Γ ∶ (α a) ⟨ f ⟩) ≡ α (Δ ∶ a ⟨ f ⟩)
    open Subt public renaming (α to ∣_∣)
    {-
    -}
    _∘t_ : {Γ Δ Θ : Cont} → Subt Δ Γ → Subt Θ Δ → Subt Θ Γ
    ∣ γ ∘t δ ∣ θi = ∣ γ ∣ (∣ δ ∣ θi)
    nat (γ ∘t δ)  = trans (nat γ) (cong ∣ γ ∣ (δ .nat))

    idt : {Γ : Cont} → Subt Γ Γ
    ∣ idt ∣ = λ z → z
    nat idt = refl

    ◆t : Cont 
    ∣ ◆t ∣       = λ x → 𝟙
    ◆t ∶ a ⟨ f ⟩ = *
    ◆t ∶⟨id⟩     = refl
    ◆t ∶⟨∘⟩      = refl

    εt : {Γ : Cont} → Subt Γ ◆t
    ∣ εt ∣ = λ x → *
    nat εt = refl

    record For(Γ : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> A I i -> (f : Hom J I) -> A J (Γ ∶ i ⟨ f ⟩)
    open For public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)

    mkForEq : ∀{Γ : Cont}{A B : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop } -> (A ≡ B) ->
        {sub₁ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> A I i -> (f : Hom J I) -> A J (Γ ∶ i ⟨ f ⟩)} ->
        {sub₂ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> B I i -> (f : Hom J I) -> B J (Γ ∶ i ⟨ f ⟩)} ->
        _≡_ {A = For Γ} (mk A sub₁)(mk B sub₂)
    mkForEq refl = refl

    _[_]F : ∀{Γ Δ} -> For Γ -> Subt Δ Γ -> For Δ
    ∣ A [ γt ]F ∣ I x = ∣ A ∣ I (∣ γt ∣ x)
    _∶_⟨_⟩ (A [ γt ]F) {I} {J} {i} x f = substp (∣ A ∣ J) (nat γt) (A ∶ x ⟨ f ⟩)

    DPSh : Cont
    ∣ DPSh ∣ x     = D
    DPSh ∶ d ⟨ f ⟩ = d
    DPSh ∶⟨id⟩     = refl
    DPSh ∶⟨∘⟩      = refl

    Tm : Cont -> Set
    Tm Γ = Subt Γ DPSh

    _[_]t : {Γ : Cont} → Tm Γ → {Δ : Cont} → Subt Δ Γ → Tm Δ
    ∣ t [ γt ]t ∣ x = ∣ t ∣ (∣ γt ∣ x)
    nat (t [ γt ]t) = trans (nat t) (cong ∣ t ∣ (nat γt))

    _▸t : Cont → Cont
    ∣ Γ ▸t ∣ I = ∣ Γ ∣ I × D
    (Γ ▸t) ∶ (i ,Σ d) ⟨ f ⟩ = (Γ ∶ i ⟨ f ⟩) ,Σ d
    (Γ ▸t) ∶⟨id⟩ = mk,= (Γ ∶⟨id⟩) refl
    (Γ ▸t) ∶⟨∘⟩ = mk,= (Γ ∶⟨∘⟩) refl

    _,t_ : {Γ Δ : Cont} → Subt Δ Γ → Tm Δ → Subt Δ (Γ ▸t)
    ∣ γt ,t t ∣ x = (∣ γt ∣ x) ,Σ (∣ t ∣ x)
    nat (γt ,t t) = mk,= (nat γt) (nat t)

    pt : {Γ : Cont} → Subt (Γ ▸t) Γ
    ∣ pt ∣ x = proj₁ x
    nat pt   = refl

    qt : {Γ : Cont} → Tm (Γ ▸t)
    ∣ qt ∣ x = proj₂ x
    nat qt   = refl

    record Conp(Γt : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γt ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γt ∣ I} -> A I i -> (f : Hom J I) -> A J (Γt ∶ i ⟨ f ⟩)
    open Conp public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)
    
    _[_]C : ∀{Γt Δt} -> Conp Γt -> Subt Δt Γt -> Conp Δt
    ∣ Γ [ γt ]C ∣ I x = ∣ Γ ∣ I (∣ γt ∣ x)
    _∶_⟨_⟩ (Γ [ γt ]C) {I} {J} x f = substp (∣ Γ ∣ J) (γt .nat) (Γ ∶ x ⟨ f ⟩)
    
    record Subp{Γt : Cont}(Δ Γ : Conp Γt) : Prop where
        constructor mk
        field
            α   : ∀{I i} -> ∣ Δ ∣ I i -> ∣ Γ ∣ I i
    open Subp public renaming (α to ∣_∣)

    _∘p_ : {Γt : Cont} {Γ Δ Θ : Conp Γt} -> Subp Δ Γ -> Subp Θ Δ -> Subp Θ Γ
    ∣ γ ∘p δ ∣ θi = ∣ γ ∣ (∣ δ ∣ θi)

    idp : {Γt : Cont} {Γ : Conp Γt} → Subp Γ Γ
    ∣ idp ∣ γi = γi

    ◆p : {Γt : Cont} → Conp Γt
    ∣ ◆p ∣ I γi  = 𝟙p
    ◆p ∶ x ⟨ f ⟩ = *

    εp : {Γt : Cont} {Γ : Conp Γt} → Subp Γ ◆p
    ∣ εp ∣ x = *

    record Pf{Γt : Cont}(Γ : Conp Γt)(K : For Γt) : Prop where
        constructor mk
        field
            α : ∀{I i} -> ∣ Γ ∣ I i -> ∣ K ∣ I i
    open Pf public renaming (α to ∣_∣)

    _[_]P : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} →
      Pf Γ K → {Δ : Conp Γt} → Subp Δ Γ → Pf Δ K
    ∣ PfK [ γ ]P ∣ Δi = ∣ PfK ∣ (∣ γ ∣ Δi)

    _[_]p : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} →
      Pf Γ K → {Δt : Cont} (γt : Subt Δt Γt) → Pf (Γ [ γt ]C) (K [ γt ]F)
    ∣ PfK [ γt ]p ∣ Γi = ∣ PfK ∣ Γi

    _▸p_ : {Γt : Cont} → Conp Γt → For Γt → Conp Γt
    ∣ Γ ▸p K ∣ I Γi    = ∣ Γ ∣ I Γi ×p ∣ K ∣ I Γi
    (Γ ▸p K) ∶ (Γi ,Σ Ki) ⟨ f ⟩ = (Γ ∶ Γi ⟨ f ⟩) ,Σ (K ∶ Ki ⟨ f ⟩)

    _,p_ : {Γt : Cont} {Γ Δ : Conp Γt} →
      Subp Δ Γ → {K : For Γt} → Pf Δ K → Subp Δ (Γ ▸p K)
    ∣ γ ,p PfK ∣ Δi = (∣ γ ∣ Δi) ,Σ ∣ PfK ∣ Δi

    pp : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} → Subp (Γ ▸p K) Γ
    ∣ pp ∣ x = proj₁ x

    qp : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} → Pf (Γ ▸p K) K
    ∣ qp ∣ x = proj₂ x

    ⊥ : {Γt : Cont} → For Γt
    ∣ ⊥ ∣ I x = 𝟘p
    ⊥ ∶ x ⟨ f ⟩ = x

    ⊤ : {Γt : Cont} → For Γt
    ∣ ⊤ ∣ I x = 𝟙p
    ⊤ ∶ x ⟨ f ⟩ = *

    exfalso : {Γt : Cont} {K : For Γt} {Γ : Conp Γt} → Pf Γ ⊥ → Pf Γ K
    ∣ exfalso x ∣ Γi = ind𝟘p (∣ x ∣ Γi)

    tt : {Γt : Cont} {Γ : Conp Γt} → Pf Γ ⊤
    ∣ tt ∣ = λ _ → *

    _⊃_ : {Γt : Cont} → For Γt → For Γt → For Γt
    ∣ _⊃_ {Γt} K L ∣ I x = (J : Ob) -> (f : Hom J I) -> ∣ K ∣ J (Γt ∶ x ⟨ f ⟩) -> ∣ L ∣ J (Γt ∶ x ⟨ f ⟩)
    (_∶_⟨_⟩ (_⊃_ {Γt} K L) {I}{J}{i}) = λ x f J' g Ki → substp (∣ L ∣ J') (Γt ∶⟨∘⟩) (x J' (f ∘C g) (substp (∣ K ∣ J') (sym (Γt ∶⟨∘⟩)) Ki))
    
    []⊃ : {Γt : Cont} {K L : For Γt} {Δt : Cont} {γt : Subt Δt Γt} →
      ((K ⊃ L) [ γt ]F) ≡ ((K [ γt ]F) ⊃ (L [ γt ]F))
    []⊃ {Γt} {K} {L} {Δt} {γt} = mkForEq {Δt} {∣ (K ⊃ L) [ γt ]F ∣} {∣ (K [ γt ]F) ⊃ (L [ γt ]F) ∣}
        (funext (λ I → funext (λ Δi → {!   !})))
      -- cong (λ Z -> (J : Ob) -> (f : Hom J I) -> Z J f)
      -- ∣ K ∣ J (Γt ∶ ∣ γt ∣ Δi ⟨ f ⟩)   -> ∣ L ∣ J (Γt ∶ ∣ γt ∣ Δi ⟨ f ⟩)
      -- cong (...) nat γt
      -- ∣ K ∣ J (∣ γt ∣ (Δt ∶ Δi ⟨ f ⟩)) -> ∣ L ∣ J (Γt ∶ ∣ γt ∣ Δi ⟨ f ⟩)
      -- cong (...) nat γt
      -- ∣ K ∣ J (∣ γt ∣ (Δt ∶ Δi ⟨ f ⟩)) -> ∣ L ∣ J (∣ γt ∣ (Δt ∶ Δi ⟨ f ⟩))

    ⊃intro : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf (Γ ▸p K) L → Pf Γ (K ⊃ L)
    ∣ ⊃intro {Γt}{K}{L}{Γ} PfKL ∣ Γi J f Kj = ∣ PfKL ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ Kj)

    ⊃elim : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf Γ (K ⊃ L) → Pf (Γ ▸p K) L
    ∣ ⊃elim {Γt}{K}{L}{Γ} PfKL ∣ {I}{i} (Γi ,Σ Ki) = substp (∣ L ∣ I) (Γt ∶⟨id⟩) (∣ PfKL ∣ Γi I idC (substp (∣ K ∣ I) (sym (Γt ∶⟨id⟩)) Ki))
    {-
    -}

    _∧_ : {Γt : Cont} → For Γt → For Γt → For Γt
    ∣ K ∧ L ∣ I Γi    = ∣ K ∣ I Γi ×p ∣ L ∣ I Γi
    (K ∧ L) ∶ x ⟨ f ⟩ = (K ∶ x .proj₁ ⟨ f ⟩) ,Σ (L ∶ x .proj₂ ⟨ f ⟩)

    ∧intro : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
    ∣ ∧intro PfK PfL ∣ Γi = (∣ PfK ∣ Γi) ,Σ (∣ PfL ∣ Γi)

    ∧elim₁ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} → Pf Γ (K ∧ L) -> Pf Γ K
    ∣ ∧elim₁ x ∣ Γi = proj₁ (∣ x ∣ Γi)

    ∧elim₂ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} → Pf Γ (K ∧ L) -> Pf Γ L
    ∣ ∧elim₂ x ∣ Γi = proj₂ (∣ x ∣ Γi)

    _∨_ : {Γt : Cont} → For Γt → For Γt → For Γt
    ∣ K ∨ L ∣ I Γi    = ∣ K ∣ I Γi +p ∣ L ∣ I Γi
    (K ∨ L) ∶ inj₁ x ⟨ f ⟩ = inj₁ (K ∶ x ⟨ f ⟩)
    (K ∨ L) ∶ inj₂ x ⟨ f ⟩ = inj₂ (L ∶ x ⟨ f ⟩)

    ∨intro₁ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf Γ K → Pf Γ (K ∨ L)
    ∣ ∨intro₁ PfK ∣ Γi = inj₁ (∣ PfK ∣ Γi)  

    ∨intro₂ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf Γ L → Pf Γ (K ∨ L)
    ∣ ∨intro₂ PfL ∣ Γi = inj₂ (∣ PfL ∣ Γi)

    ∨elim : ∀{Γt}{K L C}{Γ : Conp Γt} → Pf (Γ ▸p K) C → Pf (Γ ▸p L) C → Pf Γ (K ∨ L) → Pf Γ C
    ∣ ∨elim {C = C} PfKC PfLC PfK∨L ∣ {I} {i} Γi = 
        ind+p 
        (λ _ → ∣ C ∣ I i) 
        (λ Ki -> ∣ PfKC ∣ (Γi ,Σ Ki)) 
        (λ Li -> ∣ PfLC ∣ (Γi ,Σ Li)) 
        (∣ PfK∨L ∣ Γi)

    ∀' : {Γt : Cont} → For (Γt ▸t) → For Γt
    ∣ ∀' K ∣ I Γi = ∀(d : D) -> ∣ K ∣ I (Γi ,Σ d)
    ∀' K ∶ x ⟨ f ⟩ = λ d → K ∶ x d ⟨ f ⟩

    ∀intro : {Γt : Cont} {K : For ((Γt ▸t) ▸t)} {Γ : Conp (Γt ▸t)} →
      Pf (Γ [ pt ]C) K → Pf Γ (∀' K)
    ∣ ∀intro PfK ∣ Γi d = ∣ PfK ∣ Γi

    ∀elim : {Γt : Cont} {K : For ((Γt ▸t) ▸t)} {Γ : Conp (Γt ▸t)} →
      Pf Γ (∀' K) → Pf (Γ [ pt ]C) K
    ∣ ∀elim PfK ∣ {I} {(Γti ,Σ d) ,Σ d'} Γi = ∣ PfK ∣ Γi d'

    ∃' : {Γt : Cont} → For (Γt ▸t) → For Γt
    ∣ ∃' {Γt} K ∣ I Γi = ∃ D λ d -> ∣ K ∣ I (Γi ,Σ d)
    ∃' K ∶ d ,∃ x ⟨ f ⟩ = d ,∃ (K ∶ x ⟨ f ⟩)

    ∃intro : {Γt : Cont} {K : For (Γt ▸t)} (t : Tm Γt) {Γ : Conp Γt} →
      Pf Γ (K [ idt ,t t ]F) → Pf Γ (∃' K)
    ∣ ∃intro {Γt}{K} t {Γ} PfK ∣ {I}{i} Γi = (∣ t ∣ i) ,∃ (∣ PfK ∣ Γi)

    ∃elim : {Γt : Cont} {K : For (Γt ▸t)} {Γp : Conp Γt}{L : For Γt} ->
      Pf Γp (∃' K) → Pf ((Γp [ pt ]C) ▸p (K [ _,t_ {Γt} pt (qt {Γt}) ]F)) (L [ pt ]F) → Pf Γp L
    ∣ ∃elim {Γt}{K}{Γp}{L} Pf∃K PfKL ∣ {I} {i} Γi = 
        with∃ (∣ Pf∃K ∣ Γi) 
        λ d Ki → ∣ PfKL ∣ (Γi ,Σ Ki) 

    Eq : {Γt : Cont} → Tm Γt → Tm Γt → For Γt
    ∣ Eq t t' ∣ I Γi = ∣ t ∣ Γi ≡ ∣ t' ∣ Γi
    _∶_⟨_⟩ (Eq {Γt} t t') {I} {J} {i} x f = trans (sym (nat t)) (trans x (nat t'))

    Eq[] : {Γt Δt : Cont} {γt : Subt Δt Γt} {t t' : Tm Γt} →
      (Eq t t' [ γt ]F) ≡ Eq (t [ γt ]t) (t' [ γt ]t)
    Eq[] = refl
    
    Eqrefl : {Γt : Cont} {t : Tm Γt} {Γ : Conp Γt} → Pf Γ (Eq t t)
    ∣ Eqrefl ∣ = λ x → refl

    subst' : {Γt : Cont} (K : For (Γt ▸t)) {t t' : Tm Γt} {Γ : Conp Γt} →
      Pf Γ (Eq t t') → Pf Γ (K [ idt ,t t ]F) → Pf Γ (K [ idt ,t t' ]F)
    ∣ subst' K t=t' PfK ∣ {I}{i} x = {!   !} -- substp (λ z -> ∣ K ∣ I (i ,Σ ∣ z ∣ i)) (∣ t=t' ∣ x) (∣ PfK ∣ x)

    Kripke : Model funar relar _ _ _ _ _
    Kripke = record
      { Cont = Cont
      ; Subt = Subt
      ; _∘t_ = _∘t_
      ; idt = idt
      ; asst = refl
      ; idlt = refl
      ; idrt = refl
      ; ◆t = ◆t
      ; εt = εt
      ; ◆tη = λ σ → refl
      ; For = For
      ; _[_]F = _[_]F
      ; [∘]F = refl
      ; [id]F = refl
      ; Tm = Tm
      ; _[_]t = _[_]t
      ; [∘]t = refl
      ; [id]t = refl
      ; _▸t = _▸t
      ; _,t_ = _,t_
      ; pt = pt
      ; qt = λ {Γt} -> qt {Γt}
      ; ▸tβ₁ = refl
      ; ▸tβ₂ = refl
      ; ▸tη = refl
      ; Tms = {!   !}
      ; _[_]ts = {!   !}
      ; [∘]ts = {!   !}
      ; [id]ts = {!   !}
      ; εs = {!   !}
      ; ◆sη = {!   !}
      ; _,s_ = {!   !}
      ; π₁ = {!   !}
      ; π₂ = {!   !}
      ; ▸sβ₁ = {!   !}
      ; ▸sβ₂ = {!   !}
      ; ▸sη = {!   !}
      ; ,[] = {!   !}
      ; fun = {!   !}
      ; fun[] = {!   !}
      ; rel = {!   !}
      ; rel[] = {!   !}
      ; Conp = Conp
      ; _[_]C = _[_]C
      ; [id]C = refl
      ; [∘]C = refl
      ; Subp = Subp
      ; _∘p_ = _∘p_
      ; idp = idp
      ; ◆p = ◆p
      ; εp = εp
      ; Pf = Pf
      ; _[_]P = _[_]P
      ; _[_]p = _[_]p
      ; _▸p_ = _▸p_
      ; _,p_ = _,p_
      ; pp = λ {Γt}{Γ}{K = K} -> pp {K = K} 
      ; qp = λ {Γt}{Γ}{K} -> qp {Γ = Γ}
      ; ⊥ = ⊥
      ; ⊥[] = refl
      ; exfalso = exfalso
      ; ⊤ = ⊤
      ; ⊤[] = refl
      ; tt = tt
      ; _⊃_ = _⊃_
      ; ⊃[] = {!   !}
      {-
      ; ⊃intro = λ{Γt}{K}{L}{Γ} -> ⊃intro {Γt}{K}{L}{Γ}
      ; ⊃elim = λ{Γt}{K}{L}{Γ} -> ⊃elim {Γt}{K}{L}{Γ}
      -}
      ; _∧_ = _∧_
      ; ∧[] = refl
      ; ∧intro = ∧intro
      ; ∧elim₁ = λ {Γt}{K}{L} -> ∧elim₁ {L = L}
      ; ∧elim₂ = λ {Γt}{K}{L} -> ∧elim₂ {K = K} 
      ; _∨_ = _∨_
      ; ∨[] = refl
      ; ∨elim = λ {Γt}{K}{L}{C} -> ∨elim {Γt}{K}{L}{C}
      ; ∨intro₁ = λ {Γt}{K}{L} -> ∨intro₁ {Γt}{K}{L}
      ; ∨intro₂ = λ {Γt}{K}{L} -> ∨intro₂ {Γt}{K}{L}
      ; ∀' = ∀'
      ; ∀[] = refl
      ; ∀intro = λ {Γt}{K}{Γ} -> ∀intro {Γt}{K}{Γ} 
      ; ∀elim = λ {Γt}{K}{Γ} -> ∀elim {Γt}{K}{Γ}
      ; ∃' = ∃'
      ; ∃[] = refl
      ; ∃intro = λ {Γt}{K} -> ∃intro {Γt}{K}
      ; ∃elim = λ {Γt}{K}{Γp}{L} -> ∃elim {Γt}{K}{Γp}{L} 
      ; Eq = Eq
      ; Eq[] = {!   !}
      ; Eqrefl = Eqrefl
      ; subst' = subst'
      }    