{-# OPTIONS --prop #-}

open import lib
open import FirstOrderLogic.IntNegative.Model

module FirstOrderLogic.IntNegative.KripkeModel
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

module Semantics
    (C : Category)
    (open Category C)
    (D : Ob -> Set)
    (D∶_⟨_⟩ : ∀{I J} -> D I -> Hom J I -> D J)
    (D∶⟨∘⟩  : ∀{I J K}{a : D I}{f : Hom J I}{g : Hom K J} -> D∶ a ⟨ f ∘C g ⟩ ≡ D∶ D∶ a ⟨ f ⟩ ⟨ g ⟩)
    (D∶⟨id⟩ : ∀{I}{a : D I} -> D∶ a ⟨ idC ⟩ ≡ a)
    (rel  : (n : ℕ) → relar n → (I : Ob) -> (D I) ^ n -> Prop)
    (⟨rel⟩ : ∀{n i I J ds} → rel n i I ds → (f : Hom J I) → rel n i J (map^ ds (D∶_⟨ f ⟩)))
    (fun  : (n : ℕ) → funar n → (I : Ob) -> (D I) ^ n → (D I))
    (⟨fun⟩ : ∀(n : ℕ)(a : funar n)(I J : Ob)(ds : (D I) ^ n)(f : Hom J I) -> (D∶ (fun n a I ds) ⟨ f ⟩) ≡ (fun n a J (map^ ds (D∶_⟨ f ⟩))) )
    where

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
            α   : ∀(I : Ob) -> ∣ Δ ∣ I -> ∣ Γ ∣ I
            nat : ∀{I J : Ob}{a : ∣ Δ ∣ I}{f : Hom J I} -> (Γ ∶ (α I a) ⟨ f ⟩) ≡ α J (Δ ∶ a ⟨ f ⟩)
    open Subt public renaming (α to ∣_∣)
    
    mkSubtEq : ∀{Δ Γ} -> {α β : ∀(I : Ob) -> ∣ Δ ∣ I -> ∣ Γ ∣ I} -> 
      {nat₁ : ∀{I J : Ob}{a : ∣ Δ ∣ I}{f : Hom J I} -> (Γ ∶ (α I a) ⟨ f ⟩) ≡ α J (Δ ∶ a ⟨ f ⟩)} ->
      {nat₂ : ∀{I J : Ob}{a : ∣ Δ ∣ I}{f : Hom J I} -> (Γ ∶ (β I a) ⟨ f ⟩) ≡ β J (Δ ∶ a ⟨ f ⟩)} ->
      (α ≡ β) ->
      _≡_ {A = Subt Δ Γ} (mk α nat₁) (mk β nat₂)
    mkSubtEq refl = refl

    _∘t_ : {Γ Δ Θ : Cont} → Subt Δ Γ → Subt Θ Δ → Subt Θ Γ
    ∣ γ ∘t δ ∣ I θi = ∣ γ ∣ I (∣ δ ∣ I θi)
    nat (γ ∘t δ) {I}{J}  = trans (nat γ) (cong (∣ γ ∣ J) (nat δ))

    idt : {Γ : Cont} → Subt Γ Γ
    ∣ idt ∣ = λ I z → z
    nat idt = refl

    ◆t : Cont 
    ∣ ◆t ∣       = λ x → 𝟙
    ◆t ∶ a ⟨ f ⟩ = *
    ◆t ∶⟨id⟩     = refl
    ◆t ∶⟨∘⟩      = refl

    εt : {Γ : Cont} → Subt Γ ◆t
    ∣ εt ∣ = λ I x → *
    nat εt = refl

    record For(Γ : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> A I i -> (f : Hom J I) -> A J (Γ ∶ i ⟨ f ⟩)
    open For public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)

    mkForEq : ∀{Γ : Cont}{A B : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop } ->
        {sub₁ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> A I i -> (f : Hom J I) -> A J (Γ ∶ i ⟨ f ⟩)} ->
        {sub₂ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> B I i -> (f : Hom J I) -> B J (Γ ∶ i ⟨ f ⟩)} ->
        (A ≡ B) -> 
        _≡_ {A = For Γ} (mk A sub₁)(mk B sub₂)
    mkForEq refl = refl

    _[_]F : ∀{Γ Δ} -> For Γ -> Subt Δ Γ -> For Δ
    ∣ A [ γt ]F ∣ I x = ∣ A ∣ I (∣ γt ∣ I x)
    _∶_⟨_⟩ (A [ γt ]F) {I} {J} {i} x f = substp (∣ A ∣ J) (nat γt) (A ∶ x ⟨ f ⟩)

    DPSh : Cont
    ∣ DPSh ∣ I     = D I
    DPSh ∶ d ⟨ f ⟩ = D∶ d ⟨ f ⟩
    DPSh ∶⟨∘⟩      = D∶⟨∘⟩
    DPSh ∶⟨id⟩     = D∶⟨id⟩

    Tm : Cont -> Set
    Tm Γ = Subt Γ DPSh

    _[_]t : {Γ : Cont} → Tm Γ → {Δ : Cont} → Subt Δ Γ → Tm Δ
    ∣ t [ γt ]t ∣ I x = ∣ t ∣ I (∣ γt ∣ I x)
    nat (t [ γt ]t) {I}{J} = trans (nat t) (cong (∣ t ∣ J) (nat γt))

    _▸t : Cont → Cont
    ∣ Γ ▸t ∣ I = ∣ Γ ∣ I × D I
    (Γ ▸t) ∶ (i ,Σ d) ⟨ f ⟩ = (Γ ∶ i ⟨ f ⟩) ,Σ (D∶ d ⟨ f ⟩)
    (Γ ▸t) ∶⟨id⟩ = mk,= (Γ ∶⟨id⟩) D∶⟨id⟩
    (Γ ▸t) ∶⟨∘⟩ = mk,= (Γ ∶⟨∘⟩) D∶⟨∘⟩

    _,t_ : {Γ Δ : Cont} → Subt Δ Γ → Tm Δ → Subt Δ (Γ ▸t)
    ∣ γt ,t t ∣ I x = (∣ γt ∣ I x) ,Σ (∣ t ∣ I x)
    nat (γt ,t t) = mk,= (nat γt) (nat t)

    pt : {Γ : Cont} → Subt (Γ ▸t) Γ
    ∣ pt ∣ I x = proj₁ x
    nat pt     = refl

    qt : {Γ : Cont} → Tm (Γ ▸t)
    ∣ qt ∣ I x = proj₂ x
    nat qt     = refl

    DPShV : ℕ -> Cont
    ∣ DPShV zero ∣ I    = 𝟙
    ∣ DPShV (suc n) ∣ I = ∣ DPShV n ∣ I × D I
    DPShV zero ∶ d ⟨ f ⟩ = d
    DPShV (suc n) ∶ dpn ,Σ d ⟨ f ⟩ = ((DPShV n) ∶ dpn ⟨ f ⟩) ,Σ D∶ d ⟨ f ⟩
    DPShV zero ∶⟨id⟩ = refl
    DPShV (suc n) ∶⟨id⟩ = mk,=(DPShV n ∶⟨id⟩) D∶⟨id⟩
    DPShV zero ∶⟨∘⟩ = refl
    DPShV (suc n) ∶⟨∘⟩ = mk,= (DPShV n ∶⟨∘⟩) D∶⟨∘⟩

    Tms : Cont -> ℕ -> Set
    Tms Γ n = Subt Γ (DPShV n)

    _[_]ts : ∀{Γ n} → Tms Γ n → ∀{Δ} → Subt Δ Γ → Tms Δ n
    ∣ ts [ γt ]ts ∣ I Δi = ∣ ts ∣ I (∣ γt ∣ I Δi)
    nat (ts [ γt ]ts) {I}{J} = trans (nat ts) (cong (∣ ts ∣ J) (nat γt))
    
    εs : ∀{Γ} → Tms Γ zero
    ∣ εs ∣ I x = *
    nat εs     = refl

    ◆sη    : ∀{Γ}(ts : Tms Γ zero) → ts ≡ εs
    ◆sη ts = mkSubtEq {nat₁ = refl}{nat₂ = refl} (funext (λ I → funext λ x → refl)) -- (λ x → mk,sp= (proj₂ (∣ ts ∣ I x)))))

    _,s_ : ∀{Γ n} → Tms Γ n → Tm Γ → Tms Γ (suc n)
    ∣ ts ,s t ∣ I x = (∣ ts ∣ I x) ,Σ (∣ t ∣ I x)
    (ts ,s t) .nat = mk,= (ts .nat) (t .nat)
    
    π₁ : ∀{Γ n} → Tms Γ (suc n) → Tms Γ n
    ∣ π₁ ts ∣ I x = proj₁ (∣ ts ∣ I x)
    nat (π₁ ts) = (cong proj₁ (nat ts))

    π₂ : ∀{Γ n} → Tms Γ (suc n) → Tm Γ
    ∣ π₂ ts ∣ I x = proj₂ (∣ ts ∣ I x)
    nat (π₂ ts) = (cong proj₂ (nat ts))

    recTms : ∀{n} -> (I : Ob) -> ∣ DPShV n ∣ I -> (D I) ^ n
    recTms {zero } I ts = *
    recTms {suc n} I (ts ,Σ d) = d ,Σ recTms I ts
    
    ⟨recTms⟩ : ∀{n I J}{f : Hom J I}{ts : ∣ DPShV n ∣ I} -> map^ (recTms {n} I ts) (D∶_⟨ f ⟩) ≡ recTms J ((DPShV n) ∶ ts ⟨ f ⟩)
    ⟨recTms⟩ {zero} {I} {J} {f} {ts} = refl
    ⟨recTms⟩ {suc n} {I} {J} {f} {ts} = mk,= refl ⟨recTms⟩

    fun' : {Γ : Cont} (n : ℕ) → funar n → Tms Γ n → Tm Γ
    ∣ fun' n a ts ∣ I x = fun n a I (recTms I (∣ ts ∣ I x)) -- fun n a (recTms I (∣ ts ∣ I x))
    nat (fun' n a ts) {I}{J}{i}{f} = trans (⟨fun⟩ n a I J (recTms I (∣ ts ∣ I i)) f) (cong (fun n a J) (trans (⟨recTms⟩ {n} {I} {J} {f} {∣ ts ∣ I i}) (cong (recTms J) (nat ts)))) -- cong (fun n a) (trans ⟨recTms⟩ (cong (recTms J) (nat ts)))

    rel' : {Γ : Cont} (n : ℕ) → relar n → Tms Γ n → For Γ
    ∣ rel' n a ts ∣ I x = rel n a I (recTms I (∣ ts ∣ I x))
    _∶_⟨_⟩ (rel' n a ts) {I} {J} {i} x f = substp (rel n a J) (trans ⟨recTms⟩ (cong (recTms J) (nat ts))) (⟨rel⟩ {n}{a}{I}{J}{recTms I (∣ ts ∣ I i)} x f) -- ⟨rel⟩ (substp (λ z -> rel n a z I) (trans ⟨recTms⟩ (cong (recTms J) (nat ts))) x) f

    record Conp(Γt : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γt ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γt ∣ I} -> A I i -> (f : Hom J I) -> A J (Γt ∶ i ⟨ f ⟩)
    open Conp public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)
    
    _[_]C : ∀{Γt Δt} -> Conp Γt -> Subt Δt Γt -> Conp Δt
    ∣ Γ [ γt ]C ∣ I x = ∣ Γ ∣ I (∣ γt ∣ I x)
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

    ⊤ : {Γt : Cont} → For Γt
    ∣ ⊤ ∣ I x = 𝟙p
    ⊤ ∶ x ⟨ f ⟩ = *

    tt : {Γt : Cont} {Γ : Conp Γt} → Pf Γ ⊤
    ∣ tt ∣ = λ _ → *

    _⊃_ : {Γt : Cont} → For Γt → For Γt → For Γt
    ∣ _⊃_ {Γt} K L ∣ I x = (J : Ob) -> (f : Hom J I) -> ∣ K ∣ J (Γt ∶ x ⟨ f ⟩) -> ∣ L ∣ J (Γt ∶ x ⟨ f ⟩)
    (_∶_⟨_⟩ (_⊃_ {Γt} K L) {I}{J}{i}) = λ x f J' g Ki → substp (∣ L ∣ J') (Γt ∶⟨∘⟩) (x J' (f ∘C g) (substp (∣ K ∣ J') (sym (Γt ∶⟨∘⟩)) Ki))
    
    ⊃[] : {Γt : Cont} {K L : For Γt} {Δt : Cont} {γt : Subt Δt Γt} →
      ((K ⊃ L) [ γt ]F) ≡ ((K [ γt ]F) ⊃ (L [ γt ]F))
    ⊃[] {Γt} {K} {L} {Δt} {γt} = 
        mkForEq {Δt} 
        {∣ (K ⊃ L) [ γt ]F ∣} {∣ (K [ γt ]F) ⊃ (L [ γt ]F) ∣}
        -- sub₁
        {λ {I} x f J g Kj → 
          let Kj' = substp (∣ K ∣ J) (trans (cong (Γt ∶_⟨ g ⟩) (sym (nat γt))) (sym (Γt ∶⟨∘⟩))) Kj in 
          substp (∣ L ∣ J) (trans ((Γt ∶⟨∘⟩)) (cong (Γt ∶_⟨ g ⟩) (nat γt))) (x J (f ∘C g) Kj')}
        -- ? : ∣ L ∣ J (Γt ∶ ∣ γt ∣ J₁ (Δt ∶ i ⟨ f ⟩) ⟨ g ⟩)
        -- x J (f ∘C g) : ∣ K ∣ J (Γt ∶ ∣ γt ∣ I i ⟨ f ∘C g ⟩) -> ∣ L ∣ J (Γt ∶ ∣ γt ∣ I i ⟨ f ∘C g ⟩)
        -- Kj : ∣ K ∣ J (Γt ∶ ∣ γt ∣ J₁ (Δt ∶ i ⟨ f ⟩) ⟨ g ⟩)
        -- sub₂
        {λ {I} x f J g Kj → 
          let Kj' = substp (λ z -> (∣ K ∣ J) (∣ γt ∣ J z)) (sym (Δt ∶⟨∘⟩)) Kj in 
          substp (λ z -> (∣ L ∣ J) (∣ γt ∣ J z)) ((Δt ∶⟨∘⟩)) (x J (f ∘C g) Kj')}
        -- ? : ∣ L ∣ J (∣ γt ∣ J (Δt ∶ Δt ∶ i ⟨ f ⟩ ⟨ g ⟩))
        -- x J (f ∘C g) : ∣ K ∣ J (∣ γt ∣ J (Δt ∶ i ⟨ f ∘C g ⟩)) → ∣ L ∣ J (∣ γt ∣ J (Δt ∶ i ⟨ f ∘C g ⟩))
        -- Kj : ∣ K ∣ J (∣ γt ∣ J (Δt ∶ Δt ∶ i ⟨ f ⟩ ⟨ g ⟩))
        -- Proof
        (funext (λ I → funext (λ Δi → cong (λ Z -> (J : Ob) (f : Hom J I) → Z J f)
        (funext (λ J → funext 
        (λ f → cong (λ z → ∣ K ∣ J (proj₁ z) → ∣ L ∣ J (proj₂ z)) 
        (mk,= (nat γt) (nat γt))))))))

    ⊃intro : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf (Γ ▸p K) L → Pf Γ (K ⊃ L)
    ∣ ⊃intro {Γt}{K}{L}{Γ} PfKL ∣ Γi J f Kj = ∣ PfKL ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ Kj)

    ⊃elim : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} →
      Pf Γ (K ⊃ L) → Pf (Γ ▸p K) L
    ∣ ⊃elim {Γt}{K}{L}{Γ} PfKL ∣ {I}{i} (Γi ,Σ Ki) = substp (∣ L ∣ I) (Γt ∶⟨id⟩) (∣ PfKL ∣ Γi I idC (substp (∣ K ∣ I) (sym (Γt ∶⟨id⟩)) Ki))

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

    ∀' : {Γt : Cont} → For (Γt ▸t) → For Γt
    ∣ ∀' {Γt} K ∣ I Γi = (J : Ob) -> (f : Hom J I) -> (d : D J) -> ∣ K ∣ J ((Γt ∶ Γi ⟨ f ⟩) ,Σ d)
    _∶_⟨_⟩ (∀' {Γt} K) {I} {J} {i} x f J' g d = substp (λ z -> ∣ K ∣ J' (z ,Σ d)) (Γt ∶⟨∘⟩) (x J' (f ∘C g) d) 

    ∀[] : {Γt : Cont} {K : For (Γt ▸t)} {Δt : Cont} {γt : Subt Δt Γt} →
      (∀' K [ γt ]F) ≡ ∀' (K [ (γt ∘t pt) ,t qt {Δt} ]F)
    ∀[] {Γt} {K} {Δt} {γt} = 
      mkForEq 
      {Δt}{∣ ∀' K [ γt ]F ∣}{∣ ∀' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F) ∣}
      {λ {I}{J}{Δi} x f J' g d → substp (λ z -> ∣ K ∣ J' (z ,Σ d)) (trans (Γt ∶⟨∘⟩) (cong (Γt ∶_⟨ g ⟩) (nat γt))) (x J' (f ∘C g) d)}
      {λ {I}{J}{Δi} x f J' g d → substp (λ z -> ∣ K ∣ J' (∣ γt ∣ J' z ,Σ d)) (Δt ∶⟨∘⟩) (x J' (f ∘C g) d)}
      (funext (λ I → 
      funext (λ Δi → 
      cong (λ Z → (J : Ob)(f : Hom J I)(d : D J) -> Z J f d) 
      (funext λ J → funext (λ f → funext (λ d → cong (λ z → ∣ K ∣ J (z ,Σ d)) (nat γt)))))))  

    ∀intro : {Γt : Cont} {K : For (Γt ▸t)} {Γ : Conp Γt} →
      Pf (Γ [ pt ]C) K → Pf Γ (∀' K)
    ∣ ∀intro {Γt}{K}{Γ} PfK ∣ Γi J f d = ∣ PfK ∣ (Γ ∶ Γi ⟨ f ⟩)

    ∀elim : {Γt : Cont} {K : For (Γt ▸t)} {Γ : Conp Γt} →
      Pf Γ (∀' K) → Pf (Γ [ pt ]C) K
    ∣ ∀elim {Γt}{K}{Γ} PfK ∣ {I} {Γti ,Σ d} Γi = substp (λ z -> ∣ K ∣ I (z ,Σ d)) (Γt ∶⟨id⟩) (∣ PfK ∣ Γi I idC d) -- ∣ PfK ∣ Γi d

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
      ; Tms = Tms
      ; _[_]ts = λ {Γ}{n} ts {Δ} ->  _[_]ts {Γ}{n} ts {Δ}
      ; [∘]ts = refl
      ; [id]ts = refl
      ; εs = εs
      ; ◆sη = λ ts → refl
      ; _,s_ = λ {Γ}{n} -> _,s_ {Γ}{n}
      ; π₁ = λ {Γ}{n} -> π₁ {Γ}{n}
      ; π₂ = λ {Γ}{n} -> π₂ {Γ}{n}
      ; ▸sβ₁ = refl
      ; ▸sβ₂ = refl
      ; ▸sη = refl
      ; ,[] = refl
      ; fun = fun'
      ; fun[] = refl
      ; rel = rel'
      ; rel[] = refl
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
      ; ◆p[] = refl
      ; ▸p[] = refl
      ; ⊤ = ⊤
      ; ⊤[] = refl
      ; tt = tt
      ; _⊃_ = _⊃_
      ; ⊃[] = λ {Γt}{K}{L}{Δt}{γt} -> ⊃[] {Γt}{K}{L}{Δt}{γt}
      ; ⊃intro = λ{Γt}{K}{L}{Γ} -> ⊃intro {Γt}{K}{L}{Γ}
      ; ⊃elim = λ{Γt}{K}{L}{Γ} -> ⊃elim {Γt}{K}{L}{Γ}
      ; _∧_ = _∧_
      ; ∧[] = refl
      ; ∧intro = ∧intro
      ; ∧elim₁ = λ {Γt}{K}{L} -> ∧elim₁ {L = L}
      ; ∧elim₂ = λ {Γt}{K}{L} -> ∧elim₂ {K = K} 
      ; ∀' = ∀'
      ; ∀[] = λ {Γt}{K}{Δt}{γt} → ∀[] {Γt}{K}{Δt}{γt}
      ; ∀intro = λ {Γt}{K}{Γ} -> ∀intro {Γt}{K}{Γ} 
      ; ∀elim = λ {Γt}{K}{Γ} -> ∀elim {Γt}{K}{Γ}
      }
    
module Completeness where
    
    open import FirstOrderLogic.IntNegative.Syntax funar relar as I

    Con : Set
    Con = Σ ConTm ConPf

    Sub : Con -> Con -> Set
    Sub (Δt ,Σ Δ) (Γt ,Σ Γ) = Σsp (Subt Δt Γt) (λ γ -> Subp Δ (Γ [ γ ]C))

    id : ∀{Γ} -> Sub Γ Γ
    id {Γt ,Σ Γ} = I.idt ,Σ substp (Subp Γ) (sym [id]C) I.idp
    
    _∘_ : {A B C : Con} → Sub B C → Sub A B → Sub A C
    _∘_ {Γt ,Σ Γ} {Δt ,Σ Δ} {Θt ,Σ Θ} (γt ,Σ γ) (δt ,Σ δ) = (γt ∘t δt) ,Σ (substp (Subp (Δ [ δt ]C)) (sym [∘]C) (γ I.[ δt ]s) ∘p δ)

    ass' : {A B C D : Con}{f : Sub C D}
      {g : Sub B C} {h : Sub A B} →
      ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))
    ass' = mk,sp= I.ass

    idl' : {A B : Con} {f : Sub A B} → (id ∘ f) ≡ f
    idl' = mk,sp= idl
    idr' : {A B : Con} {f : Sub A B} → (f ∘ id) ≡ f
    idr' = mk,sp= idr

    ◆ : Con
    ◆ = ◆t ,Σ ◆p

    ε : {Γ : Con} → Sub Γ ◆
    ε {Γt ,Σ Γp} = εt ,Σ εp

    ◆η : {Γ : Con} (σ : Sub Γ ◆) → σ ≡ ε {Γ}
    ◆η {Γt ,Σ Γp} (εt ,Σ _) = refl

    _▸t' : Con -> Con
    (Γt ,Σ Γ) ▸t' = (Γt ▸t) ,Σ (Γ I.[ I.pt ]C)

    qt' : ∀{Γ : Con} -> Tm (proj₁ (Γ ▸t'))
    qt' {Γt ,Σ Γ} = I.qt {Γt}

    pt' : ∀{Γ : Con} -> Sub (Γ ▸t') Γ
    pt' {Γt ,Σ Γ} = I.pt ,Σ I.idp

    _,t'_ : ∀{Γ Δ} → Sub Δ Γ → I.Tm (proj₁ Δ) → Sub Δ (Γ ▸t')
    _,t'_ {Γt ,Σ Γ}{Δt ,Σ Δ} (γt ,Σ γ) t = (γt ,t t) ,Σ substp (Subp Δ) (trans (cong (Γ [_]C) (sym I.▸tβ₁)) [∘]C)  γ

    _▸p'_ : (Γ : Con) -> I.For (proj₁ Γ) -> Con
    (Γt ,Σ Γ) ▸p' K = Γt ,Σ (Γ ▸p K)

    _,p'_ : ∀{Γ Δ : Con} → (γ : Sub Δ Γ) → ∀{K : For (proj₁ Γ)} → I.Pf (proj₂ Δ) (K [ γ .proj₁ ]F) → Sub Δ (Γ ▸p' K)
    _,p'_ {Γt ,Σ Γ}{Δt ,Σ Δ} (γt ,Σ γ) PfK = γt ,Σ (γ ,p PfK)

    qp' : ∀{Γ : Con}{K} → I.Pf (proj₂ (Γ ▸p' K)) K
    qp' = qp

    pp' : ∀{Γ : Con}{K : I.For (proj₁ Γ)} -> Sub (Γ ▸p' K) Γ
    pp' {Γt ,Σ Γ} {K} = I.idt ,Σ (substp (Subp (Γ ▸p K)) (sym [id]C) pp)

    _↑t : ∀{Γt Δt} -> Subt Δt Γt -> Subt (Δt ▸t) (Γt ▸t)
    γt ↑t = γt ∘t pt ,t qt

    _↑p : ∀{Γt}{Γ Δ : I.ConPf Γt}{K} -> Subp Δ Γ -> Subp (Δ ▸p K) (Γ ▸p K)
    γp ↑p = γp ∘p pp ,p qp

    ↑t-pt : ∀{Γt Δt : I.ConTm} -> (γt : Subt Δt Γt) -> pt ∘t (γt ↑t) ≡ γt ∘t pt
    ↑t-pt γt = ▸tβ₁

    ↑-,t  : ∀{Γt Δt : I.ConTm} -> (γt : Subt Δt Γt) -> (d : I.Tm Δt) -> γt ↑t ∘t (idt ,t d) ≡ γt ,t d
    ↑-,t εt d = refl
    ↑-,t {Γt ▸t}{Δt} (γt ,t t) d = 
        cong-bin (I._,t_) 
        (trans (cong-bin _,t_ 
            (trans ass (trans (cong (γt I.∘t_) (trans ▸tβ₁ (sym ▸tβ₁))) (sym ass))) 
            (trans (sym ([∘]t {t = t}{γ = pt}{δ = idt ,t d})) 
            (trans (cong (t [_]t) ▸tβ₁) [id]t))) (↑-,t {Γt}{Δt} γt t)) 
        refl
    
    ∘t-pt : ∀{Γt Δt Θt : I.ConTm} -> (γt : Subt Δt Γt) -> (δt : Subt Θt Δt) -> (γt ∘t δt) ∘t pt ≡ (γt ∘t pt) ∘t (δt ∘t pt ,t qt)
    ∘t-pt εt δt = refl
    ∘t-pt (γt ,t t) δt = cong-bin _,t_ (∘t-pt γt δt) (trans (sym ([∘]t {t = t}{γ = δt}{δ = pt})) (trans (cong (t [_]t) ((sym ▸tβ₁))) ([∘]t {t = t}{γ = pt}{δ = δt I.∘t I.pt I.,t I.qt})))

    _↑t' : ∀{Γ Δ : Con} -> Sub Δ Γ -> Sub (Δ ▸t') (Γ ▸t')
    _↑t' {Γ@(Γt ,Σ Γp)}{Δ@(Δt ,Σ Δp)} (γt ,Σ γp) = (γt ↑t) ,Σ substp (Subp (Δp [ pt ]C)) (trans (sym [∘]C) (trans (cong (Γp [_]C) (sym (↑t-pt γt))) [∘]C)) (γp [ I.pt ]s)    

    _[_]t' : ∀{Γ Δ} -> Tm (proj₁ Γ) -> Sub Δ Γ → Tm (proj₁ Δ)
    t [ (γt ,Σ γp ) ]t' = t [ γt ]t

    ▸t'β₁  : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm (proj₁ Δ)} → (pt' ∘ (γ ,t' t)) ≡ γ
    ▸t'β₁ {Γ} {Δ} {γ} {t} = mk,sp= ▸tβ₁

    ▸t'β₂  : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm (proj₁ Δ)} → ((qt' {Γ}) [ γ ,t' t ]t') ≡ t
    ▸t'β₂ = refl

    ▸t'η   : ∀{Γ Δ}{γ : Sub Δ (Γ ▸t')} -> ((pt' ∘ γ) ,t' ((qt' {Γ}) [ γ ]t')) ≡ γ
    ▸t'η = mk,sp= ▸tη

    C : Category
    C = record
      { Ob = Con
      ; Hom = Sub
      ; idC = id
      ; _∘C_ = λ γ δ -> γ ∘ δ
      ; assC = λ {Γ}{Δ}{Θ}{Ξ}{γ}{δ}{θ} -> ass' {Γ}{Δ}{Θ}{Ξ}{γ}{δ}{θ}
      ; idlC = λ {Γ}{Δ}{γ} -> idl' {Γ}{Δ}{γ}
      ; idrC = λ {Γ}{Δ}{γ} -> idr' {Γ}{Δ}{γ}
      }

    reifyTms : ∀{Γt n} -> I.Tm Γt ^ n -> I.Tms Γt n
    reifyTms {Γt}{zero} * = *
    reifyTms {Γt}{suc n} (t ,Σ ts) = (reifyTms ts) ,Σ t

    reflectTms : ∀{Γt n} -> I.Tms Γt n -> I.Tm Γt ^ n
    reflectTms {Γt}{zero} * = *
    reflectTms {Γt}{suc n} (ts ,Σ t) = t ,Σ reflectTms ts

    ⟨reifyTms⟩ : ∀{n Γt Δt}{ds : Tm Γt ^ n}{γ : I.Subt Δt Γt} -> (reifyTms (map^ ds (_[ γ ]t))) ≡ (reifyTms ds [ γ ]ts)
    ⟨reifyTms⟩ {zero} {Γt} {Δt} {ds} {γ} = refl
    ⟨reifyTms⟩ {suc n} {Γt} {Δt} {ds} {γ} = mk,= ⟨reifyTms⟩ refl 

    module K = Semantics
        C
        (λ (Γt ,Σ Γ) → I.Tm Γt)
        (λ t (γt ,Σ γ) -> t I.[ γt ]t)
        (λ {Γ}{Δ}{Θ}{t}{(γt ,Σ γ)}{(δt ,Σ δ)} -> [∘]t {t = t}{γ = γt}{δ = δt})
        (λ {Γ}{t} -> [id]t {t = t})
        (λ n a (Γt ,Σ Γ) ts -> I.Pf Γ (rel n a (reifyTms {Γt} ts)))
        (λ {n}{a}{(Γt ,Σ Γ)}{(Δt ,Σ Δ)}{ts} Pfrel (γt ,Σ γ) → substp (λ z -> Pf Δ (rel n a z)) (sym ⟨reifyTms⟩) ((Pfrel I.[ γt ]p) [ γ ]P))
        (λ n a (Γt ,Σ Γ) ts -> fun n a (reifyTms ts))
        (λ n a (Γt ,Σ Γ) (Δt ,Σ Δ) ts (γt ,Σ γ) -> cong (fun n a) (sym ⟨reifyTms⟩))

    open K
    open import FirstOrderLogic.IntNegative.Iterator
    open Ite funar relar Kripke

    mutual
        
        reflect-cont : ∀{Γt : I.ConTm}{Γ : I.ConPf Γt}(Δt : I.ConTm) -> (γt : I.Subt Γt Δt) -> ∣ ⟦ Δt ⟧Cont ∣ (Γt ,Σ Γ)
        reflect-cont ◆t x = *
        reflect-cont (Δt ▸t) (γ ,t t) = reflect-cont Δt γ ,Σ t

        reflect-conp : ∀{Γt}{Γ}{Δt} (Δ : I.ConPf Δt) -> (γt : I.Subt Γt Δt) -> (γ : I.Subp Γ (Δ I.[ γt ]C)) -> ∣ ⟦ Δ ⟧Conp ∣ (Γt ,Σ Γ) (reflect-cont Δt γt)
        reflect-conp {Γt}{Γ}{Δt} ◆p γ γt = *
        reflect-conp {Γt}{Γ}{Δt} (Δ ▸p K) γt γ = (reflect-conp Δ γt (I.pp I.∘p γ)) ,Σ reflect {Δt}{Γt}{Γ}{γt} K (I.qp I.[ γ ]P)
        
        reflect-con : ∀{Γ : Con} (Δ : Con) -> Sub Γ Δ -> Σsp (∣ ⟦ proj₁ Δ ⟧Cont ∣ Γ) (∣ ⟦ proj₂ Δ ⟧Conp ∣ Γ)
        reflect-con {Γt ,Σ Γ} (Δt ,Σ Δ) (γt ,Σ γ) = reflect-cont Δt γt ,Σ reflect-conp Δ γt γ

        reflect-TmVar : ∀{Γt Δt Δ}{γt : I.Subt Δt (Γt I.▸t)}{v : V.Tm (Γt I.▸t)} -> ∣ ⟦ var v ⟧Tm ∣ (Δt ,Σ Δ) (reflect-cont (Γt I.▸t) γt) ≡ var v I.[ γt ]t
        reflect-TmVar {Γt} {Δt} {Δ} {γt ,t t} {V.Tm.vz} = refl
        reflect-TmVar {Γt ▸t} {Δt} {Δ} {γt ,t t} {V.Tm.vs v} = reflect-TmVar {v = v}

        reflect-Tm : ∀{Γt Δt Δ}{γt : I.Subt Δt Γt}{t : I.Tm Γt} -> 
            ∣ ⟦ t ⟧Tm ∣ (Δt ,Σ Δ) (reflect-cont Γt γt) ≡ t I.[ γt ]t
        reflect-Tm {◆t} {Δt} {Δ} {γt} {fun zero a *} = refl
        reflect-Tm {◆t} {Δt} {Δ} {γt} {fun (suc n) a (ts ,Σ t)} = cong (fun (suc n) a) (mk,= reflect-Tms (reflect-Tm {I.◆t}{Δt}{Δ}{γt}{t}))
        reflect-Tm {Γt ▸t} {Δt} {Δ} {γt} {Tm.var v} = reflect-TmVar {v = v}
        reflect-Tm {Γt ▸t} {Δt} {Δ} {γt} {Tm.fun zero a *} = refl
        reflect-Tm {Γt ▸t} {Δt} {Δ} {γt} {Tm.fun (suc n) a (ts ,Σ t)} = cong (fun (suc n) a) (mk,= reflect-Tms (reflect-Tm {Γt I.▸t}{Δt}{Δ}{γt}{t}))

        reflect-Tms : ∀{n Γt Δt Δ}{γt : I.Subt Δt Γt}{ts : I.Tms Γt n} -> reifyTms (recTms (Δt ,Σ Δ) (∣ ⟦ ts ⟧Tms ∣ (Δt ,Σ Δ) (reflect-cont Γt γt))) ≡ ts I.[ γt ]ts
        reflect-Tms {zero} {Γt} {Δt} {Δ} {γt} {*} = refl
        reflect-Tms {suc n} {Γt} {Δt} {Δ} {γt} {(ts ,Σ t)} = mk,= reflect-Tms (reflect-Tm {Γt}{Δt}{Δ}{γt}{t})

        ⟨∘⟩-reflect-cont : ∀{Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{A : I.For Γt}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ} -> 
            ∣ ⟦ A ⟧For ∣ Θ (reflect-cont Γt (γt I.∘t δt)) ≡ 
            ∣ ⟦ A ⟧For ∣ Θ (⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ δ ⟩)
        ⟨∘⟩-reflect-cont {Γt} {Δ@(Δt ,Σ Δp)} {Θ@(Θt ,Σ Θp)} {A} {γt} {δ} = 
            cong (∣ ⟦ A ⟧For ∣ Θ) (⟨⟩-reflect-cont {Γt} {Δt} {Θt} {Δp} {Θp} {γt} {δ})

        ⟨⟩-reflect-cont : ∀{Γt Δt Θt : I.ConTm}{Δ : I.ConPf Δt}{Θ : I.ConPf Θt}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub (Θt ,Σ Θ) (Δt ,Σ Δ)} -> 
            (reflect-cont Γt (γt I.∘t δt)) ≡ ⟦ Γt ⟧Cont ∶ (reflect-cont Γt γt) ⟨ δ ⟩
        ⟨⟩-reflect-cont {◆t} {Δt} {Θt} {Δ} {Θ} {γt} {δ} = refl
        ⟨⟩-reflect-cont {Γt ▸t} {Δt} {Θt} {Δ} {Θ} {γt ,t t} {δ} = 
            let h = ⟨⟩-reflect-cont {Γt} {Δt} {Θt} {Δ} {Θ} {γt} {δ} in
            mk,= h refl

        ⟨d⟩-reflect-cont : ∀{Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{A : I.For (Γt I.▸t)}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{d : I.Tm Θt} -> 
            ∣ ⟦ A ⟧For ∣ Θ (reflect-cont Γt (γt I.∘t δt) ,Σ d)
            ≡
            ∣ ⟦ A ⟧For ∣ Θ ((⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ δ ⟩) ,Σ d)
        ⟨d⟩-reflect-cont {Γt} {Δ@(Δt ,Σ Δp)} {Θ@(Θt ,Σ Θp)} {A} {γt} {δ} {d} = 
            cong (∣ ⟦ A ⟧For ∣ Θ) (mk,= (⟨⟩-reflect-cont {Γt}{Δt}{Θt}{Δp}{Θp}{γt}{δ}) refl)

        ⟨pt⟩-reflect-cont : ∀{Γt : I.ConTm}{Δ@(Δt ,Σ Δp) : Con}{A : I.For (Γt I.▸t)}{γt : I.Subt Δt Γt} ->
            ∣ ⟦ A ⟧For ∣ (Δ ▸t') ((⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ pt' ⟩) ,Σ I.qt)
            ≡
            ∣ ⟦ A ⟧For ∣ (Δ ▸t') (reflect-cont Γt (γt I.∘t I.pt) ,Σ I.qt)
        ⟨pt⟩-reflect-cont {Γt} {Δ} {A} {γt} = sym (⟨d⟩-reflect-cont {Γt}{Δ}{Δ ▸t'}{A}{γt}{pt'}{I.qt})

        reify : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt) -> I.Pf Δ (A I.[ γt ]F)
        reify ⊤ x = I.tt
        reify {Γt} {Δt} {Δ} {γt} (A ⊃ B) x =
            let pa  = reflect {Γt}{Δt}{Δ I.▸p (A I.[ γt ]F)} A I.qp in
            let pa' = substp (λ z -> z) (trans (cong (λ z -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ (Δ I.▸p (A I.[ γt ]F))) (reflect-cont Γt z)) (sym idr)) (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Δt ,Σ (Δ I.▸p A I.[ γt ]F)}{A}{γt}{pp'})) pa in
            let pb = x (Δt ,Σ (Δ I.▸p A I.[ γt ]F)) pp' pa' in 
            let pb' = substp (λ z -> z) (trans (sym (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Δt ,Σ (Δ I.▸p A I.[ γt ]F)}{B}{γt}{pp'})) (cong (λ z -> ∣ ⟦ B ⟧For ∣ (Δt ,Σ (Δ I.▸p (A I.[ γt ]F))) (reflect-cont Γt z)) idr)) pb in
            I.⊃intro (reify B pb')
        reify {Γt} {Δt} {Δ} {γt} (A ∧ B) x = I.∧intro (reify {Γt}{Δt}{Δ}{γt} A (proj₁ x)) (reify {Γt}{Δt}{Δ}{γt} B (proj₂ x))
        reify {Γt} {Δt} {Δ} {γt} (∀' A) x = 
            let pa  = x ((Δt I.▸t) ,Σ Δ I.[ I.pt ]C) pt' I.qt in
            let pa' = substp (λ z -> z) (⟨pt⟩-reflect-cont {Γt}{Δt ,Σ Δ}{A}{γt}) pa in 
            I.∀intro (reify A pa')
        reify (rel zero a *) x = x
        reify {Γt} {Δt} {Δ} {γt} (rel (suc n) a (ts ,Σ t)) x = 
            substp (I.Pf Δ) 
            (cong (rel (suc n) a)
            let Tm-eq  = (reflect-Tm {Γt}{Δt}{Δ}{γt}{t}) in
            let Tms-eq =  (reflect-Tms {n}{Γt}{Δt}{Δ}{γt}{ts}) in
            (mk,= Tms-eq Tm-eq))
            x

        reflect : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> I.Pf Δ (A I.[ γt ]F) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt)
        reflect ⊤ x = *
        reflect {Γt} {Δt} {Δ} {γt} (A ⊃ B) x Θ@(Θt ,Σ Θp) δ@(δt ,Σ δp) pa =
            let PfA  = reify {Γt}{Θt}{Θp}{γt I.∘t δt} A (substp (λ z -> z) (sym (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Θ}{A}{γt}{δ})) pa) in 
            let PfAB = substp (λ z -> z) (cong (I.Pf Θp) (cong-bin I._⊃_ (sym [∘]F) (sym [∘]F))) (x I.[ δt ]p I.[ δp ]P) in 
            substp (λ z -> z) (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Θ}{B}{γt}{δ}) 
            (reflect {Γt}{Θt}{Θp}{γt I.∘t δt} B ((I.⊃elim PfAB) I.[ I.idp I.,p PfA ]P))
        reflect {Γt}{Δt}{Δ}{γt} (A ∧ B) x = reflect {Γt}{Δt}{Δ}{γt} A (I.∧elim₁ x) ,Σ reflect {Γt}{Δt}{Δ}{γt} B (I.∧elim₂ x)
        reflect {Γt}{Δt}{Δ}{γt} (∀' A) x Θ@(Θt ,Σ Θp) δ@(δt ,Σ δp) pa = 
            let Pf∀A = substp (λ z -> I.Pf Θp (I.∀' z)) (sym [∘]F) (x I.[ δt ]p I.[ δp ]P) in
            let k = (I.∀elim Pf∀A) I.[ I.idt I.,t pa ]p in
            let eq = (trans (trans (cong (λ z -> z I.∘t (I.idt I.,t pa) I.,t pa) (sym (∘t-pt γt δt))) refl) ((↑-,t (γt I.∘t δt) pa))) in
            let k' = substp (λ z -> I.Pf (proj₁ z) (proj₂ z)) (mk,=
                    (trans (sym [∘]C) (trans (cong (Θp I.[_]C) ▸tβ₁) [id]C)) 
                    (trans (sym [∘]F) (cong (A I.[_]F) eq))) k in
            substp (λ z -> z) (⟨d⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Θ}{A}{γt}{δ}{pa}) (reflect {Γt I.▸t}{Θt}{Θp}{(γt I.∘t δt) I.,t pa} A k')
        reflect (rel zero a *) x = x
        reflect {Γt} {Δt} {Δ} {γt} (rel (suc n) a (ts ,Σ t)) x = 
            substp (I.Pf Δ)
            (cong (rel (suc n) a)
            let Tm-eq  = sym (reflect-Tm {Γt}{Δt}{Δ}{γt}{t}) in
            let Tms-eq = sym (reflect-Tms {n}{Γt}{Δt}{Δ}{γt}{ts}) in
            (mk,= Tms-eq Tm-eq))
            x

    completeness : ∀{Γt}{Γ} -> (A : I.For Γt) -> K.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For -> I.Pf Γ A
    completeness {Γt}{Γ} A p = substp (I.Pf Γ) [id]F (reify {Γt}{Γt}{Γ} A (∣ p ∣ (reflect-conp Γ I.idt (substp (I.Subp Γ) (sym [id]C) I.idp))))
    
    soundness : ∀{Γt Γ} -> (A : I.For Γt) -> I.Pf Γ A -> K.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For
    soundness A = ⟦_⟧Pf