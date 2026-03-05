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
    --
    ---- (dzero : D)
    --(rel  : (n : ℕ) → relar n → D ^ n → Ob → Prop)
    --(⟨rel⟩ : ∀{n i ds I J} → rel n i ds I → Hom J I → rel n i ds J)
    --(fun  : (n : ℕ) → funar n → D ^ n → D)
    ---- (⟨fun⟩ : ∀{n i ds I J} → fun n i ds I → Hom J I → fun n i ds J)
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
    DPSh ∶⟨∘⟩      = D∶⟨∘⟩ --refl
    DPSh ∶⟨id⟩     = D∶⟨id⟩ --refl

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
    ∣ DPShV zero ∣ I    = 𝟙 -- Σsp D (λ d -> (d ≡ dzero)) 
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
    recTms {zero } I ts = * -- ts -- *
    recTms {suc n} I (ts ,Σ d) = d ,Σ recTms I ts -- d ,Σ recTms I ts -- proj₂ (∣ t ∣ I Γi) ,Σ recTms {Γ}{n} {! proj₁ (∣ t ∣ I Γi)  !} I Γi
    
    --⟨recTms⟩ : ∀{I J : Ob}{n : ℕ}{f : Hom J I}{ts : ∣ DPShV n ∣ I} -> recTms {n} I ts ≡ {! map^ (recTms {n} I ?) D∶_⟨ f ⟩  !} -- srecTms {n} J (DPShV n ∶ ts ⟨ f ⟩)
    --⟨recTms⟩ {I} {J} {zero} {f} {ts} = {!   !}
    --⟨recTms⟩ {I} {J} {suc n} {f} {ts} = mk,= {!   !} ⟨recTms⟩

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
      -- substp (∣ K ∣ J') (mk,= (Γt ∶⟨∘⟩) {! sym D∶⟨∘⟩ !}) (x J' (f ∘C g) D∶ d ⟨ {!   !} ⟩) -- λ d → K ∶ x d ⟨ f ⟩

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

    Eq : {Γt : Cont} → Tm Γt → Tm Γt → For Γt
    ∣ Eq t t' ∣ I Γi = ∣ t ∣ I Γi ≡ ∣ t' ∣ I Γi
    _∶_⟨_⟩ (Eq {Γt} t t') x f = trans (sym (nat t)) (trans (cong (D∶_⟨ f ⟩) x) (nat t'))
    
    Eq[] : {Γt Δt : Cont} {γt : Subt Δt Γt} {t t' : Tm Γt} →
      (Eq t t' [ γt ]F) ≡ Eq (t [ γt ]t) (t' [ γt ]t)
    Eq[] = refl
    
    Eqrefl : {Γt : Cont} {t : Tm Γt} {Γ : Conp Γt} → Pf Γ (Eq t t)
    ∣ Eqrefl ∣ = λ x → refl

    subst' : {Γt : Cont} (K : For (Γt ▸t)) {t t' : Tm Γt} {Γ : Conp Γt} →
      Pf Γ (Eq t t') → Pf Γ (K [ idt ,t t ]F) → Pf Γ (K [ idt ,t t' ]F)
    ∣ subst' K t=t' PfK ∣ {I}{i} x = substp (λ z → ∣ K ∣ I (i ,Σ z)) (∣ t=t' ∣ x) (∣ PfK ∣ x)

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
      ; Eq = Eq
      ; Eq[] = refl
      ; Eqrefl = λ {Γt}{t}{Γ} -> Eqrefl {Γt}{t}{Γ}
      ; subst' = subst'
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

    -- qt isnt needed
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

    _[_]t' : ∀{Γ Δ} -> Tm (proj₁ Γ) -> Sub Δ Γ → Tm (proj₁ Δ)
    t [ (γt ,Σ γp ) ]t' = t [ γt ]t

    ▸t'β₁  : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm (proj₁ Δ)} → (pt' ∘ (γ ,t' t)) ≡ γ
    ▸t'β₁ {Γ} {Δ} {γ} {t} = mk,sp= ▸tβ₁

    ▸t'β₂  : ∀{Γ Δ}{γ : Sub Δ Γ}{t : Tm (proj₁ Δ)} → ((qt' {Γ}) [ γ ,t' t ]t') ≡ t
    ▸t'β₂ = refl

    ▸t'η   : ∀{Γ Δ}{γ : Sub Δ (Γ ▸t')} -> ((pt' ∘ γ) ,t' ((qt' {Γ}) [ γ ]t')) ≡ γ -- ∈ (Subt (Γ ▸t) (Γ ▸t))
    ▸t'η = mk,sp= ▸tη

    C : Category
    C = record
      { Ob = Con
      ; Hom = Sub -- I.Subt
      ; idC = id -- I.idt
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

    --isoTms : ∀{n Γt}{ts : I.Tms Γt n} -> reifyTms (⟦ ts ⟧Tms ?) ≡ ts
    
    --isoTms {zero} {*} = refl
    --isoTms {suc n} {(ts ,Σ t)} = mk,= isoTms isoTm

    --isoTm {fun zero a *} = refl
    --isoTm {fun (suc n) a (ts ,Σ t)} = cong (fun (suc n) a) (mk,= isoTms isoTm)
    mutual
        
        reflect-cont : ∀{Γt : I.ConTm}{Γ : I.ConPf Γt}(Δt : I.ConTm) -> (γt : I.Subt Γt Δt) -> ∣ ⟦ Δt ⟧Cont ∣ (Γt ,Σ Γ)
        reflect-cont ◆t x = *
        reflect-cont (Δt ▸t) (γ ,t t) = reflect-cont Δt γ ,Σ t
        
        reflect-conp : ∀{Γt}{Γ}{Δt} (Δ : I.ConPf Δt) -> (γt : I.Subt Γt Δt) -> I.Subp Γ (Δ I.[ γt ]C) -> ∣ ⟦ Δ ⟧Conp ∣ (Γt ,Σ Γ) (reflect-cont Δt γt)
        reflect-conp {Γt}{Γ}{Δt} ◆p γ γt = *
        reflect-conp {Γt}{Γ}{Δt} (Δ ▸p K) γt γ = (reflect-conp Δ γt (I.pp I.∘p γ)) ,Σ reflect {Δt}{Γt}{Δ I.▸p K}{Γ}{γt ,Σ γ} K (I.qp I.[ γ ]P)
       
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

        reify : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γ : Sub (Δt ,Σ Δ) (Γt ,Σ Γ)}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt (proj₁ γ)) -> I.Pf Δ (A I.[ proj₁ γ ]F)
        reify ⊤ x = I.tt
        reify (A ⊃ B) x = {!   !}
        reify (A ∧ B) x = {!   !}
        reify (∀' A) x = {!   !}
        reify (Eq t t') x = {!   !}
        reify (rel n a ts) x = {!   !}

        reflect : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γ : Sub (Δt ,Σ Δ) (Γt ,Σ Γ)}(A : I.For Γt) -> (PfA : I.Pf Δ (A I.[ proj₁ γ ]F)) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt (proj₁ γ))
        reflect ⊤ x = *
        reflect {Γt} {Δt} {Γ} {Δ} γ@{γt ,Σ γp} (A ⊃ B) x (Θt ,Σ Θ) δ@(δt ,Σ δp) PfA = 
            let PfA = (I.qp I.[ I.idp I.,p {! reify A  !} ]P) in
            {! reflect {Γt}{Δt}{Γ}{Δ}{γ} A  !}
        reflect (A ∧ B) x = {!   !}
        reflect (∀' A) x = {!   !}
        reflect (Eq t t') x = {!   !}
        reflect (rel n a ts) x = {!   !}
        

        
        {- -- Doesnt work
        reflect-cont-backwards : ∀{Γt : I.ConTm}{Γ : I.ConPf Γt}(Δt : I.ConTm) -> (γt : I.Subt Δt Γt) -> ∣ ⟦ Δt ⟧Cont ∣ (Γt ,Σ Γ)
        reflect-cont-backwards {◆t} {Γ} ◆t εt = *
        reflect-cont-backwards {◆t} {Γ} (Δt ▸t) εt = (reflect-cont-backwards Δt I.εt) ,Σ {!   !}
        reflect-cont-backwards {Γt ▸t} {Γ} ◆t γt = *
        reflect-cont-backwards {Γt ▸t} {Γ} (Δt ▸t) (γt ,t t) = {!   !} ,Σ (t I.[ {! γt  !} ]t)
        -- Or this 
        reflect-cont-bw : ∀{Γt : I.ConTm}{Γ : I.ConPf Γt}(Δt : I.ConTm){Δ : I.ConPf Δt} -> (γt : I.Subt Γt Δt) -> ∣ ⟦ Γt ⟧Cont ∣ (Δt ,Σ Δ)
        reflect-cont-bw {◆t} {Γ} Δt {Δ} γt = *
        reflect-cont-bw {Γt ▸t} {Γ} Δt {Δ} εt = (reflect-cont-bw {Γt}{Γ I.[ {!   !} ]C} Δt {Δ} I.εt) ,Σ {!   !}
        reflect-cont-bw {Γt ▸t} {Γ} Δt {Δ} (γt ,t x) = {!   !}

        -- 
        reflect-cont' : ∀{Γt : I.ConTm}{Γ : I.ConPf Γt}(Δt : I.ConTm){Δ : I.ConPf Δt} -> (γt : I.Subt Γt Δt) -> (γ : I.Subp Γ (Δ I.[ γt ]C)) -> ∣ ⟦ Δt ⟧Cont ∣ (Γt ,Σ Γ)
        reflect-cont' ◆t x γ = *
        reflect-cont' {Γt}{Γ} (Δt ▸t) {Δ} (γt ,t t) γ = reflect-cont' {Γt}{Γ} Δt {Δ} γt {! γ  !} ,Σ t
        -}
 
        {-
        -- OLD
        -- weak conp
        reflect-conp-weak : ∀{Γt}{Γ} (Δ : I.ConPf Γt) -> I.Subp Γ Δ -> ∣ ⟦ Δ ⟧Conp ∣ (Γt ,Σ Γ) (reflect-cont Γt I.idt)
        reflect-conp-weak {Γt}{Γ} ◆p γ = *
        reflect-conp-weak {Γt}{Γ} (Δ ▸p K) γ = reflect-conp-weak Δ (I.pp I.∘p γ) ,Σ reflect K (I.qp I.[ γ ]P) -- (reflect-conp Δ (I.pp I.∘p γ)) ,Σ reflect  K (I.qp I.[ γ ]P)
        -}

        
        
        help : ∀{Γ}{K}{PfK : I.Pf (proj₂ Γ) K} -> (id {Γ}) ≡ ((pp' {Γ}{K}) ∘ (I.idt ,Σ substp (I.Subp (proj₂ Γ)) (cong (λ z → proj₁ z I.▸p proj₂ z) (mk,= (sym [id]C) (sym [id]F))) (I.idp I.,p PfK)))
        help {Γ} {K} {PfK} = mk,sp= (sym idl)

        ⟨pp⟩-reflect-cont : ∀{Γ Δ : Con}{K : I.For (proj₁ Δ)}{γt : I.Subt (proj₁ Δ) (proj₁ Γ)}{PfK : I.Pf (proj₂ Δ) K} -> (⟦ (proj₁ Γ) ⟧Cont ∶ (reflect-cont (proj₁ Γ) γt) ⟨ ((pp' {Δ}) ∘ (I.idt ,Σ substp (I.Subp (proj₂ Δ)) (cong (λ z → proj₁ z I.▸p proj₂ z) (mk,= (sym [id]C) (sym [id]F))) (I.idp I.,p PfK)) ) ⟩) ≡ reflect-cont (proj₁ Γ) γt
        ⟨pp⟩-reflect-cont {Γt ,Σ Γ}{Δ}{K}{γt}{PfK} = trans (cong (λ z → ⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ z ⟩) (sym (help {Δ}{K}{PfK}))) (⟦ Γt ⟧Cont ∶⟨id⟩) -- substp (λ z -> (⟦ Γt ⟧Cont ∶ reflect-cont {proj₁ Δ}{proj₂ Δ} Γt γt ⟨ z ⟩) ≡ reflect-cont Γt γt) ({! help {Γt ,Σ Γ}{K}{?}  !}) ({! ⟦ Γt ⟧Cont ∶⟨id⟩  !})
        
        {- TODO : Very much needed, best i have rn
        reflect' : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> I.Pf Δ (A I.[ γt ]F) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt) -- (Δt ,Σ (Γ I.[ γt ]C)) (reflect-cont Γt γt)
        reify'   : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt) -> I.Pf Δ (A I.[ γt ]F)
        
        reflect' ⊤ x = *
        reflect' {Γt}{Δt}{Γ}{Δ}{γt} (A ⊃ B) x (Θt ,Σ Θ) (δt ,Σ δ) PfA = {! reflect' {Γt}{Θt}{Γ}{Θ}{γt I.∘t δt} B ((I.⊃elim ?) I.[ ? ]P ) !}
        reflect' {Γt}{Δt}{Γ}{Δ}{γt} (A ∧ B) x = reflect' {Γt}{Δt}{Γ}{Δ}{γt} A (I.∧elim₁ x) ,Σ reflect' {Γt}{Δt}{Γ}{Δ}{γt} B (I.∧elim₂ x)
        reflect' {Γt}{Δt}{Γ}{Δ}{γt} (∀' A) x (Θt ,Σ Θ) δ d = {! reflect' A (I.∀elim x d)  !}
        reflect' (Eq t t') x = {!   !}
        reflect' (rel zero a ts) x = x
        reflect' {Γt}{Δt}{Γ}{Δ}{γt} (rel (suc n) a (ts ,Σ t)) x =
          substp (I.Pf Δ) (cong (rel (suc n) a) 
          (mk,= (sym (isoTms' {n}{Γt}{Δt}{Δ}{γt}{ts})) (sym (isoTm' {Γt}{Δt}{Δ}{γt}{t})))) 
          x 

        reify' ⊤ x = I.tt
        reify' {Γt}{Δt}{Γ}{Δ}{γt} (A ⊃ B) x = let PfA = reflect' {Γt}{Δt}{Γ}{Δ I.▸p A I.[ γt ]F}{γt} A I.qp in
            I.⊃intro 
            (reify' {Γt}{Δt}{Γ}{Δ I.▸p A I.[ γt ]F} B  -- I.idt ,Σ (I.idp I.,p ?)
            {! ⟦ B ⟧For ∶ (x (Δt ,Σ Δ) id ?) ⟨ pp' ⟩ !})
            {-
            I.⊃intro 
            (reify' {Γt}{Δt}{Γ}{Δ I.▸p A I.[ γt ]F} B 
            (substp (∣ ⟦ B ⟧For ∣ _) (⟨pp⟩-reflect-cont {Γt ,Σ Γ}{Δt ,Σ Δ}{A}{γt}) 
            (x (Δt ,Σ (Δ I.▸p A I.[ γt ]F)) pp'
            (substp (∣ ⟦ A ⟧For ∣ _) (sym (⟨pp⟩-reflect-cont {Γt ,Σ Γ}{Δt ,Σ Δ}{A}{γt})) 
            (reflect' {Γt}{Δt}{Γ}{Δ I.▸p A I.[ γt ]F}{γt} A I.qp)))))
            -}
            
            {-
            (reify' B 
            (substp (∣ ⟦ B ⟧For ∣ (Δt ,Σ (Δ I.▸p A I.[ γt ]F))) ({!   !}) 
            (x ((Δt ,Σ Δ) ▸p' (A I.[ γt ]F)) pp'
            (substp (λ z -> ∣ ⟦ A ⟧For ∣ (proj₁ z) (proj₂ z)) {!   !} 
            (reflect' A I.qp)))))
            -}
        reify' {Γt}{Δt}{Γ}{Δ}{γt} (A ∧ B) x = I.∧intro (reify' {Γt}{Δt}{Γ}{Δ}{γt} A (proj₁ x)) (reify' {Γt}{Δt}{Γ}{Δ}{γt} B (proj₂ x))
        reify' (∀' A) x = I.∀intro (reify' A  (x _ pt' I.qt))
        reify' (Eq t t') x = _
        reify' (rel zero a ts) x = x
        reify' {Γt}{Δt}{Γ}{Δ}{γt} (rel (suc n) a (ts ,Σ t)) x = 
          substp (I.Pf Δ) (cong (rel (suc n) a) 
          (mk,= (isoTms' {n}{Γt}{Δt}{Δ}{γt}{ts}) (isoTm' {Γt}{Δt}{Δ}{γt}{t}))) 
          x
        -}

        help' : ∀{Γ Δ Θ}{γ : Sub Δ Γ}{δ : Sub Θ Δ} -> 
            reflect-con Γ (γ ∘ δ) ≡ 
                (reflect-cont (proj₁ Γ) (proj₁ γ I.∘t proj₁ δ)) ,Σ 
                reflect-conp (proj₂ Γ) (proj₁ γ I.∘t proj₁ δ) (substp (I.Subp (Δ .proj₂ I.[ δ .proj₁ ]C)) (sym [∘]C) ((proj₂ γ) [ proj₁ δ ]s) I.∘p (proj₂ δ))
        help' {◆t ,Σ Γ} {Δ} {Θ} {γ} {δ} = refl
        help' {(Γt ▸t) ,Σ Γ} {Δ} {Θ} {γ} {δ} = mk,sp= refl
        
        
        {-
        reify : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γ : Sub (Δt ,Σ Δ) (Γt ,Σ Γ)}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt (proj₁ γ)) -> I.Pf Δ (A I.[ proj₁ γ ]F)
        reify ⊤ x = {!   !}
        reify (A ⊃ B) x = {!   !}
        reify (A ∧ B) x = {!   !}
        reify (∀' A) x = {!   !}
        reify (Eq t t') x = {!   !}
        reify (rel n a ts) x = {!   !}

        reflect : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γ : Sub (Δt ,Σ Δ) (Γt ,Σ Γ)}(A : I.For Γt) -> (PfA : I.Pf Δ (A I.[ proj₁ γ ]F)) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt (proj₁ γ))
        reflect ⊤ x = *
        reflect {Γt} {Δt} {Γ} {Δ} γ@{γt ,Σ γp} (A ⊃ B) x (Θt ,Σ Θ) δ@(δt ,Σ δp) PfA = 
            let PfA = (I.qp I.[ I.idp I.,p {! reify A  !} ]P) in
            {! reflect {Γt}{Δt}{Γ}{Δ}{γ} A  !}
        reflect (A ∧ B) x = {!   !}
        reflect (∀' A) x = {!   !}
        reflect (Eq t t') x = {!   !}
        reflect (rel n a ts) x = {!   !}
        -}

        --lemma : ∀{Γ A} -> ⟦ proj₁ Γ ⟧Cont ∶ reflect-cont (proj₁ Γ) I.idt ⟨ (pp' {Γ} {A}) ⟩ ≡ reflect-cont (proj₁ Γ) I.idt
        --lemma {◆t ,Σ Γp} {A} = refl
        --lemma Γ@{(Γt ▸t) ,Σ Γp} {A} = mk,= {! trans ?   !} refl

        {-
        reify' : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Γt ,Σ Γ) (reflect-cont Γt I.idt) -> I.Pf Γ A
        reify' ⊤ x = I.tt
        reify' {Γt}{Γ} (A ⊃ B) x = 
            let a = reflect' A (qp' {Γt ,Σ Γ}) in
            let p = x ((Γt ,Σ Γ) ▸p' A) pp' {!   !} in
            I.⊃intro (reify' B {!   !})
        reify' (A ∧ B) x = {!   !}
        reify' (∀' A) x = {!   !}
        reify' (Eq t t') x = {!   !}
        reify' (rel n a ts) x = {!   !}

        reflect' : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For Γt) -> I.Pf Γ A -> ∣ ⟦ A ⟧For ∣ (Γt ,Σ Γ) (reflect-cont Γt I.idt)
        reflect' A x = {!   !}
        -}
        

        {-
        reflect'' : ∀{Γt Δt}{Γ : I.ConPf Γt}{Δ : I.ConPf Δt}{γ : Sub (Δt ,Σ Δ) (Γt ,Σ Γ)}(A : I.For Γt) -> (PfA : I.Pf Γ A) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt (proj₁ γ))
        reflect'' {Γt} {Δt} {Γ} {Δ} {γt ,Σ γ} ⊤ x = *
        reflect'' {Γt} {Δt} {Γ} {Δ} γ@{γt ,Σ γp} (A ⊃ B) x (Θt ,Σ Θ) δ@(δt ,Σ δp) PfA = 
            {! reflect'' {Γt}{Θt}{Γ}{Θ}{γ ∘ δ} B ?  !}
        reflect'' {Γt} {Δt} {Γ} {Δ} {γt ,Σ γ} (A ∧ A₁) x = {!   !}
        reflect'' {Γt} {Δt} {Γ} {Δ} {γt ,Σ γ} (∀' A) x (Θt ,Σ Θ) δ@(δt ,Σ δp) d = 
            let h = ((I.∀elim x) I.[ {!   !} ]p) I.[ {!   !} ]P in
            {! reflect'' {Γt I.▸t}{Θt}{Γ I.[ I.pt ]C}{Θ} A  !}
        reflect'' {Γt} {Δt} {Γ} {Δ} {γt ,Σ γ} (Eq x₁ x₂) x = {!   !}
        reflect'' {Γt} {Δt} {Γ} {Δ} {γt ,Σ γ} (rel zero x₁ *) x = (x I.[ γt ]p) I.[ γ ]P
        reflect'' {Γt} {Δt} {Γ} {Δ} {γt ,Σ γ} (rel (suc n) x₁ x₂) x = {!   !}
        -}
        
        {-

    completeness : ∀{Γt}{Γ} -> (A : I.For Γt) -> K.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For -> I.Pf Γ A
    completeness {Γt}{Γ} A p = substp (I.Pf Γ) [id]F (reify' {Γt}{Γt}{Γ}{Γ} A (∣ p ∣ (reflect-conp Γ I.idt (substp (I.Subp Γ) (sym [id]C) I.idp)))) -- reify A (∣ p ∣ (reflect-conp Γ I.idp)) -- reify A (∣ p ∣ (reflect-conp Γ I.idp))
    
    soundness : ∀{Γt Γ} -> (A : I.For Γt) -> I.Pf Γ A -> K.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For
    soundness A = ⟦_⟧Pf
        -}

{-      
        -- previous
        reify   : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Γt ,Σ Γ) (reflect-cont Γt I.idt) -> I.Pf Γ A
        reflect : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For Γt) -> I.Pf Γ A -> ∣ ⟦ A ⟧For ∣ (Γt ,Σ Γ) (reflect-cont Γt I.idt)

        reify ⊤ x = I.tt
        reify {Γt}{Γ} (A ⊃ B) x = 
            I.⊃intro 
            (reify B 
            (substp (∣ ⟦ B ⟧For ∣ (Γt ,Σ (Γ I.▸p A))) {! ⟦ Γt ⟧Cont ∶⟨id⟩  !} (x (Γt ,Σ (Γ I.▸p A)) (I.idt ,Σ substp (I.Subp (Γ I.▸p A)) (sym [id]C) (I.pp)) ({! reflect A I.qp  !}))))
        reify (A ∧ B) x = I.∧intro (reify A (proj₁ x)) (reify B (proj₂ x))
        reify (∀' A) x = {!   !}
        reify (Eq t t') x = {!    !}
        reify (rel zero a *) x = x
        reify {Γt}{Γ} (rel (suc n) a (ts ,Σ t)) x = 
            substp (λ z -> I.Pf Γ (rel (suc n) a z)) 
            {!   !} -- (mk,= isoTms isoTm) 
            x
        
        reflect-Eq : ∀{Γt Γ}{t t' : I.Tm Γt} -> ∣ ⟦ I.Eq t t' ⟧For ∣ (Γt ,Σ Γ) (reflect-cont {Γt} Γt I.idt) -> t ≡ t'
        reflect-Eq {Γt} {Γ} {t}{t'} x = {!   !}

        reflect ⊤ x = *
        reflect {Γt}{Γ} (A ⊃ B) x (Δt ,Σ Δ) (γt ,Σ γ) PfA = let h = ⟦ A ⟧For ∶ PfA ⟨ {!   !} ⟩ in 
            ⟦ B ⟧For ∶ (reflect B ((I.⊃elim x) I.[ I.idp I.,p reify A {! h  !} ]P)) ⟨ γt ,Σ γ ⟩
        reflect (A ∧ B) x = (reflect A (I.∧elim₁ x)) ,Σ (reflect B (I.∧elim₂ x))
        reflect (∀' A) x = {!   !}
        reflect {Γt}{Γ} (Eq t t') x = {!   !} -- trans (isoTm {Γt}{Γ}{t}) (trans {!  reflect (I.Eq t t') x !} (sym (isoTm {Γt}{Γ}{t'})))
        reflect (rel zero a *) x = x
        reflect {Γt}{Γ} (rel (suc n) a (ts ,Σ t)) x = 
            substp (I.Pf Γ) 
            {!   !} -- (cong (rel (suc n) a) (mk,= (sym isoTms) (sym isoTm))) 
            x
-}


{-
    -- Kinda close?
    module K = Semantics 
        C 
        I.Tm 
        (λ t γt -> t I.[ γt ]t)
        (λ {Γt}{Δt}{Θt}{t}{f}{g} -> I.[∘]t {Γt}{t}{Δt}{f}{Θt}{g})
        (λ {Γt}{t} -> I.[id]t {Γt}{t})
        (λ n a Γt ts → I.Pf ◆p (rel n a (reifyTms ts)))
        -- substp (λ z -> I.Pf ◆p (rel n a z)) ? (Pfrel [ γ ]p)
        (λ {n}{a} Pfrel γ -> substp (λ z -> I.Pf ◆p (rel n a z)) (sym ⟨reifyTms⟩) (Pfrel [ γ ]p))
        (λ n a Γt ts → fun n a (reifyTms ts))
        (λ n a Γt Δt ds γ → cong (fun n a) (sym ⟨reifyTms⟩))
    open K
    open import FirstOrderLogic.IntNegative.Iterator
    open Ite funar relar Kripke

    reflect-cont : ∀{Γt Δt} -> I.Subt Γt Δt -> (∣ ⟦ Δt ⟧Cont ∣) Γt
    reflect-conp : ∀{Γt}{Γ : I.ConPf Γt} -> (Δ : I.ConPf Γt) -> I.Subp Γ Δ -> ∣ ⟦ Δ ⟧Conp ∣ Γt (reflect-cont {Γt} I.idt)
    reify   : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ Γt (reflect-cont {Γt}{Γt} I.idt) -> I.Pf Γ A
    reflect : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For Γt) -> I.Pf Γ A -> ∣ ⟦ A ⟧For ∣ Γt (reflect-cont {Γt}{Γt} I.idt)
    
    reflect-cont {Γt} {Δt} εt = *
    reflect-cont {Γt} {Δt} (γt ,t t) = reflect-cont γt ,Σ t

    reify ⊤ x = I.tt
    reify (A ⊃ B) x = {!   !}
    reify (A ∧ B) x = I.∧intro (reify A (proj₁ x)) (reify B (proj₂ x))
    reify (∀' A) x = {!   !}
    reify (Eq t t') x = {!   !}
    reify (rel zero a ts) x = x I.[ I.εp ]P
    reify (rel (suc n) a (ts ,Σ t)) x = {!   !}
    
    reflect ⊤ x = *
    reflect (A ⊃ B) x = {!   !}
    reflect (A ∧ B) x = (reflect A (I.∧elim₁ x)) ,Σ (reflect B (I.∧elim₂ x))
    reflect (∀' A) x = {!   !}
    reflect (Eq t t') x = {!   !}
    reflect (rel zero a ts) x = x I.[ {!   !} ]P
    reflect (rel (suc n) a ts) x = {!   !}

    reflect-conp ◆p γ = *
    reflect-conp {Γt}{Γ} (Δ ▸p K) γ = (reflect-conp Δ ((I.pp I.∘p γ))) ,Σ reflect K (I.qp I.[ γ ]P)

    completeness : ∀{Γt}{Γ} -> (A : I.For Γt) -> K.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For -> I.Pf Γ A
    completeness {Γt}{Γ} A p = reify A (∣ p ∣ (reflect-conp Γ I.idp))
    
    soundness : ∀{Γt Γ} -> (A : I.For Γt) -> I.Pf Γ A -> K.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For
    soundness A = ⟦_⟧Pf
-}

{-
    postulate
      relS  : (n : ℕ) → relar n → D ^ n → I.ConTm → Prop
      ⟨relS⟩ : ∀{n i ds I J} → relS n i ds I → I.Subt J I → relS n i ds J
      funS  : (n : ℕ) → funar n → D ^ n → D
    
    _▸ts_ : I.ConTm -> ℕ -> I.ConTm
    Γt ▸ts zero = Γt
    Γt ▸ts (suc n) = (Γt ▸ts n) ▸t

    reify-Tms : ∀{n} -> (Γt : I.ConTm) -> D ^ n -> I.Tms (Γt ▸ts n) n
    reify-Tms {zero} Γt x = *
    reify-Tms {suc n} Γt (_ ,Σ ds) = (reify-Tms {n} Γt ds I.[ I.pt ]ts) ,Σ I.qt

    _↑t : ∀{Γt Δt} -> Subt Δt Γt -> Subt (Δt ▸t) (Γt ▸t)
    γt ↑t = γt ∘t pt ,t qt

    _↑t_ : ∀{Γt Δt} -> Subt Δt Γt -> (n : ℕ) -> Subt (Δt ▸ts n) (Γt ▸ts n)
    γt ↑t zero = γt
    γt ↑t suc n = (γt ↑t n) ↑t

    ⟨reify-Tms⟩ : ∀{n a I J ds} -> Pf ◆p (I.rel n a (reify-Tms I ds)) -> I.Subt J I -> Pf ◆p (I.rel n a (reify-Tms J ds))
    ⟨reify-Tms⟩ {zero} {a} {I} {J} {ds} Pfrel γ = Pfrel [ γ ]p
    ⟨reify-Tms⟩ {suc n} {a} {I} {J} {ds} Pfrel γ = 
        substp (Pf ◆p) (cong (rel (suc n) a) (mk,= (trans (sym [∘]ts) {!   !}) refl)) 
        (Pfrel [ γ ↑t (suc n) ]p)
    {-
    open Semantics C D (λ n a ds Γt → Pf ◆p (I.rel n a (reify-Tms Γt ds))) (λ PfDs γt → {!   !}) funS

--    open Semantics C D relS ⟨relS⟩ funS 

    open import FirstOrderLogic.IntNegative.Iterator
    open Ite funar relar Kripke

    reflect-cont : ∀{Γt} Δt -> I.Subt Γt Δt -> ∣ ⟦ Δt ⟧Cont ∣ Γt
    reflect-conp : ∀{Γt}{Γ : I.ConPf Γt} -> (Δ : I.ConPf Γt) -> I.Subp Γ Δ -> ∣ ⟦ Δ ⟧Conp ∣ Γt (reflect-cont Γt I.idt)
    
    reify   : ∀{Γt Δt Γ}{γt : I.Subt Δt Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ Δt (reflect-cont Γt γt) -> I.Pf Γ A
    reflect : ∀{Γt Δt Γ}{γt : I.Subt Δt Γt}(A : I.For Γt) -> I.Pf Γ A -> ∣ ⟦ A ⟧For ∣ Δt (reflect-cont Γt γt)

    reflect-cont ◆t             I.εt = *
    reflect-cont (Δt ▸t) (γt I.,t t) = (reflect-cont Δt γt) ,Σ {!   !}


{-
    reflect-cont : ∀{Γt} Δt -> I.Subt Γt Δt -> ∣ ⟦ Δt ⟧Cont ∣ Γt
    reflect-conp : ∀{Γt}{Γ : I.ConPf Γt} -> (Δ : I.ConPf Γt) -> I.Subp Γ Δ -> ∣ ⟦ Δ ⟧Conp ∣ Γt (reflect-cont Γt I.idt)
    reflect-Tm   : ∀{Γt} -> (t : I.Tm Γt) -> D
-- Reflect terms?
-- Or dont need to reflect cont?    
    reify   : ∀{Γt Γ}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ Γt (reflect-cont Γt I.idt) -> I.Pf Γ A
    reify-∀ : ∀{Γt Γ}(A : I.For (Γt I.▸t)) -> ∣ ⟦ I.∀' A ⟧For ∣ Γt ((reflect-cont Γt I.idt)) -> I.Pf Γ (I.∀' A)
    reflect : ∀{Γt Γ}(A : I.For Γt) -> I.Pf Γ A -> ∣ ⟦ A ⟧For ∣ Γt (reflect-cont Γt I.idt)

    reflect-Tm {Γt} t = ∣ ⟦ t ⟧Tm ∣ Γt (reflect-cont Γt I.idt)
    reflect-conp ◆p       γ = *
    reflect-conp (Δ ▸p K) γ = (reflect-conp Δ (I.pp I.∘p γ)) ,Σ reflect K (I.qp I.[ γ ]P )

    reflect-cont ◆t           I.εt      = *
    reflect-cont {Γt} (Δt ▸t) (γt ,t t) = (reflect-cont Δt γt) ,Σ {!   !}

    reify ⊤ x = I.tt
    reify {Γt} (A ⊃ B) PfAB = I.⊃intro (reify B (substp (∣ ⟦ B ⟧For ∣ Γt) {!   !} (PfAB Γt {!   !} {! reflect A I.qp  !})))
    reify (A ∧ B) (PfA ,Σ PfB) = I.∧intro (reify A PfA) (reify B PfB)
    reify (∀' A) x = I.∀intro (reify A {! x  !})
    reify (Eq t t') x = {!   !}
    reify (rel n a ts) x = {!  !}
    
    reify-∀ A x = I.∀intro (reify A {! ⟦ A ⟧For ∶ (x ?) ⟨ ? ⟩   !}) -- (reify A {!   !})
    -- I.Pf (Γ I.[ I.pt ]C) A
    -- ? : ∣ ⟦ A      ⟧For ∣ (Γt I.▸t) (reflect-cont pt ,Σ ?4 )
    -- x : ∣ ⟦ I.∀' A ⟧For ∣ Γt        (reflect-cont Γt I.idt)
    -- ⟦ A ⟧For ∶ (x ?) ⟨ ? ⟩ :  ⟦ A ⟧For ∣ ? ((⟦ Γt ⟧Cont ∶ reflect-cont Γt I.idt ⟨ ? ⟩) ,Σ ?)

    reflect ⊤ x = *
    reflect {Γt}{Γ} (A ⊃ B) x = λ J f PfA → (⟦ B ⟧For) ∶ (reflect B ((I.⊃elim x))) ⟨ f ⟩
    reflect (A ∧ B) x = (reflect A (I.∧elim₁ x)) ,Σ (reflect B (I.∧elim₂ x))
    reflect (∀' A) x = λ d → {!   !}
    reflect (Eq t t') x = {!   !}
    reflect (rel n a ts) x = {! x  !} -- x

-} 
    -}-}                                                                                                                                                                                             