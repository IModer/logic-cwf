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

    ⊥ : {Γt : Cont} → For Γt
    ∣ ⊥ ∣ I x = 𝟘p
    ⊥ ∶ x ⟨ f ⟩ = x

    exfalso : {Γt : Cont} {K : For Γt} {Γ : Conp Γt} → Pf Γ ⊥ → Pf Γ K
    ∣ exfalso x ∣ Γi = ind𝟘p (∣ x ∣ Γi)

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

    ∃' : {Γt : Cont} → For (Γt ▸t) → For Γt
    ∣ ∃' {Γt} K ∣ I Γi = ∃ (D I) λ d -> ∣ K ∣ I (Γi ,Σ d)
    ∃' K ∶ d ,∃ x ⟨ f ⟩ = D∶ d ⟨ f ⟩ ,∃ K ∶ x ⟨ f ⟩
    
    ∃intro : {Γt : Cont} {K : For (Γt ▸t)} (t : Tm Γt) {Γ : Conp Γt} →
      Pf Γ (K [ idt ,t t ]F) → Pf Γ (∃' K)
    ∣ ∃intro {Γt}{K} t {Γ} PfK ∣ {I}{i} Γi = (∣ t ∣ I i) ,∃ (∣ PfK ∣ Γi)
    
    ∃elim : {Γt : Cont} {K : For (Γt ▸t)} {Γp : Conp Γt}{L : For Γt} ->
      Pf Γp (∃' K) → Pf ((Γp [ pt ]C) ▸p (K [ _,t_ {Γt} pt (qt {Γt}) ]F)) (L [ pt ]F) → Pf Γp L
    ∣ ∃elim {Γt}{K}{Γp}{L} Pf∃K PfKL ∣ {I} {i} Γi = 
        with∃ (∣ Pf∃K ∣ Γi) 
        λ d Ki → ∣ PfKL ∣ (Γi ,Σ Ki) 

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
        ; ⊥ = ⊥
        ; ⊥[] = refl
        ; exfalso = exfalso
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
        ; _∨_ = _∨_
        ; ∨[] = refl
        ; ∨elim = λ {Γt}{K}{L}{C} -> ∨elim {Γt}{K}{L}{C}
        ; ∨intro₁ = λ {Γt}{K}{L} -> ∨intro₁ {Γt}{K}{L}
        ; ∨intro₂ = λ {Γt}{K}{L} -> ∨intro₂ {Γt}{K}{L}
        ; ∀' = ∀'
        ; ∀[] = λ {Γt}{K}{Δt}{γt} → ∀[] {Γt}{K}{Δt}{γt}
        ; ∀intro = λ {Γt}{K}{Γ} -> ∀intro {Γt}{K}{Γ} 
        ; ∀elim = λ {Γt}{K}{Γ} -> ∀elim {Γt}{K}{Γ}
        ; ∃' = ∃'
        ; ∃[] = refl
        ; ∃intro = λ {Γt}{K} -> ∃intro {Γt}{K}
        ; ∃elim = λ {Γt}{K}{Γp}{L} -> ∃elim {Γt}{K}{Γp}{L} 
        ; Eq = Eq
        ; Eq[] = refl
        ; Eqrefl = λ {Γt}{t}{Γ} -> Eqrefl {Γt}{t}{Γ}
        ; subst' = subst'
        }