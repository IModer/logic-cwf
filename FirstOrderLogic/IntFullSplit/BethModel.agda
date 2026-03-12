{-# OPTIONS --prop #-}

open import lib
open import FirstOrderLogic.IntFullSplit.Model

module FirstOrderLogic.IntFullSplit.BethModel
    (funar : ℕ -> Set)
    (relar : ℕ -> Set)
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

module Sh (C : Category) where
    open Category C

    record Sieve(I : Ob) : Set₁ where
        constructor mkSieve
        field
            R     : (J : Ob) -> (f : Hom J I) -> Prop
            restr : ∀{J f K} -> R J f -> (g : Hom K J) -> R K (f ∘C g)
    open Sieve renaming (R to ∣_∣)

    mkSieveEq : ∀{I : Ob} -> (R R' : (J : Ob) -> (f : Hom J I) -> Prop) 
        {restr  : ∀{J f K} -> R  J f -> (g : Hom K J) -> R  K (f ∘C g)} -> 
        {restr' : ∀{J f K} -> R' J f -> (g : Hom K J) -> R' K (f ∘C g)} ->
        R ≡ R' -> 
        mkSieve R restr ≡ mkSieve R' restr' 
    mkSieveEq R R' refl = refl

    infix 0 ⟨_,_⟩⊩_
    ⟨_,_⟩⊩_ : ∀ {I} J → Hom J I → Sieve I → Prop
    ⟨ J , f ⟩⊩ R = ∣ R ∣ J f

    _[_]ˢ : ∀{I J : Ob} -> Sieve I -> (Hom J I) -> Sieve J
    ∣ R [ f ]ˢ ∣ K g = ∣ R ∣ K (f ∘C g)
    restr (R [ f ]ˢ) {J} {g} {K} Rk h = substp (∣ R ∣ K) assC (restr R Rk h)

    record Top : Set₁ where
        infix 4 _◁_
        infixl 9 _[_]ᶜ
        field
            _◁_     : (I : Ob) -> Sieve I -> Prop
            _[_]ᶜ   : ∀ {I J R} -> I ◁ R -> (f : Hom J I) -> J ◁ (R [ f ]ˢ)
            maximal : ∀{I R} -> ∣ R ∣ I idC -> I ◁ R
            local   : ∀{I R S} -> I ◁ R -> (∀{J} -> (f : Hom J I) -> ∣ R ∣ J f  -> J ◁ (S [ f ]ˢ)) -> I ◁ S

    record Sheaf (J : Top) : Set₁ where
        
        open Top J
        
        field
            A     : Ob -> Set
            _⟨_⟩  : ∀{I J} -> A I -> Hom J I -> A J
            ⟨id⟩  : ∀{I : Ob}{a : A I} -> a ⟨ idC ⟩ ≡ a
            ⟨∘⟩   : ∀{I J K : Ob}{a : A I}{f : Hom J I}{g : Hom K J} -> (a ⟨ f ⟩) ⟨ g ⟩ ≡ a ⟨ f ∘C g ⟩
            glue  : ∀{I R} -> I ◁ R -> (∀{J} -> (f : Hom J I) -> ∣ R ∣ J f -> A J) -> A I
    open Sheaf renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩; ⟨id⟩ to _∶⟨id⟩; ⟨∘⟩ to _∶⟨∘⟩)

module Semantics
    (C : Category)
    (open Category C)
    (open Sh C)
    (J : Top)
    (open Top J)
    (D : Ob -> Set)
    (D∶_⟨_⟩ : ∀{I J} -> D I -> Hom J I -> D J)
    (D∶⟨∘⟩  : ∀{I J K}{a : D I}{f : Hom J I}{g : Hom K J} -> D∶ a ⟨ f ∘C g ⟩ ≡ D∶ D∶ a ⟨ f ⟩ ⟨ g ⟩)
    (D∶⟨id⟩ : ∀{I}{a : D I} -> D∶ a ⟨ idC ⟩ ≡ a)
    -- ? Helyett valami más kéne
    --(Dglue  : ∀{I : Ob}{R : Sieve I} -> I ◁ R -> (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R  -> D J) -> D I)
    (rel  : (n : ℕ) -> relar n -> (I : Ob) -> (D I) ^ n -> Prop)
    -- ?
    --(relGlue : ∀ (n : ℕ)(a : relar n)(I : Ob)(ts : (D I) ^ n)(R : Sieve I) -> (I ◁ R) -> ({J : Ob} (f : Hom J I) -> ⟨ J , f ⟩⊩ R → rel n a J ((map^ ts (D∶_⟨ f ⟩)))) -> rel n a I ts)
    (⟨rel⟩ : ∀{n i I J ds} -> rel n i I ds -> (f : Hom J I) -> rel n i J (map^ ds (D∶_⟨ f ⟩)))
    (fun  : (n : ℕ) -> funar n -> (I : Ob) -> (D I) ^ n -> (D I))
    (⟨fun⟩ : ∀(n : ℕ)(a : funar n)(I J : Ob)(ds : (D I) ^ n)(f : Hom J I) -> (D∶ (fun n a I ds) ⟨ f ⟩) ≡ (fun n a J (map^ ds (D∶_⟨ f ⟩))) )
    where

    --open Top J
    record Cont : Set₁ where
        constructor mk
        field
            A    : Ob -> Set
            _⟨_⟩ : ∀{I J} -> A I -> Hom J I -> A J
            ⟨id⟩ : ∀{I}{a : A I} -> a ⟨ idC ⟩ ≡ a
            ⟨∘⟩  : ∀{I J K}{a : A I}{g : Hom K J}{f : Hom J I} -> a ⟨ f ∘C g ⟩ ≡ (a ⟨ f ⟩) ⟨ g ⟩
            --glue  : ∀{I R} -> I ◁ R -> (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R  -> A J) -> A I
    open Cont public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩; ⟨id⟩ to _∶⟨id⟩; ⟨∘⟩ to _∶⟨∘⟩)

    record Subt(Δ Γ : Cont) : Set where
        constructor mk
        field
            α   : ∀(I : Ob) -> ∣ Δ ∣ I -> ∣ Γ ∣ I
            nat : ∀{I J : Ob}{a : ∣ Δ ∣ I}{f : Hom J I} -> (Γ ∶ (α I a) ⟨ f ⟩) ≡ α J (Δ ∶ a ⟨ f ⟩)
    open Subt public renaming (α to ∣_∣)
    
    _∘t_ : {Γ Δ Θ : Cont} -> Subt Δ Γ -> Subt Θ Δ -> Subt Θ Γ
    ∣ γ ∘t δ ∣ I θi = ∣ γ ∣ I (∣ δ ∣ I θi)
    nat (γ ∘t δ) {I}{J} = trans (nat γ) (cong (∣ γ ∣ J) (nat δ))

    idt : {Γ : Cont} -> Subt Γ Γ
    ∣ idt ∣ = λ I z -> z
    nat idt = refl

    ◆t : Cont 
    ∣ ◆t ∣ I = 𝟙
    ◆t ∶ x ⟨ f ⟩ = *
    ◆t ∶⟨id⟩ = refl
    ◆t ∶⟨∘⟩ = refl
    --glue ◆t = λ _ _ → *

    εt : {Γ : Cont} -> Subt Γ ◆t
    ∣ εt ∣ = λ I x -> *
    nat εt = refl

    record For(Γ : Cont) : Set₁ where

        constructor mk

        field
            A    : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> A I i -> (f : Hom J I) -> A J (Γ ∶ i ⟨ f ⟩)
            glue : ∀{I : Ob}{i : ∣ Γ ∣ I}{R : Sieve I} -> I ◁ R -> (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R -> A J (Γ ∶ i ⟨ f ⟩)) -> A I i
    open For public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)

    _[_]F : ∀{Γ Δ} -> For Γ -> Subt Δ Γ -> For Δ
    ∣ A [ γt ]F ∣ I x = ∣ A ∣ I (∣ γt ∣ I x)
    _∶_⟨_⟩ (A [ γt ]F) {I} {J} {i} x f = substp (∣ A ∣ J) (nat γt) (A ∶ x ⟨ f ⟩)
    glue (_[_]F {Γ}{Δ} A γt) {I} {i} {R} Ri f = 
        glue A Ri λ {J} g J⊩R -> 
        substp (∣ A ∣ J) (sym (nat γt)) (f {J} g J⊩R)

    DPSh : Cont
    ∣ DPSh ∣ I     = D I
    DPSh ∶ d ⟨ f ⟩ = D∶ d ⟨ f ⟩
    DPSh ∶⟨∘⟩      = D∶⟨∘⟩
    DPSh ∶⟨id⟩     = D∶⟨id⟩

    Tm : Cont -> Set
    Tm Γ = Subt Γ DPSh

    _[_]t : {Γ : Cont} -> Tm Γ -> {Δ : Cont} -> Subt Δ Γ -> Tm Δ
    ∣ t [ γt ]t ∣ I x = ∣ t ∣ I (∣ γt ∣ I x)
    nat (t [ γt ]t) {I}{J} = trans (nat t) (cong (∣ t ∣ J) (nat γt))

    _▸t : Cont -> Cont
    ∣ Γ ▸t ∣ I = ∣ Γ ∣ I × D I
    (Γ ▸t) ∶ (i ,Σ d) ⟨ f ⟩ = (Γ ∶ i ⟨ f ⟩) ,Σ (D∶ d ⟨ f ⟩)
    (Γ ▸t) ∶⟨id⟩ = mk,= (Γ ∶⟨id⟩) D∶⟨id⟩
    (Γ ▸t) ∶⟨∘⟩ = mk,= (Γ ∶⟨∘⟩) D∶⟨∘⟩

    _,t_ : {Γ Δ : Cont} -> Subt Δ Γ -> Tm Δ -> Subt Δ (Γ ▸t)
    ∣ γt ,t t ∣ I x = (∣ γt ∣ I x) ,Σ (∣ t ∣ I x)
    nat (γt ,t t) = mk,= (nat γt) (nat t)

    pt : {Γ : Cont} -> Subt (Γ ▸t) Γ
    ∣ pt ∣ I x = proj₁ x
    nat pt     = refl

    qt : {Γ : Cont} -> Tm (Γ ▸t)
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

    _[_]ts : ∀{Γ n} -> Tms Γ n -> ∀{Δ} -> Subt Δ Γ -> Tms Δ n
    ∣ ts [ γt ]ts ∣ I Δi = ∣ ts ∣ I (∣ γt ∣ I Δi)
    nat (ts [ γt ]ts) {I}{J} = trans (nat ts) (cong (∣ ts ∣ J) (nat γt))
    
    εs : ∀{Γ} -> Tms Γ zero
    ∣ εs ∣ I x = *
    nat εs     = refl

    ◆sη    : ∀{Γ}(ts : Tms Γ zero) -> ts ≡ εs
    ◆sη ts = refl
    
    _,s_ : ∀{Γ n} -> Tms Γ n -> Tm Γ -> Tms Γ (suc n)
    ∣ ts ,s t ∣ I x = (∣ ts ∣ I x) ,Σ (∣ t ∣ I x)
    (ts ,s t) .nat = mk,= (ts .nat) (t .nat)
    
    π₁ : ∀{Γ n} -> Tms Γ (suc n) -> Tms Γ n
    ∣ π₁ ts ∣ I x = proj₁ (∣ ts ∣ I x)
    nat (π₁ ts) = (cong proj₁ (nat ts))

    π₂ : ∀{Γ n} -> Tms Γ (suc n) -> Tm Γ
    ∣ π₂ ts ∣ I x = proj₂ (∣ ts ∣ I x)
    nat (π₂ ts) = (cong proj₂ (nat ts))

    recTms : ∀{n} -> (I : Ob) -> ∣ DPShV n ∣ I -> (D I) ^ n
    recTms {zero } I ts = *
    recTms {suc n} I (ts ,Σ d) = d ,Σ recTms I ts
    
    ⟨recTms⟩ : ∀{n I J}{f : Hom J I}{ts : ∣ DPShV n ∣ I} -> map^ (recTms {n} I ts) (D∶_⟨ f ⟩) ≡ recTms J ((DPShV n) ∶ ts ⟨ f ⟩)
    ⟨recTms⟩ {zero} {I} {J} {f} {ts} = refl
    ⟨recTms⟩ {suc n} {I} {J} {f} {ts} = mk,= refl ⟨recTms⟩

    fun' : {Γ : Cont} (n : ℕ) -> funar n -> Tms Γ n -> Tm Γ
    ∣ fun' n a ts ∣ I x = fun n a I (recTms I (∣ ts ∣ I x)) -- fun n a (recTms I (∣ ts ∣ I x))
    nat (fun' n a ts) {I}{J}{i}{f} = trans (⟨fun⟩ n a I J (recTms I (∣ ts ∣ I i)) f) (cong (fun n a J) (trans (⟨recTms⟩ {n} {I} {J} {f} {∣ ts ∣ I i}) (cong (recTms J) (nat ts)))) -- cong (fun n a) (trans ⟨recTms⟩ (cong (recTms J) (nat ts)))

    --rel' : {Γ : Cont} (n : ℕ) -> relar n -> Tms Γ n -> For Γ
    --∣ rel' n a ts ∣ I x = rel n a I (recTms I (∣ ts ∣ I x))
    --_∶_⟨_⟩ (rel' n a ts) {I} {J} {i} x f = substp (rel n a J) (trans ⟨recTms⟩ (cong (recTms J) (nat ts))) (⟨rel⟩ {n}{a}{I}{J}{recTms I (∣ ts ∣ I i)} x f)
    --glue (rel' n a ts) {I} {i} {R} I◁R x = 
    --    relGlue n a I (recTms {n} I (∣ ts ∣ I i)) R I◁R λ {J} f y -> 
    --    substp (rel n a J) (trans (cong (recTms J) (sym (nat ts))) (sym (⟨recTms⟩ {n}{I}{J}{f}{∣ ts ∣ I i}))) (x {J} f y)

    rel-sieve : (Γt : Cont) -> (n : ℕ) -> (relar n) -> (ts : Tms Γt n) -> (I : Ob) -> (∣ Γt ∣ I) -> Sieve I
    rel-sieve Γt n a ts I i .Sh.Sieve.R J f = rel n a J (recTms J (∣ ts ∣ J (Γt ∶ i ⟨ f ⟩)))
    rel-sieve Γt n a ts I i .Sh.Sieve.restr {J} {f} {K} r g = 
        substp (rel n a K) (trans ⟨recTms⟩ (cong (recTms K) (trans (nat ts) (cong (∣ ts ∣ K) (sym (Γt ∶⟨∘⟩)))))) (⟨rel⟩ r g)

    rel-[]ˢ-⟨⟩ : ∀{Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}{n : ℕ}{a : relar n}{ts : Tms Γt n} ->
        (rel-sieve Γt n a ts I Γi) [ f ]ˢ ≡ rel-sieve Γt n a ts J (Γt ∶ Γi ⟨ f ⟩)
    rel-[]ˢ-⟨⟩ {Γt} {I} {J} {Γi} {f} {n} {a} {ts} = 
        mkSieveEq {J}
        (Sh.Sieve.R ((rel-sieve Γt n a ts I Γi) [ f ]ˢ))
        (Sh.Sieve.R (rel-sieve Γt n a ts J (Γt ∶ Γi ⟨ f ⟩))) 
        {Sh.Sieve.restr ((rel-sieve Γt n a ts I Γi) [ f ]ˢ)}
        {Sh.Sieve.restr (rel-sieve Γt n a ts J (Γt ∶ Γi ⟨ f ⟩))}
        (funext (λ I' → funext (λ f' → 
        cong (λ z → rel n a I' (recTms I' (∣ ts ∣ I' z))) (Γt ∶⟨∘⟩))))

    rel' : {Γ : Cont} (n : ℕ) -> relar n -> Tms Γ n -> For Γ
    ∣ rel' {Γt} n a ts ∣ I i = I ◁ (rel-sieve Γt n a ts I i)
    _∶_⟨_⟩ (rel' {Γt} n a ts) {I} {J} {i} x f = substp (J ◁_) (rel-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {n} {a} {ts}) (x [ f ]ᶜ)
    rel' {Γt} n a ts .glue {I} {i} I◁R x = local I◁R (λ {J} f y → substp (J ◁_) (sym (rel-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {n} {a} {ts})) (x f y))

    record Conp(Γt : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γt ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γt ∣ I} -> A I i -> (f : Hom J I) -> A J (Γt ∶ i ⟨ f ⟩)
            glue : ∀{I : Ob}{i : ∣ Γt ∣ I}{R : Sieve I} -> I ◁ R -> (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R -> A J (Γt ∶ i ⟨ f ⟩)) -> A I i
    open Conp public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)
    
    _[_]C : ∀{Γt Δt} -> Conp Γt -> Subt Δt Γt -> Conp Δt
    ∣ Γ [ γt ]C ∣ I x = ∣ Γ ∣ I (∣ γt ∣ I x)
    _∶_⟨_⟩ (Γ [ γt ]C) {I} {J} x f = substp (∣ Γ ∣ J) (γt .nat) (Γ ∶ x ⟨ f ⟩)
    glue (_[_]C {Γt} {Δt} Γ γt) {I} {i} {R} I◁R f = 
        glue Γ I◁R (λ {J} g J⊩R → substp (∣ Γ ∣ J) (sym (nat γt)) (f {J} g J⊩R))
    
    record Subp{Γt : Cont}(Δ Γ : Conp Γt) : Prop where
        constructor mk
        field
            α   : ∀{I i} -> ∣ Δ ∣ I i -> ∣ Γ ∣ I i
    open Subp public renaming (α to ∣_∣)

    _∘p_ : {Γt : Cont} {Γ Δ Θ : Conp Γt} -> Subp Δ Γ -> Subp Θ Δ -> Subp Θ Γ
    ∣ γ ∘p δ ∣ θi = ∣ γ ∣ (∣ δ ∣ θi)

    idp : {Γt : Cont} {Γ : Conp Γt} -> Subp Γ Γ
    ∣ idp ∣ γi = γi

    ◆p : {Γt : Cont} -> Conp Γt
    ∣ ◆p ∣ I γi  = 𝟙p
    ◆p ∶ x ⟨ f ⟩ = *
    glue ◆p _ _  = *

    εp : {Γt : Cont} {Γ : Conp Γt} -> Subp Γ ◆p
    ∣ εp ∣ x = *

    record Pf{Γt : Cont}(Γ : Conp Γt)(K : For Γt) : Prop where
        constructor mk
        field
            α : ∀{I i} -> ∣ Γ ∣ I i -> ∣ K ∣ I i
    open Pf public renaming (α to ∣_∣)

    _[_]P : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} ->
      Pf Γ K -> {Δ : Conp Γt} -> Subp Δ Γ -> Pf Δ K
    ∣ PfK [ γ ]P ∣ Δi = ∣ PfK ∣ (∣ γ ∣ Δi)

    _[_]p : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} ->
      Pf Γ K -> {Δt : Cont} (γt : Subt Δt Γt) -> Pf (Γ [ γt ]C) (K [ γt ]F)
    ∣ PfK [ γt ]p ∣ Γi = ∣ PfK ∣ Γi

    _▸p_ : {Γt : Cont} -> Conp Γt -> For Γt -> Conp Γt
    ∣ Γ ▸p K ∣ I Γi    = ∣ Γ ∣ I Γi ×p ∣ K ∣ I Γi
    (Γ ▸p K) ∶ (Γi ,Σ Ki) ⟨ f ⟩ = (Γ ∶ Γi ⟨ f ⟩) ,Σ (K ∶ Ki ⟨ f ⟩)
    glue (Γ ▸p K) {I}{i}{R} I◁R f = 
        let glueΓ = glue Γ I◁R (λ {J} g J⊩R → proj₁ (f {J} g J⊩R)) in
        let glueK = glue K I◁R (λ {J} g J⊩R → proj₂ (f {J} g J⊩R)) in
        glueΓ ,Σ glueK

    _,p_ : {Γt : Cont} {Γ Δ : Conp Γt} ->
      Subp Δ Γ -> {K : For Γt} -> Pf Δ K -> Subp Δ (Γ ▸p K)
    ∣ γ ,p PfK ∣ Δi = (∣ γ ∣ Δi) ,Σ ∣ PfK ∣ Δi

    pp : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} -> Subp (Γ ▸p K) Γ
    ∣ pp ∣ x = proj₁ x

    qp : {Γt : Cont} {Γ : Conp Γt} {K : For Γt} -> Pf (Γ ▸p K) K
    ∣ qp ∣ x = proj₂ x

    ⊥ : {Γt : Cont} -> For Γt
    ∣ ⊥ ∣ I x = I ◁ sieve
        where
            sieve : Sieve I
            sieve .Sh.Sieve.R _ _ = 𝟘p
            sieve .Sh.Sieve.restr () g
    ⊥ ∶ x ⟨ f ⟩ = x [ f ]ᶜ
    glue ⊥ I◁R f = local I◁R f

    exfalso : {Γt : Cont} {K : For Γt} {Γ : Conp Γt} -> Pf Γ ⊥ -> Pf Γ K
    ∣ exfalso {Γt}{K} x ∣ Γi = K .glue (∣ x ∣ Γi) λ f ()

    ⊤ : {Γt : Cont} -> For Γt
    ∣ ⊤ ∣ I x = 𝟙p
    ⊤ ∶ x ⟨ f ⟩ = *
    glue ⊤ I◁R f = *

    tt : {Γt : Cont} {Γ : Conp Γt} -> Pf Γ ⊤
    ∣ tt ∣ _ = *

    _⊃_ : {Γt : Cont} -> For Γt -> For Γt -> For Γt
    ∣ _⊃_ {Γt} K L ∣ I x = (J : Ob) -> (f : Hom J I) -> ∣ K ∣ J (Γt ∶ x ⟨ f ⟩) -> ∣ L ∣ J (Γt ∶ x ⟨ f ⟩)
    (_∶_⟨_⟩ (_⊃_ {Γt} K L) {I}{J}{i}) = λ x f J' g Ki -> substp (∣ L ∣ J') (Γt ∶⟨∘⟩) (x J' (f ∘C g) (substp (∣ K ∣ J') (sym (Γt ∶⟨∘⟩)) Ki))
    glue (_⊃_ {Γt} K L) {I} I◁R x J f Kj = 
        L .glue (I◁R [ f ]ᶜ) (λ {K'} g J⊩R -> 
        let EQ  = substp (∣ L ∣ K') (trans (Γt ∶⟨id⟩) (Γt ∶⟨∘⟩)) in
        let EQ' = substp (∣ K ∣ K') (trans (sym (Γt ∶⟨∘⟩)) (sym (Γt ∶⟨id⟩))) in
        EQ (x {K'} (f ∘C g) J⊩R K' idC (EQ' (K ∶ Kj ⟨ g ⟩))))

    ⊃[] : {Γt : Cont} {K L : For Γt} {Δt : Cont} {γt : Subt Δt Γt} ->
      ((K ⊃ L) [ γt ]F) ≡ ((K [ γt ]F) ⊃ (L [ γt ]F))
    ⊃[] {Γt} {K} {L} {Δt} {γt} = {!   !}
    
    ⊃intro : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf (Γ ▸p K) L -> Pf Γ (K ⊃ L)
    ∣ ⊃intro {Γt}{K}{L}{Γ} PfKL ∣ Γi J f Kj = ∣ PfKL ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ Kj)

    ⊃elim : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ (K ⊃ L) -> Pf (Γ ▸p K) L
    ∣ ⊃elim {Γt}{K}{L}{Γ} PfKL ∣ {I}{i} (Γi ,Σ Ki) = substp (∣ L ∣ I) (Γt ∶⟨id⟩) (∣ PfKL ∣ Γi I idC (substp (∣ K ∣ I) (sym (Γt ∶⟨id⟩)) Ki))

    _∧_ : {Γt : Cont} -> For Γt -> For Γt -> For Γt
    ∣ K ∧ L ∣ I Γi    = ∣ K ∣ I Γi ×p ∣ L ∣ I Γi
    (K ∧ L) ∶ x ⟨ f ⟩ = (K ∶ x .proj₁ ⟨ f ⟩) ,Σ (L ∶ x .proj₂ ⟨ f ⟩)
    glue (K ∧ L) {I} I◁R x = 
        K .glue I◁R (λ {J} f J⊩R → x f J⊩R .proj₁) ,Σ 
        L .glue I◁R (λ {J} f J⊩R → x f J⊩R .proj₂)

    ∧intro : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ K -> Pf Γ L -> Pf Γ (K ∧ L)
    ∣ ∧intro PfK PfL ∣ Γi = (∣ PfK ∣ Γi) ,Σ (∣ PfL ∣ Γi)

    ∧elim₁ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} -> Pf Γ (K ∧ L) -> Pf Γ K
    ∣ ∧elim₁ x ∣ Γi = proj₁ (∣ x ∣ Γi)

    ∧elim₂ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} -> Pf Γ (K ∧ L) -> Pf Γ L
    ∣ ∧elim₂ x ∣ Γi = proj₂ (∣ x ∣ Γi)

    ∨-sieve : (Γt : Cont) -> (I : Ob) -> (Γi : ∣ Γt ∣ I) -> (K L : For Γt) -> Sieve I
    (∨-sieve Γt I Γi K L) .Sh.Sieve.R = λ J f -> ∣ K ∣ J (Γt ∶ Γi ⟨ f ⟩) +p ∣ L ∣ J (Γt ∶ Γi ⟨ f ⟩)
    (∨-sieve Γt I Γi K L) .Sh.Sieve.restr {J}{f}{K'} (inj₁ Kj) g = inj₁ (substp (∣ K ∣ K') (sym (Γt ∶⟨∘⟩)) (K ∶ Kj ⟨ g ⟩))
    (∨-sieve Γt I Γi K L) .Sh.Sieve.restr {J}{f}{K'} (inj₂ Lj) g = inj₂ (substp (∣ L ∣ K') (sym (Γt ∶⟨∘⟩)) (L ∶ Lj ⟨ g ⟩))
    
    ∨-[]ˢ-⟨⟩ : ∀{Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}{K L : For Γt} ->
        (∨-sieve Γt I Γi K L) [ f ]ˢ ≡  ∨-sieve Γt J (Γt ∶ Γi ⟨ f ⟩) K L
    ∨-[]ˢ-⟨⟩ {Γt} {I} {J} {Γi} {f} {K} {L} = 
        mkSieveEq {J}
        (Sh.Sieve.R (∨-sieve Γt I Γi K L [ f ]ˢ))
        (Sh.Sieve.R (∨-sieve Γt J (Γt ∶ Γi ⟨ f ⟩) K L)) 
        {Sh.Sieve.restr (∨-sieve Γt I Γi K L [ f ]ˢ)}
        {Sh.Sieve.restr (∨-sieve Γt J (Γt ∶ Γi ⟨ f ⟩) K L)}
        (funext (λ I' → funext (λ f' → cong-bin _+p_ (cong (∣ K ∣ I') (Γt ∶⟨∘⟩)) (cong (∣ L ∣ I') (Γt ∶⟨∘⟩))))) 

    _∨_ : {Γt : Cont} -> For Γt -> For Γt -> For Γt
    ∣ _∨_ {Γt} K L ∣ I Γi    = I ◁ (∨-sieve Γt I Γi K L)
    _∶_⟨_⟩ (_∨_ {Γt} K L) {I} {J} {i} x f = substp (J ◁_) (∨-[]ˢ-⟨⟩ {Γt}{I}{J}{i}{f}{K}{L}) (_[_]ᶜ {I}{J} x f)
    glue (_∨_ {Γt} K L) {I} {i} {R} I◁R x = local {I}{R} I◁R λ {J'} f J'⊩R → substp (J' ◁_) (sym (∨-[]ˢ-⟨⟩ {Γt}{I}{J'}{i}{f}{K}{L})) (x f J'⊩R)

    ∨intro₁ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ K -> Pf Γ (K ∨ L)
    ∣ ∨intro₁ {Γt} {K} {L} {Γ} PfK ∣ Γi = maximal (inj₁ (K ∶ ∣ PfK ∣ Γi ⟨ idC ⟩))
    
    ∨intro₂ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ L -> Pf Γ (K ∨ L)
    ∣ ∨intro₂ {Γt} {K} {L} {Γ} PfL ∣ Γi = maximal (inj₂ (L ∶ ∣ PfL ∣ Γi ⟨ idC ⟩))

    ∨elim : ∀{Γt}{K L C}{Γ : Conp Γt} -> Pf (Γ ▸p K) C -> Pf (Γ ▸p L) C -> Pf Γ (K ∨ L) -> Pf Γ C
    ∣ ∨elim {Γt}{K}{L}{C}{Γ} PfKC PfLC PfK∨L ∣ {I} {i} Γi = 
        C .glue (∣ PfK∨L ∣ Γi) 
        λ {J} f J⊩R → 
            ind+p 
            (λ v → ∣ C ∣ J (Γt ∶ i ⟨ f ⟩)) 
            (λ x → ∣ PfKC ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ x)) 
            (λ y → ∣ PfLC ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ y)) 
            J⊩R

    ∀' : {Γt : Cont} -> For (Γt ▸t) -> For Γt
    ∣ ∀' {Γt} K ∣ I Γi = (J : Ob) -> (f : Hom J I) -> (d : D J) -> ∣ K ∣ J ((Γt ∶ Γi ⟨ f ⟩) ,Σ d)
    _∶_⟨_⟩ (∀' {Γt} K) {I} {J} {i} x f J' g d = substp (λ z -> ∣ K ∣ J' (z ,Σ d)) (Γt ∶⟨∘⟩) (x J' (f ∘C g) d) 
    glue (∀' {Γt} K){I} {i} {R} I◁R x J f d = 
        K .glue {J}{Γt ∶ i ⟨ f ⟩ ,Σ d} 
        (I◁R [ f ]ᶜ) λ {K'} g y → substp (λ z -> ∣ K ∣ K' (z ,Σ D∶ d ⟨ g ⟩)) (trans (Γt ∶⟨id⟩) (Γt ∶⟨∘⟩)) 
        (x {K'} (f ∘C g) y K' idC D∶ d ⟨ g ⟩)

    ∀[] : {Γt : Cont} {K : For (Γt ▸t)} {Δt : Cont} {γt : Subt Δt Γt} ->
      (∀' K [ γt ]F) ≡ ∀' (K [ (γt ∘t pt) ,t qt {Δt} ]F)
    ∀[] {Γt} {K} {Δt} {γt} = {!   !}
    {-
      mkForEq 
      {Δt}{∣ ∀' K [ γt ]F ∣}{∣ ∀' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F) ∣}
      {λ {I}{J}{Δi} x f J' g d -> substp (λ z -> ∣ K ∣ J' (z ,Σ d)) (trans (Γt ∶⟨∘⟩) (cong (Γt ∶_⟨ g ⟩) (nat γt))) (x J' (f ∘C g) d)}
      {λ {I}{J}{Δi} x f J' g d -> substp (λ z -> ∣ K ∣ J' (∣ γt ∣ J' z ,Σ d)) (Δt ∶⟨∘⟩) (x J' (f ∘C g) d)}
      (funext (λ I -> 
      funext (λ Δi -> 
      cong (λ Z -> (J : Ob)(f : Hom J I)(d : D J) -> Z J f d) 
      (funext λ J -> funext (λ f -> funext (λ d -> cong (λ z -> ∣ K ∣ J (z ,Σ d)) (nat γt)))))))  
    -}

    ∀intro : {Γt : Cont} {K : For (Γt ▸t)} {Γ : Conp Γt} ->
      Pf (Γ [ pt ]C) K -> Pf Γ (∀' K)
    ∣ ∀intro {Γt}{K}{Γ} PfK ∣ Γi J f d = ∣ PfK ∣ (Γ ∶ Γi ⟨ f ⟩)

    ∀elim : {Γt : Cont} {K : For (Γt ▸t)} {Γ : Conp Γt} ->
      Pf Γ (∀' K) -> Pf (Γ [ pt ]C) K
    ∣ ∀elim {Γt}{K}{Γ} PfK ∣ {I} {Γti ,Σ d} Γi = substp (λ z -> ∣ K ∣ I (z ,Σ d)) (Γt ∶⟨id⟩) (∣ PfK ∣ Γi I idC d) -- ∣ PfK ∣ Γi d

    ∃-sieve : (Γt : Cont) -> (K : For (Γt ▸t)) -> (I : Ob) -> (Γi : ∣ Γt ∣ I) -> Sieve I
    ∃-sieve Γt K I Γi .Sh.Sieve.R = λ J f → ∃ (D J) λ d -> ∣ K ∣ J ((Γt ∶ Γi ⟨ f ⟩) ,Σ d)
    ∃-sieve Γt K I Γi .Sh.Sieve.restr {J} {f} {K'} (Dj ,∃ Kj) g = 
        D∶ Dj ⟨ g ⟩ ,∃ 
        substp (λ z -> ∣ K ∣ K' (z ,Σ D∶ Dj ⟨ g ⟩)) (sym (Γt ∶⟨∘⟩)) 
        (K ∶ Kj ⟨ g ⟩)

    ∃-[]ˢ-⟨⟩ : ∀{Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}{K : For (Γt ▸t)} ->
        (∃-sieve Γt K I Γi) [ f ]ˢ ≡  ∃-sieve Γt K J (Γt ∶ Γi ⟨ f ⟩)
    ∃-[]ˢ-⟨⟩ {Γt} {I} {J} {Γi} {f} {K} = 
        mkSieveEq {J}
        (Sh.Sieve.R ((∃-sieve Γt K I Γi) [ f ]ˢ))
        (Sh.Sieve.R (∃-sieve Γt K J (Γt ∶ Γi ⟨ f ⟩))) 
        {Sh.Sieve.restr ((∃-sieve Γt K I Γi) [ f ]ˢ)}
        {Sh.Sieve.restr (∃-sieve Γt K J (Γt ∶ Γi ⟨ f ⟩))}
        (funext (λ K' → funext (λ g → cong (∃ (D K')) 
        (funext (λ d → cong (λ z -> ∣ K ∣ K' (z ,Σ d)) (Γt ∶⟨∘⟩))))))

    ∃' : {Γt : Cont} -> For (Γt ▸t) -> For Γt
    ∣ ∃' {Γt} K ∣ I Γi = I ◁ (∃-sieve Γt K I Γi) --∃ (D I) λ d -> ∣ K ∣ I (Γi ,Σ d)
    _∶_⟨_⟩ (∃' {Γt} K) {I} {J} {i} x f = substp (J ◁_) (∃-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {K}) (x [ f ]ᶜ)
    glue (∃' {Γt} K) {I} {i} {R} I◁R x = local I◁R λ {J} f J⊩R → substp (J ◁_) (sym (∃-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {K})) (x {J} f J⊩R)
    
    ∃intro : {Γt : Cont} {K : For (Γt ▸t)} (t : Tm Γt) {Γ : Conp Γt} ->
      Pf Γ (K [ idt ,t t ]F) -> Pf Γ (∃' K)
    ∣ ∃intro {Γt}{K} t {Γ} PfK ∣ {I}{i} Γi = maximal ((∣ t ∣ I i) ,∃ substp (λ z -> ∣ K ∣ I (z ,Σ ∣ t ∣ I i)) (sym (Γt ∶⟨id⟩)) (∣ PfK ∣ Γi))
    
    ∃elim : {Γt : Cont} {K : For (Γt ▸t)} {Γp : Conp Γt}{L : For Γt} ->
      Pf Γp (∃' K) -> Pf ((Γp [ pt ]C) ▸p (K [ _,t_ {Γt} pt (qt {Γt}) ]F)) (L [ pt ]F) -> Pf Γp L
    ∣ ∃elim {Γt}{K}{Γp}{L} Pf∃K PfKL ∣ {I} {i} Γi = 
        L .glue (∣ Pf∃K ∣ Γi) λ {J} f x → 
        with∃ x (λ d Kj → ∣ PfKL ∣ ((Γp ∶ Γi ⟨ f ⟩) ,Σ Kj))

    Eq-sieve : (Γt : Cont) -> (t t' : Tm Γt) -> (I : Ob) -> (Γi : ∣ Γt ∣ I) -> Sieve I
    Eq-sieve Γt t t' I Γi .Sh.Sieve.R = λ J f -> ∣ t ∣ J (Γt ∶ Γi ⟨ f ⟩) ≡ ∣ t' ∣ J (Γt ∶ Γi ⟨ f ⟩)
    Eq-sieve Γt t t' I Γi .Sh.Sieve.restr {J} {f} {K} x g = 
        trans 
            (trans (sym (nat t)) D∶⟨∘⟩) 
            (trans (cong (D∶_⟨ g ⟩) (trans (nat t) (trans x (sym (nat t')))))
            (trans (sym D∶⟨∘⟩) (nat t')))

    Eq-[]ˢ-⟨⟩ : ∀{Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}{t t' : Tm Γt} ->
        (Eq-sieve Γt t t' I Γi) [ f ]ˢ ≡  Eq-sieve Γt t t' J (Γt ∶ Γi ⟨ f ⟩)
    Eq-[]ˢ-⟨⟩ {Γt}{I}{J}{Γi}{f}{t}{t'} = 
        mkSieveEq {J}
        (Sh.Sieve.R ((Eq-sieve Γt t t' I Γi) [ f ]ˢ))
        (Sh.Sieve.R (Eq-sieve Γt t t' J (Γt ∶ Γi ⟨ f ⟩))) 
        {Sh.Sieve.restr ((Eq-sieve Γt t t' I Γi) [ f ]ˢ)}
        {Sh.Sieve.restr (Eq-sieve Γt t t' J (Γt ∶ Γi ⟨ f ⟩))}
        (funext (λ K → funext (λ g → 
        cong-bin (_≡_) (cong (∣ t ∣ K) (Γt ∶⟨∘⟩)) (cong (∣ t' ∣ K) (Γt ∶⟨∘⟩)))))
    
    Eq : {Γt : Cont} -> Tm Γt -> Tm Γt -> For Γt
    ∣ Eq {Γt} t t' ∣ I Γi = I ◁ (Eq-sieve Γt t t' I Γi) 
    _∶_⟨_⟩ (Eq {Γt} t t') {I} {J} {i} x f = substp (J ◁_) (Eq-[]ˢ-⟨⟩ {Γt}{I}{J}{i}{f}{t}{t'}) (x [ f ]ᶜ)
    glue (Eq {Γt} t t') {I} {i} {R} I◁R x = local I◁R λ {J} f y → substp (J ◁_) (sym (Eq-[]ˢ-⟨⟩ {Γt}{I}{J}{i}{f}{t}{t'})) (x f y)

    Eq[] : {Γt Δt : Cont} {γt : Subt Δt Γt} {t t' : Tm Γt} ->
      (Eq t t' [ γt ]F) ≡ Eq (t [ γt ]t) (t' [ γt ]t)
    Eq[] = {!   !} -- refl
    
    Eqrefl : {Γt : Cont} {t : Tm Γt} {Γ : Conp Γt} -> Pf Γ (Eq t t)
    ∣ Eqrefl ∣ x = maximal refl

    subst' : {Γt : Cont} (K : For (Γt ▸t)) {t t' : Tm Γt} {Γ : Conp Γt} ->
      Pf Γ (Eq t t') -> Pf Γ (K [ idt ,t t ]F) -> Pf Γ (K [ idt ,t t' ]F)
    ∣ subst' {Γt} K {t}{t'} t=t' PfK ∣ {I}{i} x = 
        K .glue (∣ t=t' ∣ x) (λ {J} f y → 
        substp (λ z -> ∣ K ∣ J ((Γt ∶ i ⟨ f ⟩) ,Σ z)) (trans (nat t) (trans y (sym (nat t')))) 
        (K ∶ (∣ PfK ∣ x) ⟨ f ⟩))
        
    Beth : Model funar relar _ _ _ _ _
    Beth = record
      { Cont = Cont
      ; Subt = Subt
      ; _∘t_ = _∘t_
      ; idt = idt
      ; asst = refl
      ; idlt = refl
      ; idrt = refl
      ; ◆t = ◆t
      ; εt = εt
      ; ◆tη = λ σ -> refl
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
      ; ◆sη = λ ts -> refl
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
      ; ∨[] = {!   !}
      ; ∨elim = λ {Γt}{K}{L}{C} -> ∨elim {Γt}{K}{L}{C}
      ; ∨intro₁ = λ {Γt}{K}{L} -> ∨intro₁ {Γt}{K}{L}
      ; ∨intro₂ = λ {Γt}{K}{L} -> ∨intro₂ {Γt}{K}{L}
      ; ∀' = ∀'
      ; ∀[] = λ {Γt}{K}{Δt}{γt} -> ∀[] {Γt}{K}{Δt}{γt}
      ; ∀intro = λ {Γt}{K}{Γ} -> ∀intro {Γt}{K}{Γ} 
      ; ∀elim = λ {Γt}{K}{Γ} -> ∀elim {Γt}{K}{Γ}
      ; ∃' = ∃'
      ; ∃[] = {!   !}
      ; ∃intro = λ {Γt}{K} -> ∃intro {Γt}{K}
      ; ∃elim = λ {Γt}{K}{Γp}{L} -> ∃elim {Γt}{K}{Γp}{L} 
      ; Eq = Eq
      ; Eq[] = {!   !}
      ; Eqrefl = λ {Γt}{t}{Γ} -> Eqrefl {Γt}{t}{Γ}
      ; subst' = subst'
      }   

module Completeness where
        
    open import FirstOrderLogic.IntFullSplit.Syntax funar relar as I

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

    pp' : ∀{Γ : Con}{K : I.For (proj₁ Γ)} -> Sub (Γ ▸p' K) Γ
    pp' {Γt ,Σ Γ} {K} = I.idt ,Σ (substp (Subp (Γ ▸p K)) (sym [id]C) pp)

    qp' : ∀{Γ : Con}{K} → I.Pf (proj₂ (Γ ▸p' K)) (K [ I.idt ]F)
    qp' {Γt ,Σ Γ} {K} = substp (I.Pf (Γ ▸p K)) (sym [id]F) I.qp

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

    open Sh C

    {-# NO_UNIVERSE_CHECK #-}
    data _◁_ (Γ : Con) : Sieve Γ → Prop where
        maximal : ∀ {R} -> ⟨ Γ , id ⟩⊩ R -> Γ ◁ R
        ◁-⊥ : ∀ {R} -> Pf (proj₂ Γ) ⊥ -> Γ ◁ R
        ◁-∨ : ∀ {R A B} -> 
            (∀ {Δ : Con} -> (γ : Sub Δ Γ) -> I.Pf (proj₂ Δ) (A [ proj₁ γ ]F) -> Δ ◁ (R [ γ ]ˢ)) ->
            (∀ {Δ : Con} -> (γ : Sub Δ Γ) -> I.Pf (proj₂ Δ) (B [ proj₁ γ ]F) -> Δ ◁ (R [ γ ]ˢ)) ->
            I.Pf (proj₂ Γ) (A I.∨ B) -> Γ ◁ R
        ◁-∃ : ∀{R A} -> 
            (∀ {Δ} (γ : Sub Δ Γ) -> 
                (d : I.Tm (proj₁ Δ)) -> 
                I.Pf (proj₂ Δ) (A [ (proj₁ γ) ,t d ]F) -> 
                Δ ◁ (R [ γ ]ˢ)) -> 
            I.Pf (proj₂ Γ) (I.∃' A) -> 
            Γ ◁ R
        --◁-Eq : ∀{t t' K} ->
        --    I.Pf (proj₂ Γ) (I.Eq t t') -> 
        --    Γ ◁ (K [ id ,t' t ]ˢ) -> 
        --    Γ ◁ (K [ id ,t' t' ]ˢ)

    -- ∃elim : Pf Γ (∃ A) -> ∃ Tm (Pf Γ A)
    -- Pf Γ (∃ A) -> ((d : Tm) -> (Pf Γ A) -> Pf Γ C) -> Pf Γ C
    -- Γ ⊢ ∃ A -> (∀ {Δ} (γ : Δ ⊢ˢ Γ) -> (d : Tm Δ) -> Δ ⊢ (A [ idt ,t d ]F) -> Δ ◁ C [ γ ]ˢ) -> Γ ◁ C
      
    -- Eq-subst' : {Γt : Cont} (K : For (Γt ▸t)) {t t' : Tm Γt} {Γ : Conp Γt} ->
    --  Pf Γ (Eq t t') -> Pf Γ (K [ idt ,t t ]F) -> Pf Γ (K [ idt ,t t' ]F) 
    -- I.Pf (proj₂ Γ) (I.Eq t t') -> I.Pf (proj₂ Γ) (K [ id ,t' t' ]F) -> Γ ◁ K [ id ,t' t' ]ˢ

    _[_]ᶜ : ∀{Γ Δ R} -> Γ ◁ R → (γ : Sub Δ Γ) → Δ ◁ (R [ γ ]ˢ)
    (_[_]ᶜ {Γ}{Δ}{R} (maximal x) γ) = maximal (substp (Sh.Sieve.R R Δ) (trans idl' (sym (idr' {f = γ}))) (R .Sh.Sieve.restr x γ))
    ◁-⊥ x [ (γt ,Σ γp) ]ᶜ = ◁-⊥ (x I.[ γt ]p I.[ γp ]P)
    ((◁-∨ x y z) [ γ@(γt ,Σ γp) ]ᶜ) = 
        ◁-∨ 
        (λ {Θ} δ l → {! x (γ ∘ δ) ?  !}) -- [∘]ˢ is needed 
        (λ {Θ} δ k → {! y (γ ∘ δ) ?  !}) -- [∘]ˢ is needed  
        (z I.[ γt ]p I.[ γp ]P) -- ◁-∨ (λ {Θ} δ l → x (γ ∘ δ) l) (λ {Θ} δ k → y (γ ∘ δ) k) (z I.[ γ ]F)
    ◁-∃ x x₁ [ γ ]ᶜ = {!   !}
    --◁-Eq x x₁ [ γ ]ᶜ = {!   !}

    local : ∀{Γ R S} -> Γ ◁ R →
      ({Δ : Con} (γ : Sub Δ Γ) → ⟨ Δ , γ ⟩⊩ R → Δ ◁ (S [ γ ]ˢ)) → Γ ◁ S
    local (maximal x) x₁ = {!   !}
    local {Γ}{R}{S} (◁-⊥ x) x₁ = {! Sieve.R S  !}
    local (◁-∨ x x₂ x₃) x₁ = {!   !}
    local (◁-∃ x₁ x₂) x = {!   !}
    --local (◁-Eq x₁ x₂) x = {!   !}

    J : Top
    J .Sh.Top._◁_ = _◁_
    J .Sh.Top._[_]ᶜ = _[_]ᶜ
    J .Sh.Top.maximal = maximal
    J .Sh.Top.local = local

    --relGlue : ∀ (n : ℕ) (a : relar n) (Γ@(Γt ,Σ Γp) : Con) (ts : Tm Γt ^ n)
    --    (R : Sieve Γ) → Γ ◁ R →
    --    ({Δ@(Δt ,Σ Δp) : Con} (f@(ft ,Σ _) : Sub Δ Γ) → ⟨ Δ , f ⟩⊩ R → Pf Δp (rel n a (reifyTms (map^ ts (_[ ft ]t))))) →
    --    Pf Γp (rel n a (reifyTms ts))
    --relGlue zero a Γ * R Γ◁R x = x {Γ} id {!   !}
    --relGlue (suc n) a Γ (ts ,Σ t) R Γ◁R x = {!   !}

    module B = Semantics
        C
        J
        (λ (Γt ,Σ _) → I.Tm Γt)
        (λ t (γt ,Σ _) → t I.[ γt ]t)
        (λ { {a = t} -> [∘]t {t = t}})
        (λ { {a = t} -> [id]t {t = t}})
        (λ n a (Γt ,Σ Γp) ts → I.Pf Γp (rel n a (reifyTms ts)))
        (λ {n}{a}{(Γt ,Σ Γ)}{(Δt ,Σ Δ)}{ts} Pfrel (γt ,Σ γ) -> substp (λ z -> Pf Δ (rel n a z)) (sym ⟨reifyTms⟩) ((Pfrel I.[ γt ]p) [ γ ]P))
        (λ n a (Γt ,Σ Γ) ts -> fun n a (reifyTms ts))
        (λ n a (Γt ,Σ Γ) (Δt ,Σ Δ) ts (γt ,Σ γ) -> cong (fun n a) (sym ⟨reifyTms⟩))

    open B
    open import FirstOrderLogic.IntFullSplit.Iterator
    open Ite funar relar Beth

    mutual
        reflect-cont : ∀{Γt : I.ConTm}{Γ : I.ConPf Γt}(Δt : I.ConTm) -> (γt : I.Subt Γt Δt) -> ∣ ⟦ Δt ⟧Cont ∣ (Γt ,Σ Γ)
        reflect-cont ◆t x = *
        reflect-cont (Δt ▸t) (γ ,t t) = reflect-cont Δt γ ,Σ t

        reflect-conp : ∀{Γt}{Γ}{Δt} (Δ : I.ConPf Δt) -> (γt : I.Subt Γt Δt) -> (γ : I.Subp Γ (Δ I.[ γt ]C)) -> ∣ ⟦ Δ ⟧Conp ∣ (Γt ,Σ Γ) (reflect-cont Δt γt)
        reflect-conp {Γt}{Γ}{Δt} ◆p γ γt = *
        reflect-conp {Γt}{Γ}{Δt} (Δ ▸p K) γt γ = (reflect-conp Δ γt (I.pp I.∘p γ)) ,Σ reflect {Δt}{Γt}{Γ}{γt} K (I.qp I.[ γ ]P)
        
        reflect-con : ∀{Γ : Con} (Δ : Con) -> Sub Γ Δ -> Σsp (∣ ⟦ proj₁ Δ ⟧Cont ∣ Γ) (∣ ⟦ proj₂ Δ ⟧Conp ∣ Γ)
        reflect-con {Γt ,Σ Γ} (Δt ,Σ Δ) (γt ,Σ γ) = reflect-cont Δt γt ,Σ reflect-conp Δ γt γ

        ⟨⟩-reflect-cont : ∀{Γt Δt Θt : I.ConTm}{Δ : I.ConPf Δt}{Θ : I.ConPf Θt}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub (Θt ,Σ Θ) (Δt ,Σ Δ)} -> 
            (reflect-cont Γt (γt I.∘t δt)) ≡ ⟦ Γt ⟧Cont ∶ (reflect-cont Γt γt) ⟨ δ ⟩
        ⟨⟩-reflect-cont {◆t} {Δt} {Θt} {Δ} {Θ} {γt} {δ} = refl
        ⟨⟩-reflect-cont {Γt ▸t} {Δt} {Θt} {Δ} {Θ} {γt ,t t} {δ} = 
            let h = ⟨⟩-reflect-cont {Γt} {Δt} {Θt} {Δ} {Θ} {γt} {δ} in
            mk,= h refl

        ⟨∘⟩-reflect-cont : ∀{Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{A : I.For Γt}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ} -> 
            ∣ ⟦ A ⟧For ∣ Θ (reflect-cont Γt (γt I.∘t δt)) ≡ 
            ∣ ⟦ A ⟧For ∣ Θ (⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ δ ⟩)
        ⟨∘⟩-reflect-cont {Γt} {Δ@(Δt ,Σ Δp)} {Θ@(Θt ,Σ Θp)} {A} {γt} {δ} = 
            cong (∣ ⟦ A ⟧For ∣ Θ) (⟨⟩-reflect-cont {Γt} {Δt} {Θt} {Δp} {Θp} {γt} {δ})

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

        -- TODO : Should try reify/reflect with more simpler type

        reify   : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt) -> I.Pf Δ (A I.[ γt ]F)        
        reify-⊥ : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt} -> ∣ ⟦ I.⊥ {Γt} ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ I.⊥        
        reify-⊥' : ∀{Γt}{Γ : I.ConPf Γt} -> ∣ ⟦ I.⊥ {Γt} ⟧For ∣ (Γt ,Σ Γ) (reflect-cont {Γt}{Γ} Γt I.idt) -> I.Pf Γ I.⊥        
        reify-∨ : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A B : I.For Γt) -> ∣ ⟦ A I.∨ B ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((A I.∨ B) I.[ γt ]F)    
        reify-∃ : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For (Γt I.▸t)) -> ∣ ⟦ I.∃' A  ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((I.∃' A) I.[ γt ]F)    
        reify-∃' : ∀{Γt}{Γ : I.ConPf Γt}(A : I.For (Γt I.▸t)) -> ∣ ⟦ I.∃' A  ⟧For ∣ (Γt ,Σ Γ) (reflect-cont {Γt}{Γ} Γt I.idt) -> I.Pf Γ (I.∃' A)    
        reify-Eq  : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(t t' : I.Tm Γt) -> ∣ ⟦ I.Eq t t'  ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((I.Eq t t') I.[ γt ]F)    
        reify-rel : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(n : ℕ)(a : relar n)(ts : I.Tms Γt n) -> ∣ ⟦ I.rel n a ts  ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((I.rel n a ts) I.[ γt ]F)    
        
        reify-⊥' (◁-⊥ x) = {!   !}
        reify-⊥' (◁-∨ x x₁ x₂) = {!   !}
        reify-⊥' (◁-∃ x x₁) = {!   !}

        reify-∃' A x = {!  x !}

{-
 R ≟    ∃-sieve 
        C 
        J 
        ∣ ⟦ Γt₁ ⟧Cont ∣
        ∣ ⟦ A ⟧For ∣ (Γt₁ ,Σ Γ₁) (reflect-cont Γt₁ I.idt)
-}


        {-
        reify-⊥ (◁-⊥ x) = I.exfalso x
        reify-⊥ {Γt}{Δt}{Δ}{γt} (◁-∨ {R}{A}{B} f g x) = 
            I.∨elim 
            (reify-⊥ {Γt}{Δt}{Δ I.▸p A}{γt} (f pp' qp')) 
            (reify-⊥ {Γt}{Δt}{Δ I.▸p B}{γt} (g pp' qp')) 
            x
        reify-⊥ (◁-∃ x₁ x₂) = ?
        -}
        reify-⊥ (◁-⊥ x) = {!   !}
        reify-⊥ (◁-∨ x x₁ x₂) = {!   !}
        reify-⊥ (◁-∃ x x₁) = {!   !}

        reify-∨ {Γt} {Δt} {Δ} {γt} A B x = {! x  !}

        reify-∃ A x = {!  !}

        reify-Eq = {!   !}
        reify-rel = {!   !}

        reify {Γt} {Δt} {Δ} {γt} ⊥ x = reify-⊥ {Γt} {Δt} {Δ} {γt} x
        reify ⊤ x = I.tt
        reify {Γt} {Δt} {Δ} {γt} (A ⊃ B) x =
            let pa  = reflect {Γt}{Δt}{Δ I.▸p (A I.[ γt ]F)} A I.qp in
            let pa' = substp (λ z -> z) (trans (cong (λ z -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ (Δ I.▸p (A I.[ γt ]F))) (reflect-cont Γt z)) (sym idr)) (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Δt ,Σ (Δ I.▸p A I.[ γt ]F)}{A}{γt}{pp'})) pa in
            let pb = x (Δt ,Σ (Δ I.▸p A I.[ γt ]F)) pp' pa' in 
            let pb' = substp (λ z -> z) (trans (sym (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Δt ,Σ (Δ I.▸p A I.[ γt ]F)}{B}{γt}{pp'})) (cong (λ z -> ∣ ⟦ B ⟧For ∣ (Δt ,Σ (Δ I.▸p (A I.[ γt ]F))) (reflect-cont Γt z)) idr)) pb in
            I.⊃intro (reify B pb')
        reify (A ∧ B) x = I.∧intro (reify A (x .proj₁)) (reify B (x .proj₂))
        reify (A ∨ B) x = reify-∨ A B x
        reify {Γt} {Δt} {Δ} {γt} (∀' A) x = 
            let pa  = x ((Δt I.▸t) ,Σ Δ I.[ I.pt ]C) pt' I.qt in
            let pa' = substp (λ z -> z) (⟨pt⟩-reflect-cont {Γt}{Δt ,Σ Δ}{A}{γt}) pa in 
            I.∀intro (reify A pa')
        reify (∃' A) x = reify-∃ A x
        reify (Eq t t') x = reify-Eq t t' x
        reify (rel n a ts) x = reify-rel n a ts x

        reflect : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> I.Pf Δ (A I.[ γt ]F) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt)
        reflect ⊥ x = ◁-⊥ x
        reflect ⊤ x = *
        reflect {Γt} {Δt} {Δ} {γt} (A ⊃ B) x Θ@(Θt ,Σ Θp) δ@(δt ,Σ δp) pa =
            let PfA  = reify {Γt}{Θt}{Θp}{γt I.∘t δt} A (substp (λ z -> z) (sym (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Θ}{A}{γt}{δ})) pa) in 
            let PfAB = substp (λ z -> z) (cong (I.Pf Θp) (cong-bin I._⊃_ (sym [∘]F) (sym [∘]F))) (x I.[ δt ]p I.[ δp ]P) in 
            substp (λ z -> z) (⟨∘⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Θ}{B}{γt}{δ}) 
            (reflect {Γt}{Θt}{Θp}{γt I.∘t δt} B ((I.⊃elim PfAB) I.[ I.idp I.,p PfA ]P))
        reflect (A ∧ B) x = (reflect A (I.∧elim₁ x)) ,Σ (reflect B (I.∧elim₂ x))
        reflect {Γt} {Δt} {Δp} {γt} (A ∨ B) x = ◁-∨ 
            (λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) PfA -> 
                let r = substp (I.Pf Θp) (sym [∘]F) PfA in
                maximal (inj₁
                    (substp (∣ ⟦ A ⟧For ∣ Θ) (trans ⟨⟩-reflect-cont (cong (⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨_⟩) (sym (idr' {Θ}{Δt ,Σ Δp}{δ})))) 
                    (reflect A r))))
            (λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) PfB -> 
                let r = substp (I.Pf Θp) (sym [∘]F) PfB in
                maximal (inj₂
                    (substp (∣ ⟦ B ⟧For ∣ Θ) (trans ⟨⟩-reflect-cont (cong (⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨_⟩) (sym (idr' {Θ}{Δt ,Σ Δp}{δ})))) 
                    (reflect B r))))
            x
        reflect {Γt}{Δt}{Δ}{γt} (∀' A) x Θ@(Θt ,Σ Θp) δ@(δt ,Σ δp) pa = 
            let Pf∀A = substp (λ z -> I.Pf Θp (I.∀' z)) (sym [∘]F) (x I.[ δt ]p I.[ δp ]P) in
            let k = (I.∀elim Pf∀A) I.[ I.idt I.,t pa ]p in
            let eq = (trans (trans (cong (λ z -> z I.∘t (I.idt I.,t pa) I.,t pa) (sym (∘t-pt γt δt))) refl) ((↑-,t (γt I.∘t δt) pa))) in
            let k' = substp (λ z -> I.Pf (proj₁ z) (proj₂ z)) (mk,=
                    (trans (sym [∘]C) (trans (cong (Θp I.[_]C) ▸tβ₁) [id]C)) 
                    (trans (sym [∘]F) (cong (A I.[_]F) eq))) k in
            substp (λ z -> z) (⟨d⟩-reflect-cont {Γt}{Δt ,Σ Δ}{Θ}{A}{γt}{δ}{pa}) (reflect {Γt I.▸t}{Θt}{Θp}{(γt I.∘t δt) I.,t pa} A k')
        reflect {Γt}{Δt}{Δ}{γt} (∃' A) x = {!   !} 
            -- Mükszik
            --◁-∃ x λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) d PfA → 
            --let PfA' = reflect A (substp (I.Pf Θp) (sym [∘]F) PfA) in
            --let PfA'' = substp (∣ ⟦ A ⟧For ∣ Θ) (trans (cong (_,Σ d) (trans {!   !} ⟨⟩-reflect-cont)) (cong (λ z -> (⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ z ⟩) ,Σ d) (sym (idr' {f = δ})))) PfA' in
            --maximal (d ,∃ PfA'')
        reflect (Eq t t') x = {!   !} -- ◁-Eq x (maximal {!   !})
        reflect (rel n a ts) x = {!  !}
    
    completeness : ∀{Γt}{Γ} -> (A : I.For Γt) -> B.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For -> I.Pf Γ A
    completeness {Γt}{Γ} A p = substp (I.Pf Γ) [id]F (reify {Γt}{Γt}{Γ} A (∣ p ∣ (reflect-conp Γ I.idt (substp (I.Subp Γ) (sym [id]C) I.idp))))
    
    soundness : ∀{Γt Γ} -> (A : I.For Γt) -> I.Pf Γ A -> B.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For
    soundness A = ⟦_⟧Pf    