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
        assC : ∀{A B C D}{f : Hom C D}{g : Hom B C}{h : Hom A B} -> 
            (f ∘C g) ∘C h ≡ f ∘C (g ∘C h)
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

    [∘]ˢ : ∀{I J K : Ob}{f : Hom J I}{g : Hom K J}{s : Sieve I} -> 
        s [ f ∘C g ]ˢ ≡ s [ f ]ˢ [ g ]ˢ  
    [∘]ˢ {I}{J}{K}{f}{g}{s} = 
        mkSieveEq
        (∣ s [ f ∘C g ]ˢ ∣) 
        (∣ (s [ f ]ˢ) [ g ]ˢ ∣) 
        {restr (s [ f ∘C g ]ˢ)}
        {restr ((s [ f ]ˢ) [ g ]ˢ)}
        (funext (λ L → funext (λ h → cong (∣ s ∣ L) assC)))
    
    [id]ˢ : ∀{I : Ob}{s : Sieve I} -> s [ idC ]ˢ ≡ s
    [id]ˢ {I}{s} = 
        mkSieveEq
        (∣ s [ idC ]ˢ ∣) 
        (∣ s ∣) 
        {restr (s [ idC ]ˢ)}
        {restr s}
        (funext (λ L → funext (λ h → cong (∣ s ∣ L) idlC)))
    
    record Top : Set₁ where
        infix 4 _◁_
        infixl 9 _[_]ᶜ
        field
            _◁_     : (I : Ob) -> Sieve I -> Prop
            _[_]ᶜ   : ∀ {I J R} -> I ◁ R -> (f : Hom J I) -> J ◁ (R [ f ]ˢ)
            maximal : ∀{I R} -> ∣ R ∣ I idC -> I ◁ R
            local   : ∀{I R S} -> I ◁ R -> 
                (∀{J} -> (f : Hom J I) -> ∣ R ∣ J f  -> J ◁ (S [ f ]ˢ)) -> I ◁ S

    record Sheaf (J : Top) : Set₁ where
        
        open Top J
        
        field
            A     : Ob -> Set
            _⟨_⟩  : ∀{I J} -> A I -> Hom J I -> A J
            ⟨id⟩  : ∀{I : Ob}{a : A I} -> a ⟨ idC ⟩ ≡ a
            ⟨∘⟩   : ∀{I J K : Ob}{a : A I}{f : Hom J I}{g : Hom K J} -> 
                (a ⟨ f ⟩) ⟨ g ⟩ ≡ a ⟨ f ∘C g ⟩
            glue  : ∀{I R} -> I ◁ R -> 
                (∀{J} -> (f : Hom J I) -> ∣ R ∣ J f -> A J) -> A I
    open Sheaf renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩; ⟨id⟩ to _∶⟨id⟩; ⟨∘⟩ to _∶⟨∘⟩)

module Semantics
    (C : Category)
    (open Category C)
    (open Sh C)
    (J : Top)
    (open Top J)
    (D : Ob -> Set)
    (D∶_⟨_⟩ : ∀{I J} -> D I -> Hom J I -> D J)
    (D∶⟨∘⟩  : ∀{I J K}{a : D I}{f : Hom J I}{g : Hom K J} -> 
        D∶ a ⟨ f ∘C g ⟩ ≡ D∶ D∶ a ⟨ f ⟩ ⟨ g ⟩)
    (D∶⟨id⟩ : ∀{I}{a : D I} -> D∶ a ⟨ idC ⟩ ≡ a)
    (rel  : (n : ℕ) -> relar n -> (I : Ob) -> (D I) ^ n -> Prop)
    (⟨rel⟩ : ∀{n i I J ds} -> rel n i I ds -> (f : Hom J I) -> 
        rel n i J (map^ ds (D∶_⟨ f ⟩)))
    (fun  : (n : ℕ) -> funar n -> (I : Ob) -> (D I) ^ n -> (D I))
    (⟨fun⟩ : ∀(n : ℕ)(a : funar n)(I J : Ob)(ds : (D I) ^ n)(f : Hom J I) -> 
        (D∶ (fun n a I ds) ⟨ f ⟩) ≡ (fun n a J (map^ ds (D∶_⟨ f ⟩))))
    where

    record Cont : Set₁ where
        constructor mk
        field
            A    : Ob -> Set
            _⟨_⟩ : ∀{I J} -> A I -> Hom J I -> A J
            ⟨id⟩ : ∀{I}{a : A I} -> a ⟨ idC ⟩ ≡ a
            ⟨∘⟩  : ∀{I J K}{a : A I}{g : Hom K J}{f : Hom J I} -> 
                a ⟨ f ∘C g ⟩ ≡ (a ⟨ f ⟩) ⟨ g ⟩
    open Cont public 
        renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩; ⟨id⟩ to _∶⟨id⟩; ⟨∘⟩ to _∶⟨∘⟩)

    record Subt(Δ Γ : Cont) : Set where
        constructor mk
        field
            α   : ∀(I : Ob) -> ∣ Δ ∣ I -> ∣ Γ ∣ I
            nat : ∀{I J : Ob}{a : ∣ Δ ∣ I}{f : Hom J I} -> 
                (Γ ∶ (α I a) ⟨ f ⟩) ≡ α J (Δ ∶ a ⟨ f ⟩)
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

    εt : {Γ : Cont} -> Subt Γ ◆t
    ∣ εt ∣ = λ I x -> *
    nat εt = refl

    record For(Γ : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> A I i -> (f : Hom J I) -> 
                A J (Γ ∶ i ⟨ f ⟩)
            glue : ∀{I : Ob}{i : ∣ Γ ∣ I}{R : Sieve I} -> 
                I ◁ R -> 
                (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R -> A J (Γ ∶ i ⟨ f ⟩)) -> 
                A I i
    open For public renaming (A to ∣_∣; _⟨_⟩ to _∶_⟨_⟩)

    mkForEq : ∀{Γ : Cont}{A B : ∀(I : Ob) -> ∣ Γ ∣ I -> Prop } ->
        {sub₁ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> 
            A I i -> (f : Hom J I) -> A J (Γ ∶ i ⟨ f ⟩)} ->
        {sub₂ : ∀{I J : Ob}{i : ∣ Γ ∣ I} -> 
            B I i -> (f : Hom J I) -> B J (Γ ∶ i ⟨ f ⟩)} ->
        {glue₁ : ∀{I : Ob}{i : ∣ Γ ∣ I}{R : Sieve I} -> 
            I ◁ R -> 
            (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R -> A J (Γ ∶ i ⟨ f ⟩)) -> 
            A I i} ->
        {glue₂ : ∀{I : Ob}{i : ∣ Γ ∣ I}{R : Sieve I} -> 
            I ◁ R -> 
            (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R -> B J (Γ ∶ i ⟨ f ⟩)) -> 
            B I i} ->
        (A ≡ B) -> 
        _≡_ {A = For Γ} (mk A sub₁ glue₁)(mk B sub₂ glue₂)
    mkForEq refl = refl

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
    
    ⟨recTms⟩ : ∀{n I J}{f : Hom J I}{ts : ∣ DPShV n ∣ I} -> 
        map^ (recTms {n} I ts) (D∶_⟨ f ⟩) ≡ recTms J ((DPShV n) ∶ ts ⟨ f ⟩)
    ⟨recTms⟩ {zero} {I} {J} {f} {ts} = refl
    ⟨recTms⟩ {suc n} {I} {J} {f} {ts} = mk,= refl ⟨recTms⟩

    fun' : {Γ : Cont} (n : ℕ) -> funar n -> Tms Γ n -> Tm Γ
    ∣ fun' n a ts ∣ I x = fun n a I (recTms I (∣ ts ∣ I x))
    nat (fun' n a ts) {I}{J}{i}{f} = 
        trans 
            (⟨fun⟩ n a I J (recTms I (∣ ts ∣ I i)) f) 
            (cong (fun n a J) (trans 
                (⟨recTms⟩ {n} {I} {J} {f} {∣ ts ∣ I i}) 
                (cong (recTms J) (nat ts))))

    rel-sieve : (Γt : Cont) -> (n : ℕ) -> (relar n) -> (ts : Tms Γt n) -> 
        (I : Ob) -> (∣ Γt ∣ I) -> Sieve I
    rel-sieve Γt n a ts I i .Sh.Sieve.R J f = 
        rel n a J (recTms J (∣ ts ∣ J (Γt ∶ i ⟨ f ⟩)))
    rel-sieve Γt n a ts I i .Sh.Sieve.restr {J} {f} {K} r g = 
        substp 
            (rel n a K) 
            (trans 
                ⟨recTms⟩ 
                (cong (recTms K) (trans 
                    (nat ts) 
                    (cong (∣ ts ∣ K) (sym (Γt ∶⟨∘⟩)))))) 
            (⟨rel⟩ r g)

    rel-[]ˢ-⟨⟩ : 
        ∀{Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}{n : ℕ}{a : relar n}
        {ts : Tms Γt n} ->
        (rel-sieve Γt n a ts I Γi) [ f ]ˢ 
        ≡ 
        rel-sieve Γt n a ts J (Γt ∶ Γi ⟨ f ⟩)
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
    _∶_⟨_⟩ (rel' {Γt} n a ts) {I} {J} {i} x f = 
        substp 
            (J ◁_) 
            (rel-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {n} {a} {ts}) 
            (x [ f ]ᶜ)
    rel' {Γt} n a ts .glue {I} {i} I◁R x = 
        local I◁R 
        (λ {J} f y → substp 
            (J ◁_) 
            (sym (rel-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {n} {a} {ts})) 
            (x f y))

    rel[] : {Γ : Cont}{n : ℕ}{a : relar n}{ts : Tms Γ n}{Δ : Cont}
        {γ : Subt Δ Γ} →
        (rel' n a ts [ γ ]F) ≡ rel' n a (_[_]ts {Γ}{n} ts γ)
    rel[] {Γ}{n}{a}{ts}{Δ}{γ} = 
        mkForEq 
        {Δ} 
        {∣ rel' n a ts [ γ ]F ∣}
        {∣ rel' n a (_[_]ts {Γ}{n} ts γ) ∣}
        {(rel' n a ts [ γ ]F) ∶_⟨_⟩}
        {(rel' n a (_[_]ts {Γ}{n} ts γ)) ∶_⟨_⟩}
        {glue (rel' n a ts [ γ ]F)}
        {glue (rel' n a (_[_]ts {Γ}{n} ts γ))}
        (funext (λ J -> funext (λ x -> cong (J ◁_) 
        (mkSieveEq 
        (Sh.Sieve.R (rel-sieve Γ n a ts J (∣ γ ∣ J x))) 
        (Sh.Sieve.R (rel-sieve Δ n a (_[_]ts {Γ}{n} ts γ) J x)) 
        {Sh.Sieve.restr (rel-sieve Γ n a ts J (∣ γ ∣ J x))}
        {Sh.Sieve.restr (rel-sieve Δ n a (_[_]ts {Γ}{n} ts γ) J x)}
        (funext (λ K -> funext (λ y -> 
            cong (λ z -> rel n a K (recTms K (∣ ts ∣ K z))) (nat γ))))))))

    record Conp(Γt : Cont) : Set₁ where
        constructor mk
        field
            A    : ∀(I : Ob) -> ∣ Γt ∣ I -> Prop
            _⟨_⟩ : ∀{I J : Ob}{i : ∣ Γt ∣ I} -> A I i -> (f : Hom J I) -> 
                A J (Γt ∶ i ⟨ f ⟩)
            glue : ∀{I : Ob}{i : ∣ Γt ∣ I}{R : Sieve I} -> 
                I ◁ R -> 
                (∀{J} -> (f : Hom J I) -> ⟨ J , f ⟩⊩ R -> A J (Γt ∶ i ⟨ f ⟩)) -> 
                A I i
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
    ∣ ⊥ ∣ I x = I ◁ ⊥sieve
        where
            ⊥sieve : Sieve I
            ⊥sieve .Sh.Sieve.R _ _ = 𝟘p
            ⊥sieve .Sh.Sieve.restr () g
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
    ∣ _⊃_ {Γt} K L ∣ I x = 
        (J : Ob) -> (f : Hom J I) -> 
        ∣ K ∣ J (Γt ∶ x ⟨ f ⟩) -> ∣ L ∣ J (Γt ∶ x ⟨ f ⟩)
    (_∶_⟨_⟩ (_⊃_ {Γt} K L) {I}{J}{i}) x f J' g Ki = 
        substp 
            (∣ L ∣ J') 
            (Γt ∶⟨∘⟩) 
            (x J' (f ∘C g) (substp (∣ K ∣ J') (sym (Γt ∶⟨∘⟩)) Ki))
    glue (_⊃_ {Γt} K L) {I} I◁R x J f Kj = 
        L .glue (I◁R [ f ]ᶜ) (λ {K'} g J⊩R -> 
        let EQ  = substp (∣ L ∣ K') (trans (Γt ∶⟨id⟩) (Γt ∶⟨∘⟩)) in
        let EQ' = substp (∣ K ∣ K') (trans (sym (Γt ∶⟨∘⟩)) (sym (Γt ∶⟨id⟩))) in
        EQ (x {K'} (f ∘C g) J⊩R K' idC (EQ' (K ∶ Kj ⟨ g ⟩))))

    prop-fun : ∀{i j}{A A' : Prop i}{B B' : Prop j} -> 
        A ≡ A' -> B ≡ B' -> 
        (A -> B) ≡ (A' -> B')
    prop-fun refl refl = refl

    ⊃[] : {Γt : Cont} {K L : For Γt} {Δt : Cont} {γt : Subt Δt Γt} ->
      ((K ⊃ L) [ γt ]F) ≡ ((K [ γt ]F) ⊃ (L [ γt ]F))
    ⊃[] {Γt} {K} {L} {Δt} {γt} = 
        mkForEq 
        {Δt}
        {∣ (K ⊃ L) [ γt ]F ∣}
        {∣ (K [ γt ]F) ⊃ (L [ γt ]F) ∣}
        {((K ⊃ L) [ γt ]F) ∶_⟨_⟩}
        {((K [ γt ]F) ⊃ (L [ γt ]F)) ∶_⟨_⟩}
        {glue ((K ⊃ L) [ γt ]F)}
        {glue ((K [ γt ]F) ⊃ (L [ γt ]F))}
        (funext (λ J → funext (λ x → 
        cong (λ Z -> (K : Ob) (f : Hom K J) -> Z K f) 
        (funext (λ K' → funext (λ y → 
            prop-fun (cong (∣ K ∣ K') (nat γt)) (cong (∣ L ∣ K') (nat γt))))))))
    
    ⊃intro : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf (Γ ▸p K) L -> Pf Γ (K ⊃ L)
    ∣ ⊃intro {Γt}{K}{L}{Γ} PfKL ∣ Γi J f Kj = ∣ PfKL ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ Kj)

    ⊃elim : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ (K ⊃ L) -> Pf (Γ ▸p K) L
    ∣ ⊃elim {Γt}{K}{L}{Γ} PfKL ∣ {I}{i} (Γi ,Σ Ki) = 
        substp 
            (∣ L ∣ I) 
            (Γt ∶⟨id⟩) 
            (∣ PfKL ∣ Γi I idC (substp (∣ K ∣ I) (sym (Γt ∶⟨id⟩)) Ki))

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

    ∨-sieve : (Γt : Cont) -> (I : Ob) -> (Γi : ∣ Γt ∣ I) -> (K L : For Γt) -> 
        Sieve I
    (∨-sieve Γt I Γi K L) .Sh.Sieve.R J f = 
        ∣ K ∣ J (Γt ∶ Γi ⟨ f ⟩) +p ∣ L ∣ J (Γt ∶ Γi ⟨ f ⟩)
    (∨-sieve Γt I Γi K L) .Sh.Sieve.restr {J}{f}{K'} (inj₁ Kj) g = 
        inj₁ (substp (∣ K ∣ K') (sym (Γt ∶⟨∘⟩)) (K ∶ Kj ⟨ g ⟩))
    (∨-sieve Γt I Γi K L) .Sh.Sieve.restr {J}{f}{K'} (inj₂ Lj) g = 
        inj₂ (substp (∣ L ∣ K') (sym (Γt ∶⟨∘⟩)) (L ∶ Lj ⟨ g ⟩))
    
    ∨-[]ˢ-⟨⟩ : {Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}
        {K L : For Γt} ->
        (∨-sieve Γt I Γi K L) [ f ]ˢ ≡  ∨-sieve Γt J (Γt ∶ Γi ⟨ f ⟩) K L
    ∨-[]ˢ-⟨⟩ {Γt} {I} {J} {Γi} {f} {K} {L} = 
        mkSieveEq {J}
        (Sh.Sieve.R (∨-sieve Γt I Γi K L [ f ]ˢ))
        (Sh.Sieve.R (∨-sieve Γt J (Γt ∶ Γi ⟨ f ⟩) K L)) 
        {Sh.Sieve.restr (∨-sieve Γt I Γi K L [ f ]ˢ)}
        {Sh.Sieve.restr (∨-sieve Γt J (Γt ∶ Γi ⟨ f ⟩) K L)}
        (funext (λ I' → funext (λ f' → 
            cong-bin _+p_ 
                (cong (∣ K ∣ I') (Γt ∶⟨∘⟩)) 
                (cong (∣ L ∣ I') (Γt ∶⟨∘⟩))))) 

    _∨_ : {Γt : Cont} -> For Γt -> For Γt -> For Γt
    ∣ _∨_ {Γt} K L ∣ I Γi    = I ◁ (∨-sieve Γt I Γi K L)
    _∶_⟨_⟩ (_∨_ {Γt} K L) {I} {J} {i} x f = 
        substp 
            (J ◁_) 
            (∨-[]ˢ-⟨⟩ {Γt}{I}{J}{i}{f}{K}{L}) 
            (_[_]ᶜ {I}{J} x f)
    glue (_∨_ {Γt} K L) {I} {i} {R} I◁R x = 
        local {I}{R} I◁R λ {J'} f J'⊩R → 
            substp (J' ◁_) (sym (∨-[]ˢ-⟨⟩ {Γt}{I}{J'}{i}{f}{K}{L})) (x f J'⊩R)

    ∨[] : {Γt : Cont} {K L : For Γt} {Δt : Cont} {γt : Subt Δt Γt} →
      ((K ∨ L) [ γt ]F) ≡ ((K [ γt ]F) ∨ (L [ γt ]F))
    ∨[] {Γt} {K}{L} {Δt} {γt} = 
        mkForEq
        {Δt} 
        {∣ (K ∨ L) [ γt ]F ∣}
        {∣ (K [ γt ]F) ∨ (L [ γt ]F) ∣}
        {((K ∨ L) [ γt ]F) ∶_⟨_⟩}
        {((K [ γt ]F) ∨ (L [ γt ]F)) ∶_⟨_⟩}
        {glue ((K ∨ L) [ γt ]F)}
        {glue ((K [ γt ]F) ∨ (L [ γt ]F))}
        (funext (λ J → funext (λ x → cong (J ◁_) 
        (mkSieveEq 
        (Sh.Sieve.R (∨-sieve Γt J (∣ γt ∣ J x) K L)) 
        (Sh.Sieve.R (∨-sieve Δt J x (K [ γt ]F) (L [ γt ]F))) 
        {Sh.Sieve.restr (∨-sieve Γt J (∣ γt ∣ J x) K L)}
        {Sh.Sieve.restr (∨-sieve Δt J x (K [ γt ]F) (L [ γt ]F))}
        (funext (λ K' → funext (λ y → 
            cong-bin _+p_ 
                (cong (∣ K ∣ K') (nat γt)) 
                (cong (∣ L ∣ K') (nat γt)))))))))

    ∨intro₁ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ K -> Pf Γ (K ∨ L)
    ∣ ∨intro₁ {Γt} {K} {L} {Γ} PfK ∣ Γi = 
        maximal (inj₁ (K ∶ ∣ PfK ∣ Γi ⟨ idC ⟩))
    
    ∨intro₂ : {Γt : Cont} {K L : For Γt} {Γ : Conp Γt} ->
      Pf Γ L -> Pf Γ (K ∨ L)
    ∣ ∨intro₂ {Γt} {K} {L} {Γ} PfL ∣ Γi = 
        maximal (inj₂ (L ∶ ∣ PfL ∣ Γi ⟨ idC ⟩))

    ∨elim : ∀{Γt}{K L C}{Γ : Conp Γt} -> 
        Pf (Γ ▸p K) C -> 
        Pf (Γ ▸p L) C -> 
        Pf Γ (K ∨ L) -> 
        Pf Γ C
    ∣ ∨elim {Γt}{K}{L}{C}{Γ} PfKC PfLC PfK∨L ∣ {I} {i} Γi = 
        C .glue (∣ PfK∨L ∣ Γi) 
        λ {J} f J⊩R → 
            ind+p 
            (λ v → ∣ C ∣ J (Γt ∶ i ⟨ f ⟩)) 
            (λ x → ∣ PfKC ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ x)) 
            (λ y → ∣ PfLC ∣ ((Γ ∶ Γi ⟨ f ⟩) ,Σ y)) 
            J⊩R

    ∀' : {Γt : Cont} -> For (Γt ▸t) -> For Γt
    ∣ ∀' {Γt} K ∣ I Γi = (J : Ob) -> (f : Hom J I) -> (d : D J) -> 
        ∣ K ∣ J ((Γt ∶ Γi ⟨ f ⟩) ,Σ d)
    _∶_⟨_⟩ (∀' {Γt} K) {I} {J} {i} x f J' g d = 
        substp 
            (λ z -> ∣ K ∣ J' (z ,Σ d)) 
            (Γt ∶⟨∘⟩) 
            (x J' (f ∘C g) d) 
    glue (∀' {Γt} K){I} {i} {R} I◁R x J f d = 
        K .glue {J}{Γt ∶ i ⟨ f ⟩ ,Σ d} 
        (I◁R [ f ]ᶜ) λ {K'} g y → 
            substp 
                (λ z -> ∣ K ∣ K' (z ,Σ D∶ d ⟨ g ⟩)) 
                (trans (Γt ∶⟨id⟩) (Γt ∶⟨∘⟩)) 
                (x {K'} (f ∘C g) y K' idC D∶ d ⟨ g ⟩)

    ∀[] : {Γt : Cont} {K : For (Γt ▸t)} {Δt : Cont} {γt : Subt Δt Γt} ->
      (∀' K [ γt ]F) ≡ ∀' (K [ (γt ∘t pt) ,t qt {Δt} ]F)
    ∀[] {Γt} {K} {Δt} {γt} = 
        mkForEq 
        {Δt}{∣ ∀' K [ γt ]F ∣}{∣ ∀' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F) ∣}
        {(∀' K [ γt ]F) ∶_⟨_⟩}
        {(∀' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F)) ∶_⟨_⟩}
        {glue (∀' K [ γt ]F)}
        {glue (∀' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F))}
        (funext (λ I -> 
        funext (λ Δi -> 
        cong (λ Z -> (J : Ob)(f : Hom J I)(d : D J) -> Z J f d) 
        (funext λ J -> funext (λ f -> funext (λ d -> 
            cong (λ z -> ∣ K ∣ J (z ,Σ d)) (nat γt)))))))

    ∀intro : {Γt : Cont} {K : For (Γt ▸t)} {Γ : Conp Γt} ->
      Pf (Γ [ pt ]C) K -> Pf Γ (∀' K)
    ∣ ∀intro {Γt}{K}{Γ} PfK ∣ Γi J f d = ∣ PfK ∣ (Γ ∶ Γi ⟨ f ⟩)

    ∀elim : {Γt : Cont} {K : For (Γt ▸t)} {Γ : Conp Γt} ->
      Pf Γ (∀' K) -> Pf (Γ [ pt ]C) K
    ∣ ∀elim {Γt}{K}{Γ} PfK ∣ {I} {Γti ,Σ d} Γi = 
        substp 
            (λ z -> ∣ K ∣ I (z ,Σ d)) 
            (Γt ∶⟨id⟩) 
            (∣ PfK ∣ Γi I idC d)

    ∃-sieve : (Γt : Cont) -> (K : For (Γt ▸t)) -> (I : Ob) -> (Γi : ∣ Γt ∣ I) ->
        Sieve I
    ∃-sieve Γt K I Γi .Sh.Sieve.R J f = 
        ∃ (D J) λ d -> ∣ K ∣ J ((Γt ∶ Γi ⟨ f ⟩) ,Σ d)
    ∃-sieve Γt K I Γi .Sh.Sieve.restr {J} {f} {K'} (Dj ,∃ Kj) g = 
        D∶ Dj ⟨ g ⟩ ,∃ 
        substp 
            (λ z -> ∣ K ∣ K' (z ,Σ D∶ Dj ⟨ g ⟩)) 
            (sym (Γt ∶⟨∘⟩)) 
            (K ∶ Kj ⟨ g ⟩)

    ∃-[]ˢ-⟨⟩ : {Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}
        {K : For (Γt ▸t)} ->
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
    ∣ ∃' {Γt} K ∣ I Γi = I ◁ (∃-sieve Γt K I Γi)
    _∶_⟨_⟩ (∃' {Γt} K) {I} {J} {i} x f = 
        substp 
            (J ◁_) 
            (∃-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {K}) 
            (x [ f ]ᶜ)
    glue (∃' {Γt} K) {I} {i} {R} I◁R x = 
        local I◁R λ {J} f J⊩R → 
            substp 
                (J ◁_) 
                (sym (∃-[]ˢ-⟨⟩ {Γt} {I} {J} {i} {f} {K})) 
                (x {J} f J⊩R)
    
    ∃[] : {Γt : Cont} {K : For (Γt ▸t)} {Δt : Cont} {γt : Subt Δt Γt} →
      (∃' K [ γt ]F) ≡ ∃' (K [ (γt ∘t pt) ,t (qt {Δt}) ]F)
    ∃[] {Γt} {K} {Δt} {γt} = 
        mkForEq
        {Δt} 
        {∣ ∃' K [ γt ]F ∣}
        {∣ ∃' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F) ∣}
        {(∃' K [ γt ]F) ∶_⟨_⟩}
        {(∃' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F)) ∶_⟨_⟩}
        {glue (∃' K [ γt ]F)}
        {glue (∃' {Δt} (K [ (γt ∘t pt) ,t (qt {Δt}) ]F))}
        (funext (λ J → funext (λ x → cong (J ◁_) 
        (mkSieveEq 
        (Sh.Sieve.R (∃-sieve Γt K J (∣ γt ∣ J x))) 
        (Sh.Sieve.R (∃-sieve Δt (K [ (γt ∘t pt) ,t (qt {Δt}) ]F) J x)) 
        {Sh.Sieve.restr (∃-sieve Γt K J (∣ γt ∣ J x))}
        {Sh.Sieve.restr (∃-sieve Δt (K [ (γt ∘t pt) ,t (qt {Δt}) ]F) J x)}
        (funext (λ K' → funext (λ y → cong (∃ (D K')) 
            (funext (λ d → cong (λ z -> ∣ K ∣ K' (z ,Σ d)) (nat γt))))))))))

    ∃intro : {Γt : Cont} {K : For (Γt ▸t)} (t : Tm Γt) {Γ : Conp Γt} ->
      Pf Γ (K [ idt ,t t ]F) -> Pf Γ (∃' K)
    ∣ ∃intro {Γt}{K} t {Γ} PfK ∣ {I}{i} Γi = 
        maximal ((∣ t ∣ I i) ,∃ 
        substp 
            (λ z -> ∣ K ∣ I (z ,Σ ∣ t ∣ I i)) 
            (sym (Γt ∶⟨id⟩)) 
            (∣ PfK ∣ Γi))
    
    ∃elim : {Γt : Cont} {K : For (Γt ▸t)} {Γp : Conp Γt}{L : For Γt} ->
      Pf Γp (∃' K) -> 
      Pf ((Γp [ pt ]C) ▸p (K [ _,t_ {Γt} pt (qt {Γt}) ]F)) (L [ pt ]F) -> 
      Pf Γp L
    ∣ ∃elim {Γt}{K}{Γp}{L} Pf∃K PfKL ∣ {I} {i} Γi = 
        L .glue (∣ Pf∃K ∣ Γi) λ {J} f x → 
        with∃ x (λ d Kj → ∣ PfKL ∣ ((Γp ∶ Γi ⟨ f ⟩) ,Σ Kj))

    Eq-sieve : (Γt : Cont) -> (t t' : Tm Γt) -> (I : Ob) -> (Γi : ∣ Γt ∣ I) -> 
        Sieve I
    Eq-sieve Γt t t' I Γi .Sh.Sieve.R J f = 
        ∣ t ∣ J (Γt ∶ Γi ⟨ f ⟩) ≡ ∣ t' ∣ J (Γt ∶ Γi ⟨ f ⟩)
    Eq-sieve Γt t t' I Γi .Sh.Sieve.restr {J} {f} {K} x g = 
        trans 
            (trans (sym (nat t)) D∶⟨∘⟩) 
            (trans 
                (cong (D∶_⟨ g ⟩) (trans 
                    (nat t) 
                    (trans x (sym (nat t')))))
                (trans 
                    (sym D∶⟨∘⟩) 
                    (nat t')))

    Eq-[]ˢ-⟨⟩ : {Γt : Cont}{I J : Ob}{Γi : ∣ Γt ∣ I}{f : Hom J I}
        {t t' : Tm Γt} ->
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
    _∶_⟨_⟩ (Eq {Γt} t t') {I} {J} {i} x f = 
        substp 
            (J ◁_) 
            (Eq-[]ˢ-⟨⟩ {Γt}{I}{J}{i}{f}{t}{t'}) 
            (x [ f ]ᶜ)
    glue (Eq {Γt} t t') {I} {i} {R} I◁R x = 
        local I◁R λ {J} f y → 
            substp 
                (J ◁_) 
                (sym (Eq-[]ˢ-⟨⟩ {Γt}{I}{J}{i}{f}{t}{t'})) 
                (x f y)

    Eq[] : {Γt Δt : Cont} {γt : Subt Δt Γt} {t t' : Tm Γt} ->
      (Eq t t' [ γt ]F) ≡ Eq (t [ γt ]t) (t' [ γt ]t)
    Eq[] {Γt}{Δt}{γt}{t}{t'} = 
        mkForEq {Δt} 
        {∣ Eq t t' [ γt ]F ∣}
        {∣ Eq (t [ γt ]t) (t' [ γt ]t) ∣} 
        {(Eq t t' [ γt ]F) ∶_⟨_⟩} 
        {(Eq (t [ γt ]t) (t' [ γt ]t)) ∶_⟨_⟩} 
        {glue (Eq t t' [ γt ]F)} 
        {glue (Eq (t [ γt ]t) (t' [ γt ]t))} 
        (funext (λ J → funext (λ x → cong (J ◁_) 
        (mkSieveEq 
        {J}
        (Sh.Sieve.R (Eq-sieve Γt t t' J (∣ γt ∣ J x))) 
        (Sh.Sieve.R (Eq-sieve Δt (t [ γt ]t) (t' [ γt ]t) J x)) 
        {Sh.Sieve.restr (Eq-sieve Γt t t' J (∣ γt ∣ J x))}
        {Sh.Sieve.restr (Eq-sieve Δt (t [ γt ]t) (t' [ γt ]t) J x)}
        (funext (λ K → funext (λ y → 
            cong-bin _≡_ 
                (cong (∣ t ∣ K) (nat γt)) 
                (cong (∣ t' ∣ K) (nat γt)))))))))
    
    Eqrefl : {Γt : Cont} {t : Tm Γt} {Γ : Conp Γt} -> Pf Γ (Eq t t)
    ∣ Eqrefl ∣ x = maximal refl

    subst' : {Γt : Cont} (K : For (Γt ▸t)) {t t' : Tm Γt} {Γ : Conp Γt} ->
      Pf Γ (Eq t t') -> Pf Γ (K [ idt ,t t ]F) -> Pf Γ (K [ idt ,t t' ]F)
    ∣ subst' {Γt} K {t}{t'} t=t' PfK ∣ {I}{i} x = 
        K .glue (∣ t=t' ∣ x) (λ {J} f y → 
        substp 
            (λ z -> ∣ K ∣ J ((Γt ∶ i ⟨ f ⟩) ,Σ z)) 
            (trans (nat t) (trans y (sym (nat t')))) 
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
        ; rel[] = λ {Γ}{n}{a}{ts}{Δ}{γ} -> rel[] {Γ}{n}{a}{ts}{Δ}{γ}
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
        ; ∨[] = λ {Γt}{K}{L}{Δt}{γt} -> ∨[] {Γt}{K}{L}{Δt}{γt}
        ; ∨elim = λ {Γt}{K}{L}{C} -> ∨elim {Γt}{K}{L}{C}
        ; ∨intro₁ = λ {Γt}{K}{L} -> ∨intro₁ {Γt}{K}{L}
        ; ∨intro₂ = λ {Γt}{K}{L} -> ∨intro₂ {Γt}{K}{L}
        ; ∀' = ∀'
        ; ∀[] = λ {Γt}{K}{Δt}{γt} -> ∀[] {Γt}{K}{Δt}{γt}
        ; ∀intro = λ {Γt}{K}{Γ} -> ∀intro {Γt}{K}{Γ} 
        ; ∀elim = λ {Γt}{K}{Γ} -> ∀elim {Γt}{K}{Γ}
        ; ∃' = ∃'
        ; ∃[] = λ {Γt}{K}{Δt}{γt} -> ∃[] {Γt}{K}{Δt}{γt}
        ; ∃intro = λ {Γt}{K} -> ∃intro {Γt}{K}
        ; ∃elim = λ {Γt}{K}{Γp}{L} -> ∃elim {Γt}{K}{Γp}{L} 
        ; Eq = Eq
        ; Eq[] = λ {Γt}{Δt}{γt}{t}{t'} -> Eq[] {Γt}{Δt}{γt}{t}{t'}
        ; Eqrefl = λ {Γt}{t}{Γ} -> Eqrefl {Γt}{t}{Γ}
        ; subst' = subst'
        }