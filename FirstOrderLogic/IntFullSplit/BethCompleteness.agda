{-# OPTIONS --prop #-}
open import lib

module FirstOrderLogic.IntFullSplit.BethCompleteness
    (funar : ℕ -> Set)
    (relar : ℕ -> Set)
    where
        
    open import FirstOrderLogic.IntFullSplit.BethModel funar relar
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

    _[_]P' : ∀{Γ Δ A} -> I.Pf (proj₂ Γ) A -> ((γt ,Σ γp) : (Sub Δ Γ)) -> I.Pf (proj₂ Δ) (A I.[ γt ]F)
    x [ γ@(γt ,Σ γp) ]P' = x I.[ γt ]p I.[ γp ]P

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
    data _◁_ (Γ : Con)(R : Sieve Γ) : Prop where
        maximal : (x : ⟨ Γ , id ⟩⊩ R) -> Γ ◁ R
        ◁-⊥ : (x : I.Pf (proj₂ Γ) ⊥) -> Γ ◁ R
        ◁-∨ : ∀ {A B} -> 
            (f : (∀ {Δ : Con} -> (γ : Sub Δ Γ) -> I.Pf (proj₂ Δ) (A [ proj₁ γ ]F) -> Δ ◁ (R [ γ ]ˢ))) ->
            (g : (∀ {Δ : Con} -> (γ : Sub Δ Γ) -> I.Pf (proj₂ Δ) (B [ proj₁ γ ]F) -> Δ ◁ (R [ γ ]ˢ))) ->
            (x : I.Pf (proj₂ Γ) (A I.∨ B)) ->  Γ ◁ R
        ◁-∃ : ∀{A} -> 
            (f : (∀ {Δ} (γ : Sub Δ Γ) -> 
                (d : I.Tm (proj₁ Δ)) -> 
                I.Pf (proj₂ Δ) (A [ (proj₁ γ) ,t d ]F) -> 
                Δ ◁ (R [ γ ]ˢ))) ->
            (x : I.Pf (proj₂ Γ) (I.∃' A)) -> 
            Γ ◁ R
        ◁-Eq : ∀{t t' : I.Tm (proj₁ Γ)}{R' : Sieve (Γ ▸t')} ->
            (x : I.Pf (proj₂ Γ) (I.Eq t t')) ->
            (f : (∀ {Δ} (γ : Sub Δ Γ) -> Δ ◁ (R [ γ ]ˢ))) ->
            (eq : R ≡ R' [ id ,t' t' ]ˢ) -> 
            Γ ◁ R

    _[_]ᶜ : ∀{Γ Δ R} -> Γ ◁ R → (γ : Sub Δ Γ) → Δ ◁ (R [ γ ]ˢ)
    (_[_]ᶜ {Γ}{Δ}{R} (maximal x) γ) = maximal (substp (Sh.Sieve.R R Δ) (trans idl' (sym (idr' {f = γ}))) (R .Sh.Sieve.restr x γ))
    ◁-⊥ x [ (γt ,Σ γp) ]ᶜ = ◁-⊥ (x I.[ γt ]p I.[ γp ]P)
    (_[_]ᶜ {Γ}{Δ}{R} (◁-∨ x y z) γ@(γt ,Σ γp)) = 
        ◁-∨ 
        (λ {Θ@(Θt ,Σ Θp)} δ l → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = R}) (x (γ ∘ δ) (substp (I.Pf Θp) (sym [∘]F) l)))
        (λ {Θ@(Θt ,Σ Θp)} δ k → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = R}) (y (γ ∘ δ) (substp (I.Pf Θp) (sym [∘]F) k)))
        (z I.[ γt ]p I.[ γp ]P)
    (_[_]ᶜ {Γ}{Δ}{R} (◁-∃ {A} x Pf∃A) γ@(γt ,Σ γp)) = 
        ◁-∃ 
        (λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) d l → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = R}) (x (γ ∘ δ) d (substp (I.Pf Θp) (trans (sym [∘]F) (cong (A [_]F) (cong (_,t d) (trans ass (cong (γt I.∘t_) ▸tβ₁))))) l))) 
        (Pf∃A [ γt ]p [ γp ]P)
    (_[_]ᶜ {Γ@(Γt ,Σ Γp)}{Δ@(Δt ,Σ Δp)}{R} (◁-Eq {t}{t'}{K} PfEq PfKt x) γ@(γt ,Σ γp)) = 
        ◁-Eq {Δ}{R [ γ ]ˢ}{t [ γt ]t}{t' [ γt ]t}{R [ γ ∘ pt' ]ˢ} 
        (PfEq [ γ ]P') 
        (λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = R}) (PfKt (γ ∘ δ))) 
        (trans 
            ((cong (λ z -> R [ z ]ˢ) (mk,sp= {b = γp} {b' = proj₂ ((γ ∘ pt') ∘ (id ,t' (t' I.[ γt ]t)))} 
                (trans (trans (sym idr) (cong (γt I.∘t_) (sym (▸tβ₁ {γ = I.idt}{t = t' I.[ γt ]t})))) (sym ((ass {γ = γt}{δ = I.pt}{θ = I.idt I.,t (t' I.[ γt ]t)}))))))) 
            ([∘]ˢ {f = γ ∘ pt'}{g = id ,t' (t' [ γt ]t)}{s = R}))
    
    local : ∀{Γ R S} -> Γ ◁ R →
      ({Δ : Con} (γ : Sub Δ Γ) → ⟨ Δ , γ ⟩⊩ R → Δ ◁ (S [ γ ]ˢ)) → Γ ◁ S
    local {Γ}{R}{S} (maximal Γ⊩R ) x = substp (Γ ◁_) ([id]ˢ {Γ}{S}) (x id Γ⊩R)
    local {Γ}{R}{S} (◁-⊥ Pf⊥) x = ◁-⊥ Pf⊥
    local {Γ}{R}{S} (◁-∨ PfAC PfBC PfAB) x = 
        ◁-∨ 
        (λ {Δ} γ a → local (PfAC γ a) (λ {Θ} δ l → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = S}) (x (γ ∘ δ) l))) 
        (λ {Δ} γ b → local (PfBC γ b) (λ {Θ} δ k → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = S}) (x (γ ∘ δ) k))) 
        PfAB
    local {Γ}{R}{S} (◁-∃ PfAC Pf∃A) x = 
        ◁-∃ 
        (λ {Δ} γ d a → local (PfAC γ d a) λ {Θ} δ l → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = S}) (x (γ ∘ δ) l)) 
        Pf∃A
    local {Γ}{R}{S} (◁-Eq {t}{t'}{K} PfEq PfKt eq) x = 
        ◁-Eq {Γ}{S}{t}{t'}{S [ pt' ]ˢ}
        PfEq 
        (λ {Δ} γ → local (PfKt γ) λ {Θ} δ l → substp (Θ ◁_) ([∘]ˢ {f = γ}{g = δ}{s = S}) (x (γ ∘ δ) l)) 
        (trans (trans (sym [id]ˢ) (cong (λ z -> S [ z ]ˢ) (mk,sp= {b = proj₂ id} {b' = proj₂ (pt' ∘ (id ,t' t'))} (sym (▸tβ₁ {γ = I.idt}{t = t'}))))) ([∘]ˢ {f = pt'}{g = id ,t' t'}{s = S}))

    J : Top
    J .Sh.Top._◁_ = _◁_
    J .Sh.Top._[_]ᶜ = _[_]ᶜ
    J .Sh.Top.maximal = maximal
    J .Sh.Top.local = local

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
        {-# TERMINATING #-}
        
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

        -- Reify ∨, Eq, Rel with equality for "f"

        reify   : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For Γt) -> ∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ) (reflect-cont Γt γt) -> I.Pf Δ (A I.[ γt ]F)        
        reify-⊥ : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt} -> ∣ ⟦ I.⊥ {Γt} ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ I.⊥        
        reify-∨ : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A B : I.For Γt) -> ∣ ⟦ A I.∨ B ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((A I.∨ B) I.[ γt ]F)    
        reify-∃ : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(A : I.For (Γt I.▸t)) -> ∣ ⟦ I.∃' A  ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((I.∃' A) I.[ γt ]F)    
        reify-Eq  : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(t t' : I.Tm Γt) -> ∣ ⟦ I.Eq t t'  ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((I.Eq t t') I.[ γt ]F)    
        reify-rel : ∀{Γt Δt}{Δ : I.ConPf Δt}{γt : I.Subt Δt Γt}(n : ℕ)(a : relar n)(ts : I.Tms Γt n) -> ∣ ⟦ I.rel n a ts  ⟧For ∣ (Δt ,Σ Δ) (reflect-cont {Δt}{Δ} Γt γt) -> I.Pf Δ ((I.rel n a ts) I.[ γt ]F)    

        reify-⊥ (◁-⊥ x) = I.exfalso x
        reify-⊥ {Γt}{Δt}{Δ}{γt} (◁-∨ {A}{B} f g x) = 
            I.∨elim 
            (reify-⊥ {Γt}{Δt}{Δ I.▸p A}{γt} (f pp' qp')) 
            (reify-⊥ {Γt}{Δt}{Δ I.▸p B}{γt} (g pp' qp')) 
            x
        reify-⊥ {Γt}{Δt}{Δ}{γt} (◁-∃ {A} f x) = I.∃elim x (reify-⊥ {Γt I.▸t}{Δt I.▸t}{Δ I.[ I.pt ]C I.▸p A I.[ I.pt I.,t var V.vz ]F}{γt ↑t} (f (I.pt ,Σ I.pp) (qt' {Δt ,Σ Δ}) I.qp))
        reify-⊥ {Γt}{Δt}{Δ}{γt} (◁-Eq {t}{t'}{R} x f eq) =
            reify-⊥ {Γt}{Δt}{Δ}{γt} (f id)

        []ˢ-∨-sieve : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{A B : I.For Γt} ->
            (∨-sieve ⟦ Γt ⟧Cont Δ (reflect-cont Γt γt) ⟦ A ⟧For ⟦ B ⟧For) [ δ ]ˢ
            ≡
            ∨-sieve ⟦ Γt ⟧Cont Θ (reflect-cont Γt (γt I.∘t δt)) ⟦ A ⟧For ⟦ B ⟧For
        []ˢ-∨-sieve {Γt}{Δ@(Δt ,Σ Δp)}{Θ@(Θt ,Σ Θp)}{γt}{δ@(δt ,Σ δp)}{A}{B} = 
            mkSieveEq 
            (Sh.Sieve.R (∨-sieve ⟦ Γt ⟧Cont Δ (reflect-cont Γt γt) ⟦ A ⟧For ⟦ B ⟧For [ δ ]ˢ)) 
            (Sh.Sieve.R (∨-sieve ⟦ Γt ⟧Cont Θ (reflect-cont Γt (γt I.∘t δt)) ⟦ A ⟧For ⟦ B ⟧For))
            {λ {J}{f}{K} x g → Sh.Sieve.restr (∨-sieve ⟦ Γt ⟧Cont Δ (reflect-cont Γt γt) ⟦ A ⟧For ⟦ B ⟧For [ δ ]ˢ) {J}{f}{K} x g}
            {Sh.Sieve.restr (∨-sieve ⟦ Γt ⟧Cont Θ (reflect-cont Γt (γt I.∘t δt)) ⟦ A ⟧For ⟦ B ⟧For)}
            (funext (λ Ξ → funext (λ θ@(θt ,Σ θp) → 
                cong-bin (_+p_) 
                (cong (∣ ⟦ A ⟧For ∣ Ξ) (trans (sym (⟨⟩-reflect-cont {γt = γt}{δ = δ ∘ θ})) (trans (cong (reflect-cont Γt) (sym ass)) (⟨⟩-reflect-cont {γt = γt I.∘t δt}{δ = θ})))) 
                (cong (∣ ⟦ B ⟧For ∣ Ξ) (trans (sym (⟨⟩-reflect-cont {γt = γt}{δ = δ ∘ θ})) (trans (cong (reflect-cont Γt) (sym ass)) (⟨⟩-reflect-cont {γt = γt I.∘t δt}{δ = θ})))))))

        reify-∨ {Γt}{Δt}{Δ}{γt} A B (maximal (inj₁ x)) = I.∨intro₁ (reify A (substp (∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ)) (⟦ Γt ⟧Cont ∶⟨id⟩) x))
        reify-∨ {Γt}{Δt}{Δ}{γt} A B (maximal (inj₂ x)) = I.∨intro₂ (reify B (substp (∣ ⟦ B ⟧For ∣ (Δt ,Σ Δ)) (⟦ Γt ⟧Cont ∶⟨id⟩) x))
        reify-∨ {Γt}{Δt}{Δ}{γt} A B (◁-⊥ x) = I.exfalso x
        reify-∨ {Γt}{Δt}{Δ}{γt} A B (◁-∨ {A'}{B'} f g x) =
            let f' = f {Δt ,Σ (Δ I.▸p A')} pp' qp' in
            let g' = g {Δt ,Σ (Δ I.▸p B')} pp' qp' in
            I.∨elim {Δt}{A'}{B'}{(A I.∨ B) I.[ γt ]F}{Δ}
            (reify-∨ {Γt}{Δt}{Δ I.▸p A'}{γt} A B
                (substp ((Δt ,Σ (Δ I.▸p A')) ◁_)
                (trans ([]ˢ-∨-sieve {Γt}{Δt ,Σ Δ}{Δt ,Σ (Δ I.▸p A')}{γt}{pp'}{A}{B})
                (cong (λ z -> ∨-sieve ⟦ Γt ⟧Cont (Δt ,Σ (Δ I.▸p A')) (reflect-cont Γt z) ⟦ A ⟧For ⟦ B ⟧For) idr)) f')) 
            (reify-∨ {Γt} {Δt} {Δ I.▸p B'} {γt} A B 
                (substp ((Δt ,Σ (Δ I.▸p B')) ◁_) 
                (trans ([]ˢ-∨-sieve {Γt}{Δt ,Σ Δ}{Δt ,Σ (Δ I.▸p B')}{γt}{pp'}{A}{B}) 
                (cong (λ z -> ∨-sieve ⟦ Γt ⟧Cont (Δt ,Σ (Δ I.▸p B')) (reflect-cont Γt z) ⟦ A ⟧For ⟦ B ⟧For) idr)) g')) 
            x
        reify-∨ {Γt}{Δt}{Δ}{γt} A B (◁-∃ {A'} f x) =
            I.∃elim x 
            (substp (I.Pf _) (trans I.∨[] (cong-bin I._∨_ [∘]F [∘]F)) 
            (reify-∨ {Γt}{Δt I.▸t}{Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t var V.vz ]F}{γt I.∘t I.pt} A B 
            (substp (λ z -> z)
            (cong (((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F)) ◁_) ([]ˢ-∨-sieve {Γt}{Δt ,Σ Δ}{(Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F)}{γt}{I.pt ,Σ I.pp}{A}{B})) 
            (f {(Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t (qt' {Δt ,Σ Δ}) ]F)} (I.pt ,Σ I.pp) (qt' {Δt ,Σ Δ}) I.qp))))
        reify-∨ {Γt}{Δt}{Δ}{γt} A B (◁-Eq {t}{t'}{K} x f eq) = 
            reify-∨ A B 
            (substp ((Δt ,Σ Δ) ◁_) ([id]ˢ {s = ∨-sieve ⟦ Γt ⟧Cont (Δt ,Σ Δ) (reflect-cont Γt γt) ⟦ A ⟧For ⟦ B ⟧For}) (f id)) 

        mk∃= : ∀{i j}{A : Set i}{B : A -> Prop j}{B' : A -> Prop j} -> B ≡ B' -> ∃ A B ≡ ∃ A B'
        mk∃= {i}{j}{A}{B}{B'} refl = refl

        []ˢ-∃-sieve : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{A : I.For (Γt I.▸t)} ->
            (∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For Δ (reflect-cont Γt γt)) [ δ ]ˢ
            ≡
            ∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For Θ (reflect-cont Γt (γt I.∘t δt))
        []ˢ-∃-sieve {Γt}{Δ@(Δt ,Σ Δp)}{Θ@(Θt ,Σ Θp)}{γt}{δ@(δt ,Σ δp)}{A} = 
            mkSieveEq 
            (Sh.Sieve.R ((∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For Δ (reflect-cont Γt γt)) [ δ ]ˢ)) 
            (Sh.Sieve.R (∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For Θ (reflect-cont Γt (γt I.∘t δt))))
            {λ {J}{f}{K} x g → Sh.Sieve.restr ((∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For Δ (reflect-cont Γt γt)) [ δ ]ˢ) {J}{f}{K} x g}
            {Sh.Sieve.restr (∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For Θ (reflect-cont Γt (γt I.∘t δt)))}
            (funext (λ Ξ@(Ξt ,Σ Ξp) → funext (λ θ@(θt ,Σ θp) → 
                mk∃= (funext (λ t → cong (λ z -> ∣ ⟦ A ⟧For ∣ Ξ (z ,Σ t)) (sym (trans (cong (⟦ Γt ⟧Cont ∶_⟨ θ ⟩) (⟨⟩-reflect-cont {γt = γt}{δ = δ})) (sym (⟦ Γt ⟧Cont ∶⟨∘⟩)))))))))

        reify-∃ {Γt}{Δt}{Δ}{γt} A (maximal (a ,∃ x)) = I.∃intro a (substp (I.Pf Δ) [∘]F (reify A (substp (∣ ⟦ A ⟧For ∣ (Δt ,Σ Δ)) (cong (_,Σ a) (trans (⟦ Γt ⟧Cont ∶⟨id⟩) (cong (reflect-cont Γt) (trans (trans (sym idr) (cong (γt I.∘t_) (sym ▸tβ₁))) (sym ass))))) x)))
        reify-∃ A (◁-⊥ x) = I.exfalso x
        reify-∃ {Γt}{Δt}{Δ}{γt} A (◁-∨ {A'}{B'} f g x) = 
            I.∨elim 
            (reify-∃ A (substp ((Δt ,Σ (Δ I.▸p A')) ◁_) (trans ([]ˢ-∃-sieve {γt = γt}{δ = pp'}{A = A}) (cong (∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For _) (cong (reflect-cont Γt) idr))) (f pp' qp'))) 
            (reify-∃ A (substp ((Δt ,Σ (Δ I.▸p B')) ◁_) (trans ([]ˢ-∃-sieve {γt = γt}{δ = pp'}{A = A}) (cong (∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For _) (cong (reflect-cont Γt) idr))) (g pp' qp'))) 
            x
        reify-∃ {Γt}{Δt}{Δ}{γt} A (◁-∃ {A'} f x) = 
            I.∃elim x 
            let fx = (f {(Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F)} (I.pt ,Σ I.pp) (qt' {Δt ,Σ Δ}) I.qp) in
            let eq = []ˢ-∃-sieve {Γt}{(Δt ,Σ Δ)}{((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F))}{γt}{(I.pt ,Σ I.pp)}{A} in
            let fx' = substp (λ z -> z) (cong (((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F)) ◁_) eq) fx in
            let reif = reify-∃ {Γt}{Δt I.▸t}{Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F}{(γt I.∘t I.pt)} A fx' in
            let reif' = 
                    substp 
                    (I.Pf (Δ I.[ I.pt ]C I.▸p (A' I.[ I.pt I.,t I.qt ]F))) 
                    (trans 
                        I.∃[] 
                        (trans 
                            (cong (λ z → I.∃' (A I.[ z ]F)) (trans (cong (I._,t I.qt) (ass {γ = γt}{δ = I.pt}{θ = I.pt})) (cong (I._,t I.qt) (trans (cong (γt I.∘t_) (sym (▸tβ₁ {γ = I.pt I.∘t I.pt}))) (sym (ass {γ = γt}{δ = I.pt})))))) 
                            (cong I.∃' ([∘]F {γ = γt I.∘t I.pt I.,t I.qt}{δ = I.pt I.∘t I.pt I.,t I.qt})))) 
                    reif in
            reif'
        reify-∃ {Γt}{Δt}{Δ}{γt} A (◁-Eq {t}{t'}{K} x f eq) = 
            reify-∃  A (substp ((Δt ,Σ Δ) ◁_) ([id]ˢ {s = ∃-sieve ⟦ Γt ⟧Cont ⟦ A ⟧For (Δt ,Σ Δ) (reflect-cont Γt γt)}) (f id))

        []ˢ-Eq-sieve : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{t t' : I.Tm Γt} ->
            (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Δ (reflect-cont Γt γt)) [ δ ]ˢ
            ≡
            (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Θ (reflect-cont Γt (γt I.∘t δt)))
        []ˢ-Eq-sieve {Γt}{Δ@(Δt ,Σ Δp)}{Θ@(Θt ,Σ Θp)}{γt}{δ@(δt ,Σ δp)}{t}{t'} = 
            mkSieveEq
            (Sh.Sieve.R ((Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Δ (reflect-cont Γt γt)) [ δ ]ˢ)) 
            (Sh.Sieve.R (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Θ (reflect-cont Γt (γt I.∘t δt))))
            {λ {J}{f}{K} x g → Sh.Sieve.restr (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Δ (reflect-cont Γt γt) [ δ ]ˢ) {J}{f}{K} x g}
            {Sh.Sieve.restr (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Θ (reflect-cont Γt (γt I.∘t δt)))}
            (funext (λ Ξ@(Ξt ,Σ Ξp) → funext (λ θ@(θt ,Σ θp) -> 
                cong-bin _≡_ 
                (cong ((Subt.α ⟦ t ⟧Tm) Ξ) (trans (trans (sym (⟨⟩-reflect-cont {γt = γt}{δ = δ ∘ θ})) (cong (reflect-cont Γt) (sym ass))) (⟨⟩-reflect-cont {γt = γt I.∘t δt}{δ = θ}))) 
                (cong (Subt.α ⟦ t' ⟧Tm Ξ) ((trans (trans (sym (⟨⟩-reflect-cont {γt = γt}{δ = δ ∘ θ})) (cong (reflect-cont Γt) (sym ass))) (⟨⟩-reflect-cont {γt = γt I.∘t δt}{δ = θ})))))))

        reify-Eq {Γt}{Δt}{Δ}{γt} t t' (maximal x) =
            let eqt = 
                    (trans 
                    (cong (I.Eq (t I.[ γt ]t)) 
                    (trans (sym (reflect-Tm {Δ = Δ}{γt = γt}{t = t})) 
                    (trans (cong (∣ ⟦ t ⟧Tm ∣ (Δt ,Σ Δ)) (sym (⟦ Γt ⟧Cont ∶⟨id⟩))) 
                    (trans x 
                    (trans ((cong (∣ ⟦ t' ⟧Tm ∣ (Δt ,Σ Δ))) (⟦ Γt ⟧Cont ∶⟨id⟩)) 
                    (reflect-Tm {Δ = Δ}{γt = γt}{t = t'})))))) 
                    refl) in 
            substp (I.Pf Δ) eqt (I.ref {a = t I.[ γt ]t})
        reify-Eq t t' (◁-⊥ x) = I.exfalso x
        reify-Eq {Γt}{Δt}{Δ}{γt} t t' (◁-∨ {A}{B} f g x) = 
            let f' = substp (((Δt ,Σ Δ) ▸p' A) ◁_ ) (trans ([]ˢ-Eq-sieve {Γt}{Δt ,Σ Δ}{(Δt ,Σ Δ) ▸p' A}{γt}{pp'}{t}{t'}) (cong (λ z -> Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm ((Δt ,Σ Δ) ▸p' A) (reflect-cont Γt z)) (idr {γ = γt}))) (f {(Δt ,Σ Δ) ▸p' A} pp' qp') in
            let g' = substp (((Δt ,Σ Δ) ▸p' B) ◁_ ) (trans ([]ˢ-Eq-sieve {Γt}{Δt ,Σ Δ}{(Δt ,Σ Δ) ▸p' B}{γt}{pp'}{t}{t'}) (cong (λ z -> Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm ((Δt ,Σ Δ) ▸p' B) (reflect-cont Γt z)) (idr {γ = γt}))) (g {(Δt ,Σ Δ) ▸p' B} pp' qp') in
            I.∨elim
            (reify-Eq t t' f')
            (reify-Eq t t' g')
            x
        reify-Eq {Γt}{Δt}{Δ}{γt} t t' (◁-∃ {A'} f x) = 
            I.∃elim x 
            let fx = (f {(Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F)} (I.pt ,Σ I.pp) (qt' {Δt ,Σ Δ}) I.qp) in
            let eq = []ˢ-Eq-sieve {Γt}{(Δt ,Σ Δ)}{((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F))}{γt}{(I.pt ,Σ I.pp)}{t}{t'} in
            let fx' = substp (λ z -> z) (cong (((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F)) ◁_) eq) fx in
            let reif = reify-Eq {Γt}{Δt I.▸t}{Δ I.[ I.pt ]C I.▸p A' I.[ I.pt I.,t I.qt ]F}{(γt I.∘t I.pt)} t t' fx' in
            let reif' = 
                    substp 
                    (I.Pf (Δ I.[ I.pt ]C I.▸p (A' I.[ I.pt I.,t I.qt ]F))) 
                    (trans (I.Eq[] {γt = γt I.∘t I.pt}{t = t}{t' = t'}) (cong-bin I.Eq ([∘]t {t = t}) ([∘]t {t = t'}))) 
                    reif in
            reif'
        reify-Eq {Γt}{Δt}{Δ}{γt} t t' (◁-Eq {k}{k'}{K} x f eq) = 
            reify-Eq t t' (substp ((Δt ,Σ Δ) ◁_) ([id]ˢ {s = Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm (Δt ,Σ Δ) (reflect-cont Γt γt)}) (f id))

        []ˢ-rel-sieve : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{n : ℕ}{a : relar n}{ts : I.Tms Γt n} ->
            (rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms Δ (reflect-cont Γt γt)) [ δ ]ˢ
            ≡
            (rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms Θ (reflect-cont Γt (γt I.∘t δt)))
        []ˢ-rel-sieve {Γt}{Δ@(Δt ,Σ Δp)}{Θ@(Θt ,Σ Θp)}{γt}{δ@(δt ,Σ δp)}{n}{a}{ts} = 
            mkSieveEq 
            (Sh.Sieve.R ((rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms Δ (reflect-cont Γt γt)) [ δ ]ˢ)) 
            (Sh.Sieve.R (rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms Θ (reflect-cont Γt (γt I.∘t δt))))
            {λ {J}{f}{K} x g → Sh.Sieve.restr (rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms Δ (reflect-cont Γt γt) [ δ ]ˢ) {J}{f}{K} x g}
            {Sh.Sieve.restr (rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms Θ (reflect-cont Γt (γt I.∘t δt)))}
            (funext (λ Ξ@(Ξt ,Σ Ξp) → funext (λ θ@(θt ,Σ θp) -> 
                cong (λ z -> I.Pf Ξp (rel n a (reifyTms (recTms Ξ ((Subt.α ⟦ ts ⟧Tms) Ξ z))))) 
                (trans (trans (sym (⟨⟩-reflect-cont {γt = γt}{δ = δ ∘ θ})) (cong (reflect-cont Γt) (sym ass))) (⟨⟩-reflect-cont {γt = γt I.∘t δt}{δ = θ})))))

        reify-rel n a ts (◁-⊥ x) = I.exfalso x
        reify-rel {Γt}{Δt}{Δ}{γt} n a ts (◁-∨ {A'}{B'} f g x) = 
            I.∨elim 
            (reify-rel n a ts (substp (((Δt ,Σ Δ) ▸p' A') ◁_) (trans ([]ˢ-rel-sieve {γt = γt}{δ = pp'}{n}{a}{ts}) (cong (λ z -> rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms ((Δt ,Σ Δ) ▸p' A') (reflect-cont Γt z)) idr)) (f pp' qp'))) 
            (reify-rel n a ts (substp (((Δt ,Σ Δ) ▸p' B') ◁_) (trans ([]ˢ-rel-sieve {γt = γt}{δ = pp'}{n}{a}{ts}) (cong (λ z -> rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms ((Δt ,Σ Δ) ▸p' B') (reflect-cont Γt z)) idr)) (g pp' qp'))) 
            x
        reify-rel {Γt}{Δt}{Δ}{γt} n a ts (◁-∃ {A} f x) = 
            let fx = (f {(Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A I.[ I.pt I.,t I.qt ]F)} (I.pt ,Σ I.pp) (qt' {Δt ,Σ Δ}) I.qp) in
            let eq = []ˢ-rel-sieve {Γt}{(Δt ,Σ Δ)}{((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A I.[ I.pt I.,t I.qt ]F))}{γt}{(I.pt ,Σ I.pp)}{n}{a}{ts} in
            let fx' = substp (λ z -> z) (cong (((Δt I.▸t) ,Σ (Δ I.[ I.pt ]C I.▸p A I.[ I.pt I.,t I.qt ]F)) ◁_) eq) fx in
            let reif = reify-rel {Γt}{Δt I.▸t}{Δ I.[ I.pt ]C I.▸p A I.[ I.pt I.,t I.qt ]F}{γt I.∘t I.pt} n a ts fx' in
            let reif' = substp (λ z -> z) (cong (λ z → I.Pf (Δ I.[ I.pt ]C I.▸p A I.[ I.pt I.,t var V.vz ]F) z) (trans I.rel[] (cong (rel n a) (I.[∘]ts {ts = ts}{γ = γt}{δ = I.pt})))) reif in
            I.∃elim x reif'
        reify-rel {Γt}{Δt}{Δ}{γt} n a ts (◁-Eq {t}{t'}{K} x f eq) = 
            reify-rel n a ts (substp ((Δt ,Σ Δ) ◁_) ([id]ˢ {s = rel-sieve ⟦ Γt ⟧Cont n a ⟦ ts ⟧Tms (Δt ,Σ Δ) (reflect-cont Γt γt)}) (f id))
        reify-rel zero a ts (maximal x) = x
        reify-rel {Γt} {Δt} {Δ} {γt} (suc n) a (ts ,Σ t) (maximal x) = 
            substp (I.Pf Δ) (cong (rel (suc n) a) 
            (mk,= 
                (trans (cong (λ z → reifyTms (recTms (Δt ,Σ Δ) (∣ ⟦ ts ⟧Tms ∣ (Δt ,Σ Δ) z))) (⟦ Γt ⟧Cont ∶⟨id⟩)) (reflect-Tms {γt = γt}{ts = ts})) 
                (trans (cong (∣ ⟦ t ⟧Tm ∣ (Δt ,Σ Δ)) (⟦ Γt ⟧Cont ∶⟨id⟩)) (reflect-Tm {γt = γt}{t = t}))))
            x

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

        reflect-Eq-sieve-Tm-eq1 : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) Ξ : Con}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{f@(ft ,Σ fp) : Sub Ξ Θ}{t : I.Tm Γt} -> 
            Subt.α ⟦ t I.[ γt ]t ⟧Tm Ξ (⟦ Δt ⟧Cont ∶ reflect-cont Δt δt ⟨ f ⟩)
            ≡
            Subt.α ⟦ t ⟧Tm Ξ (⟦ Γt ⟧Cont ∶ (reflect-cont Γt γt) ⟨ δ ∘ f ⟩)
        reflect-Eq-sieve-Tm-eq1  {Γt} {Δ@(Δt ,Σ Δp)} {Θ@(Θt ,Σ Θp)} {Ξ} {γt} {δ@(δt ,Σ δp)} {f@(ft ,Σ fp)} {t} = 
            trans 
                (cong (∣ ⟦ t I.[ γt ]t ⟧Tm ∣ Ξ) (sym (⟨⟩-reflect-cont {γt = δt}{δ = f})))
            (trans 
                (reflect-Tm {γt = δt I.∘t ft}{t I.[ γt ]t}) 
            (trans 
                (sym ([∘]t {t = t}{γ = γt}{δ = δt I.∘t ft}))  
            (trans 
                (sym (reflect-Tm {γt = γt I.∘t δt I.∘t ft}{t})) 
                (cong (∣ ⟦ t ⟧Tm ∣ Ξ) (⟨⟩-reflect-cont {γt = γt}{δ = δ ∘ f})))))

        reflect-Eq-sieve-eq1 : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) Θ@(Θt ,Σ Θp) : Con}{γt : I.Subt Δt Γt}{δ@(δt ,Σ δp) : Sub Θ Δ}{t t' : I.Tm Γt} -> 
            Θ ◁ Eq-sieve ⟦ Δt ⟧Cont ⟦ t I.[ γt ]t ⟧Tm ⟦ t' I.[ γt ]t ⟧Tm Θ (reflect-cont Δt δt)
            ≡
            Θ ◁ (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Δ (reflect-cont Γt γt) [ δ ]ˢ)
        reflect-Eq-sieve-eq1 {Γt} {Δ@(Δt ,Σ Δp)} {Θ@(Θt ,Σ Θp)} {γt} {δ@(δt ,Σ δp)} {t} {t'} = 
            cong (Θ ◁_) 
            (mkSieveEq 
            (Sh.Sieve.R (Eq-sieve ⟦ Δt ⟧Cont ⟦ t I.[ γt ]t ⟧Tm ⟦ t' I.[ γt ]t ⟧Tm Θ (reflect-cont Δt δt))) 
            (Sh.Sieve.R (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Δ (reflect-cont Γt γt) [ δ ]ˢ)) 
            {Sh.Sieve.restr (Eq-sieve ⟦ Δt ⟧Cont ⟦ t I.[ γt ]t ⟧Tm ⟦ t' I.[ γt ]t ⟧Tm Θ (reflect-cont Δt δt))} 
            {λ {J}{f}{K} x g → Sh.Sieve.restr (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm Δ (reflect-cont Γt γt) [ δ ]ˢ) {J}{f}{K} x g} 
            ((funext (λ Ξ@(Ξt ,Σ Ξp) → funext (λ f@(ft ,Σ fp) → 
            cong-bin (_≡_) 
                (reflect-Eq-sieve-Tm-eq1 {Γt}{Δ}{Θ}{Ξ}{γt}{δ}{f}{t})
                (reflect-Eq-sieve-Tm-eq1 {Γt}{Δ}{Θ}{Ξ}{γt}{δ}{f}{t'}) 
            )))))

        reflect-Eq-sieve-eq2 : ∀ {Γt : I.ConTm}{Δ@(Δt ,Σ Δp) : Con}{γt : I.Subt Δt Γt}{t t' : I.Tm Γt} ->
            Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm (Δt ,Σ Δp) (reflect-cont Γt γt)
            ≡
            (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm ((Δt ,Σ Δp) ▸t') (reflect-cont Γt (γt I.∘t I.pt)) [ id ,t' (t' I.[ γt ]t) ]ˢ)
        reflect-Eq-sieve-eq2 {Γt} {Δ@(Δt ,Σ Δp)} {γt} {t} {t'} = 
            (mkSieveEq 
            (Sh.Sieve.R (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm (Δt ,Σ Δp) (reflect-cont Γt γt))) 
            (Sh.Sieve.R (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm ((Δt ,Σ Δp) ▸t') (reflect-cont Γt (γt I.∘t I.pt)) [ id ,t' (t' I.[ γt ]t) ]ˢ)) 
            {(Sh.Sieve.restr (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm (Δt ,Σ Δp) (reflect-cont Γt γt)))}
            {λ {J}{f}{K} x g → Sh.Sieve.restr (Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm ((Δt ,Σ Δp) ▸t') (reflect-cont Γt (γt I.∘t I.pt)) [ id ,t' (t' I.[ γt ]t) ]ˢ) {J}{f}{K} x g}
            (funext (λ Ξ@(Ξt ,Σ Ξp) → funext (λ f@(ft ,Σ fp) → 
            cong-bin (_≡_) 
            (cong (Subt.α ⟦ t ⟧Tm Ξ) (trans (cong (λ z -> ⟦ Γt ⟧Cont ∶ (reflect-cont Γt z) ⟨ f ⟩) (trans (trans (sym (idr {γ = γt})) (cong (γt I.∘t_) (sym ▸tβ₁))) (sym (ass {γ = γt}{δ = I.pt})))) (trans ((cong (⟦ Γt ⟧Cont ∶_⟨ f ⟩) (⟨⟩-reflect-cont {γt = γt I.∘t I.pt}{δ = id ,t' (t' I.[ γt ]t)}))) (sym (⟦ Γt ⟧Cont ∶⟨∘⟩))))) 
            (cong (Subt.α ⟦ t' ⟧Tm Ξ) ((trans (cong (λ z -> ⟦ Γt ⟧Cont ∶ (reflect-cont Γt z) ⟨ f ⟩) (trans (trans (sym (idr {γ = γt})) (cong (γt I.∘t_) (sym ▸tβ₁))) (sym (ass {γ = γt}{δ = I.pt})))) (trans ((cong (⟦ Γt ⟧Cont ∶_⟨ f ⟩) (⟨⟩-reflect-cont {γt = γt I.∘t I.pt}{δ = id ,t' (t' I.[ γt ]t)}))) (sym (⟦ Γt ⟧Cont ∶⟨∘⟩))))))))))

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
        reflect {Γt}{Δt}{Δ}{γt} (∃' A) x = 
            ◁-∃ 
            (λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) d PfA → 
            let PfA' = reflect A (substp (I.Pf Θp) (sym [∘]F) PfA) in
            let PfA'' = substp (∣ ⟦ A ⟧For ∣ Θ) (trans (cong (_,Σ d) (trans (cong (reflect-cont Γt) (trans ass (cong (γt I.∘t_) ▸tβ₁))) ⟨⟩-reflect-cont)) (cong (λ z -> (⟦ Γt ⟧Cont ∶ reflect-cont Γt γt ⟨ z ⟩) ,Σ d) (sym (idr' {f = δ})))) PfA' in
            maximal (d ,∃ PfA''))
            x
        reflect {Γt}{Δt}{Δ}{γt} (Eq t t') x = 
            ◁-Eq {R' = Eq-sieve ⟦ Γt ⟧Cont ⟦ t ⟧Tm ⟦ t' ⟧Tm ((Δt ,Σ Δ) ▸t') (reflect-cont Γt (γt I.∘t I.pt))} x
            (λ {Θ@(Θt ,Σ Θp)} δ@(δt ,Σ δp) → 
            let e = (Pf.α ⟦ x ⟧Pf) (reflect-conp Δ δt δp) in 
            substp (λ z -> z) (reflect-Eq-sieve-eq1 {Γt}{Δt ,Σ Δ}{Θ}{γt}{δ}{t}{t'}) e)
            ((reflect-Eq-sieve-eq2 {Γt}{Δt ,Σ Δ}{γt}{t}{t'}))
        reflect (rel zero a ts) x = maximal x
        reflect {Γt}{Δt}{Δ}{γt} (rel (suc n) a (ts ,Σ t)) x = 
            maximal (substp (λ z → I.Pf Δ (rel (suc n) a z)) 
            (mk,= 
                (trans (sym (reflect-Tms {n}{Γt}{Δt}{Δ}{γt}{ts})) (cong (λ z -> reifyTms (recTms (Δt ,Σ Δ) (∣ ⟦ ts ⟧Tms ∣ (Δt ,Σ Δ) z))) (sym (⟦ Γt ⟧Cont ∶⟨id⟩)))) 
                (trans (sym (reflect-Tm {Γt}{Δt}{Δ}{γt}{t})) ((cong (∣ ⟦ t ⟧Tm ∣ (Δt ,Σ Δ)) (sym (⟦ Γt ⟧Cont ∶⟨id⟩)))))) 
                x)

    completeness : ∀{Γt}{Γ} -> (A : I.For Γt) -> B.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For -> I.Pf Γ A
    completeness {Γt}{Γ} A p = substp (I.Pf Γ) [id]F (reify {Γt}{Γt}{Γ} A (∣ p ∣ (reflect-conp Γ I.idt (substp (I.Subp Γ) (sym [id]C) I.idp))))
    
    soundness : ∀{Γt Γ} -> (A : I.For Γt) -> I.Pf Γ A -> B.Pf ⟦ Γ ⟧Conp ⟦ A ⟧For
    soundness A = ⟦_⟧Pf    
 