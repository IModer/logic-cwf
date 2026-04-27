open import lib

module FirstOrderLogic.IntNegative.Iterator 
    (funar : ℕ → Set)
    (relar : ℕ → Set)
    where

open import FirstOrderLogic.IntNegative.Model funar relar
open import FirstOrderLogic.IntNegative.Syntax funar relar

record Morphism{i j k l m i' j' k' l' m' : Level}(A : Model i j k l m)(B : Model i' j' k' l' m') : Set (i ⊔ j ⊔ k ⊔ l ⊔ m ⊔ i' ⊔ j' ⊔ k' ⊔ l' ⊔ m') where
    private module M = Model A
    private module N = Model B
    field
        ⟦_⟧Cont : M.Cont -> N.Cont
        ⟦_⟧Subt : ∀{Δt Γt : M.Cont} -> M.Subt Δt Γt -> N.Subt ⟦ Δt ⟧Cont ⟦ Γt ⟧Cont
        ⟦_⟧For  : ∀{Γt : M.Cont} -> M.For Γt -> N.For ⟦ Γt ⟧Cont
        ⟦_⟧Tm   : ∀{Γt : M.Cont} -> M.Tm Γt -> N.Tm ⟦ Γt ⟧Cont
        ⟦_⟧Tms  : ∀{Γt : M.Cont}{n : ℕ} -> M.Tms Γt n -> N.Tms ⟦ Γt ⟧Cont n
        ⟦_⟧Conp : ∀{Γt : M.Cont} -> M.Conp Γt -> N.Conp ⟦ Γt ⟧Cont
        ⟦_⟧Subp : ∀{Γt : M.Cont}{Δ Γ : M.Conp Γt} -> M.Subp Δ Γ -> N.Subp ⟦ Δ ⟧Conp ⟦ Γ ⟧Conp
        ⟦_⟧Pf   : ∀{Γt : M.Cont}{Γ : M.Conp Γt}{K : M.For Γt} -> M.Pf Γ K -> N.Pf ⟦ Γ ⟧Conp ⟦ K ⟧For
        
        ⟦◆t⟧    : ⟦ M.◆t ⟧Cont ≡ N.◆t
        ⟦▸t⟧    : ∀{Γt} -> ⟦ Γt M.▸t ⟧Cont ≡ ⟦ Γt ⟧Cont N.▸t
        ⟦idt⟧   : ∀{Γt} -> ⟦ M.idt {Γt} ⟧Subt ≡ N.idt {⟦ Γt ⟧Cont}
        ⟦∘t⟧    : ∀{Γt Δt Θt}{γt : M.Subt Δt Γt}{δt : M.Subt Θt Δt} -> ⟦ γt M.∘t δt ⟧Subt ≡ ⟦ γt ⟧Subt N.∘t ⟦ δt ⟧Subt
        ⟦εt⟧    : ∀{Γt} -> ⟦ M.εt ⟧Subt ≡ transport (N.Subt ⟦ Γt ⟧Cont) (sym ⟦◆t⟧) (N.εt {⟦ Γt ⟧Cont})
        
        ⟦[]F⟧   : ∀{Γt Δt}{K : M.For Γt}{γt : M.Subt Δt Γt} -> ⟦ K M.[ γt ]F ⟧For ≡ ⟦ K ⟧For N.[ ⟦ γt ⟧Subt ]F
        ⟦[]t⟧   : ∀{Γt Δt}{t : M.Tm Γt}{γt : M.Subt Δt Γt} -> ⟦ t M.[ γt ]t ⟧Tm ≡ ⟦ t ⟧Tm N.[ ⟦ γt ⟧Subt ]t
        ⟦,t⟧    : ∀{Γt Δt}{t : M.Tm Γt}{γt : M.Subt Γt Δt} -> ⟦ γt M.,t t ⟧Subt ≡ transport (N.Subt ⟦ Γt ⟧Cont) (sym ⟦▸t⟧) (⟦ γt ⟧Subt N.,t ⟦ t ⟧Tm)
        ⟦pt⟧    : ∀{Γt : M.Cont} -> ⟦ M.pt {Γt} ⟧Subt ≡ transport (λ z -> N.Subt z ⟦ Γt ⟧Cont) (sym ⟦▸t⟧) N.pt
        ⟦qt⟧    : ∀{Γt : M.Cont} -> ⟦ M.qt {Γt} ⟧Tm ≡ transport N.Tm (sym ⟦▸t⟧) (N.qt {⟦ Γt ⟧Cont})
        
        ⟦[]ts⟧  : ∀{Γt Δt n}{ts : M.Tms Γt n}{γt : M.Subt Δt Γt} -> ⟦ ts M.[ γt ]ts ⟧Tms ≡ ⟦ ts ⟧Tms N.[ ⟦ γt ⟧Subt ]ts
        ⟦εs⟧    : ∀{Γt} -> ⟦ M.εs {Γt} ⟧Tms ≡ N.εs
        ⟦,s⟧    : ∀{Γt n}{ts : M.Tms Γt n}{t : M.Tm Γt} -> ⟦ ts M.,s t ⟧Tms ≡ (⟦ ts ⟧Tms N.,s ⟦ t ⟧Tm) 
        ⟦π₁⟧    : ∀{Γt n}{ts : M.Tms Γt (suc n)} -> ⟦ M.π₁ ts ⟧Tms ≡ N.π₁ ⟦ ts ⟧Tms
        ⟦π₂⟧    : ∀{Γt n}{ts : M.Tms Γt (suc n)} -> ⟦ M.π₂ ts ⟧Tm  ≡ N.π₂ ⟦ ts ⟧Tms

        ⟦fun⟧ : ∀{Γt n a}{ts : M.Tms Γt n} -> ⟦ M.fun n a ts ⟧Tm  ≡ N.fun n a ⟦ ts ⟧Tms
        ⟦rel⟧ : ∀{Γt n a}{ts : M.Tms Γt n} -> ⟦ M.rel n a ts ⟧For ≡ N.rel n a ⟦ ts ⟧Tms

        ⟦◆p⟧    : ∀{Γt} -> ⟦ M.◆p {Γt} ⟧Conp ≡ N.◆p
        ⟦▸p⟧    : ∀{Γt}{Γ : M.Conp Γt}{K : M.For Γt} -> ⟦ Γ M.▸p K ⟧Conp ≡ ⟦ Γ ⟧Conp N.▸p ⟦ K ⟧For
        ⟦[]C⟧   : ∀{Γt Δt}{Γ : M.Conp Γt}{γt : M.Subt Δt Γt} -> ⟦ Γ M.[ γt ]C ⟧Conp ≡ (⟦ Γ ⟧Conp N.[ ⟦ γt ⟧Subt ]C)
        
        ⟦⊤⟧     : ∀{Γt} -> ⟦ M.⊤ {Γt} ⟧For ≡ N.⊤
        ⟦⊃⟧     : ∀{Γt}{K L : M.For Γt} -> ⟦ K M.⊃ L ⟧For ≡ ⟦ K ⟧For N.⊃ ⟦ L ⟧For
        ⟦∧⟧     : ∀{Γt}{K L : M.For Γt} -> ⟦ K M.∧ L ⟧For ≡ ⟦ K ⟧For N.∧ ⟦ L ⟧For
        ⟦∀⟧     : ∀{Γt}{K : M.For (Γt M.▸t)} -> ⟦ M.∀' K ⟧For ≡ N.∀' (transport N.For ⟦▸t⟧ ⟦ K ⟧For) 
        
module Ite
    {i j k l m : Level}
    (M : Model i j k l m)
    where
    
    private module M = Model M
    private module I = Model I

    ⟦_⟧Cont : I.Cont -> M.Cont
    ⟦_⟧Subt : ∀{Γt Δt} -> I.Subt Δt Γt -> M.Subt ⟦ Δt ⟧Cont ⟦ Γt ⟧Cont
    ⟦_⟧For  : ∀{Γt} -> I.For Γt -> M.For ⟦ Γt ⟧Cont
    ⟦_⟧Tm   : ∀{Γt} -> I.Tm Γt -> M.Tm ⟦ Γt ⟧Cont
    ⟦_⟧Tms  : ∀{Γt n} -> I.Tms Γt n -> M.Tms ⟦ Γt ⟧Cont n
    ⟦_⟧Conp : ∀{Γt} -> I.Conp Γt -> M.Conp ⟦ Γt ⟧Cont
    ⟦_⟧Subp : ∀{Γt}{Δ Γ : I.Conp Γt} -> I.Subp Δ Γ -> M.Subp ⟦ Δ ⟧Conp ⟦ Γ ⟧Conp
    ⟦_⟧Pf   : ∀{Γt}{Γ : I.Conp Γt}{K : I.For Γt} -> I.Pf Γ K -> M.Pf ⟦ Γ ⟧Conp ⟦ K ⟧For
    ⟦_⟧Var  : ∀{Γt} -> V.Tm Γt -> M.Tm ⟦ Γt ⟧Cont

    ⟦ ◆t ⟧Cont = M.◆t
    ⟦ Γt ▸t ⟧Cont = ⟦ Γt ⟧Cont M.▸t

    ⟦ εt  ⟧Subt = M.εt
    ⟦ _,t_ {Δt} γ t ⟧Subt = ⟦ γ ⟧Subt M.,t ⟦ t ⟧Tm

    ⟦ V.vz ⟧Var = M.qt
    ⟦ V.vs t ⟧Var = ⟦ t ⟧Var M.[ M.pt ]t

    ⟦ var t ⟧Tm = ⟦ t ⟧Var
    ⟦ fun n a ts ⟧Tm = M.fun n a ⟦ ts ⟧Tms

    ⟦_⟧Tms {Γt} {zero} * = M.εs
    ⟦_⟧Tms {Γt} {suc n} (ts ,Σ t) = ⟦ ts ⟧Tms M.,s ⟦ t ⟧Tm
    
    ⟦[]v⟧ : ∀{Γt Δt}{t : V.Tm Γt}{γ : Subt Δt Γt} -> ⟦ t [ γ ]v ⟧Tm ≡ ⟦ t ⟧Var M.[ ⟦ γ ⟧Subt ]t
    ⟦[]v⟧ {Γt} {Δt} {V.vz}   {γ ,t t} = sym M.▸tβ₂
    ⟦[]v⟧ {Γt ▸t} {Δt} {V.vs x} {γ ,t t} = trans (⟦[]v⟧ {t = x}) (trans (cong (λ z → ⟦ x ⟧Var M.[ z ]t) (sym M.▸tβ₁)) M.[∘]t)

    ⟦[]t⟧ : ∀{Γt Δt}{t : Tm Γt}{γt : Subt Δt Γt} -> ⟦ t [ γt ]t ⟧Tm ≡ ⟦ t ⟧Tm M.[ ⟦ γt ⟧Subt ]t
    ⟦[]ts⟧ : ∀{Γt Δt n}{ts : Tms Γt n}{γt : Subt Δt Γt} -> ⟦ ts [ γt ]ts ⟧Tms ≡ ⟦ ts ⟧Tms M.[ ⟦ γt ⟧Subt ]ts
    
    ⟦[]t⟧ {Γt} {Δt} {var x} {γt} = ⟦[]v⟧ {t = x}
    ⟦[]t⟧ {Γt} {Δt} {fun n a ts} {γt} = trans (cong (M.fun n a) ⟦[]ts⟧) (sym M.fun[]) 
    ⟦[]ts⟧ {Γt} {Δt} {zero} {ts} {γt} = sym (M.◆sη (M.εs M.[ ⟦ γt ⟧Subt ]ts))
    ⟦[]ts⟧ {Γt} {Δt} {suc n} {ts ,Σ t} {γt} = trans (cong (λ z → proj₁ z M.,s proj₂ z) (mk,= ⟦[]ts⟧ (⟦[]t⟧ {t = t}))) (sym M.,[])

    ⟦π₁⟧ : ∀{Γt n}{ts : Tms Γt (suc n)} -> ⟦ π₁ ts ⟧Tms ≡ M.π₁ ⟦ ts ⟧Tms
    ⟦π₁⟧ = (sym M.▸sβ₁)

    ⟦π₂⟧ : ∀{Γt n}{ts : Tms Γt (suc n)} -> ⟦ π₂ ts ⟧Tm  ≡ M.π₂ ⟦ ts ⟧Tms
    ⟦π₂⟧ = sym M.▸sβ₂    

    ⟦∘t⟧ : ∀{Γt Δt Θt}{γt : Subt Δt Γt}{δt : Subt Θt Δt} -> ⟦ γt ∘t δt ⟧Subt ≡ ⟦ γt ⟧Subt M.∘t ⟦ δt ⟧Subt
    ⟦∘t⟧ {◆t} {Δt} {Θt} {εt} {δt} = sym (M.◆tη (M.εt M.∘t ⟦ δt ⟧Subt)) -- sym (M.◆tη (⟦ εt ⟧Subt M.∘t ⟦ δt ⟧Subt))
    ⟦∘t⟧ {Γt ▸t} {Δt} {Θt} {γt ,t t} {δt} = 
        trans (cong (λ z -> proj₁ z M.,t proj₂ z) 
        (mk,= (⟦∘t⟧ {γt = γt}{δt = δt}) (⟦[]t⟧ {t = t}))) 
        (sym M.,t∘t)

    ⟦_⟧Subv : ∀{Δ Γ} -> V.Sub Δ Γ -> M.Subt ⟦ Δ ⟧Cont ⟦ Γ ⟧Cont
    ⟦ V.εt ⟧Subv = M.εt
    ⟦ γ V.,t t ⟧Subv = ⟦ γ ⟧Subv M.,t ⟦ var t ⟧Tm

    ⟦wk⟧ : ∀{Γ Δ}{γv : V.Sub Δ Γ} -> ⟦ ⌜ V.wk γv ⌝ ⟧Subt ≡ ⟦ ⌜ γv ⌝ ⟧Subt M.∘t M.pt
    ⟦wk⟧ {◆t} {Δ} {V.εt} = sym (M.◆tη (M.εt M.∘t M.pt))
    ⟦wk⟧ {Γ ▸t} {Δ} {γv V.,t x} = trans (cong (λ z → z M.,t (⟦ x ⟧Var M.[ M.pt ]t)) (⟦wk⟧ {γv = γv})) (sym (M.,t∘t {γt = ⟦ ⌜ γv ⌝ ⟧Subt}{t = ⟦ x ⟧Var}))

    ⟦idt⟧ : ∀{Γt} -> ⟦ I.idt {Γt} ⟧Subt ≡ M.idt
    ⟦idt⟧ {◆t}    = sym (M.◆tη M.idt)
    ⟦idt⟧ {Γt ▸t} = trans (cong (M._,t M.qt) (trans (⟦wk⟧ {Γt}{Γt}{V.id}) (trans (cong (M._∘t M.pt) (⟦idt⟧ {Γt})) M.idlt))) M.▸tη'
    
    ⟦pt⟧ : ∀{Γt} -> ⟦ pt {Γt} ⟧Subt ≡ M.pt
    ⟦pt⟧ {Γt} = trans (⟦wk⟧ {Γt}{Γt}{V.id}) (trans (cong (M._∘t M.pt) (⟦idt⟧ {Γt})) M.idlt)

    ⟦ ⊤ ⟧For = M.⊤
    ⟦ K ⊃ L ⟧For = ⟦ K ⟧For M.⊃ ⟦ L ⟧For
    ⟦ K ∧ L ⟧For = ⟦ K ⟧For M.∧ ⟦ L ⟧For
    ⟦ ∀' K ⟧For = M.∀' ⟦ K ⟧For
    ⟦ rel n a ts ⟧For = M.rel n a ⟦ ts ⟧Tms

    ⟦[]F⟧   : ∀{Γt Δt}{K : I.For Γt}{γt : I.Subt Δt Γt} -> ⟦ K I.[ γt ]F ⟧For ≡ ⟦ K ⟧For M.[ ⟦ γt ⟧Subt ]F
    ⟦[]F⟧ {Γt} {Δt} {⊤} {γt} = sym M.⊤[]
    ⟦[]F⟧ {Γt} {Δt} {K ⊃ L} {γt} = trans (cong (λ z → proj₁ z M.⊃ proj₂ z) (mk,= (⟦[]F⟧ {K = K}) (⟦[]F⟧ {K = L}))) (sym M.⊃[])
    ⟦[]F⟧ {Γt} {Δt} {K ∧ L} {γt} = trans (cong (λ z → proj₁ z M.∧ proj₂ z) (mk,= (⟦[]F⟧ {K = K}) (⟦[]F⟧ {K = L}))) (sym M.∧[])
    ⟦[]F⟧ {Γt} {Δt} {∀' K} {γt} = trans (cong M.∀' (⟦[]F⟧ {K = K})) (trans (cong (λ z → M.∀' (⟦ K ⟧For M.[ z M.,t M.qt ]F)) (trans (⟦∘t⟧ {γt = γt}{δt = pt}) (cong (⟦ γt ⟧Subt M.∘t_) (⟦pt⟧ {Δt})))) (sym (M.∀[] {K = ⟦ K ⟧For} {γt = ⟦ γt ⟧Subt})))
    ⟦[]F⟧ {Γt} {Δt} {rel n x ts} {γt} = trans (cong (M.rel n x) (⟦[]ts⟧ {ts = ts})) (sym M.rel[])     

    ⟦ ◆p ⟧Conp = M.◆p
    ⟦ Γ ▸p K ⟧Conp = ⟦ Γ ⟧Conp M.▸p ⟦ K ⟧For

    ⟦[]C⟧ : ∀{Γt Δt}{Γ : I.Conp Γt}{γt : I.Subt Δt Γt} -> ⟦ Γ I.[ γt ]C ⟧Conp ≡ (⟦ Γ ⟧Conp M.[ ⟦ γt ⟧Subt ]C)
    ⟦[]C⟧ {Γt} {Δt} {◆p} {γt} = sym M.◆p[]
    ⟦[]C⟧ {Γt} {Δt} {Γ ▸p K} {γt} = trans (cong (λ z → proj₁ z M.▸p proj₂ z) (mk,= (⟦[]C⟧ {Γ = Γ}) (⟦[]F⟧ {K = K}))) (sym M.▸p[])
    
    ⟦ εp       ⟧Subp = M.εp
    ⟦ γ ,p PfK ⟧Subp = ⟦ γ ⟧Subp M.,p ⟦ PfK ⟧Pf
    ⟦ idp      ⟧Subp = M.idp
    ⟦ γ ∘p δ   ⟧Subp = ⟦ γ ⟧Subp M.∘p ⟦ δ ⟧Subp
    ⟦ pp       ⟧Subp = M.pp

    ⟦ tt ⟧Pf = M.tt
    ⟦ ⊃intro PfK ⟧Pf = M.⊃intro ⟦ PfK ⟧Pf
    ⟦ PfKL $ PfK ⟧Pf = (M.⊃elim ⟦ PfKL ⟧Pf) M.[ M.idp M.,p ⟦ PfK ⟧Pf ]P
    ⟦ ∧intro PfK PfL ⟧Pf = M.∧intro ⟦ PfK ⟧Pf ⟦ PfL ⟧Pf
    ⟦ ∧elim₁ PfKL ⟧Pf = M.∧elim₁ ⟦ PfKL ⟧Pf
    ⟦ ∧elim₂ PfKL ⟧Pf = M.∧elim₂ ⟦ PfKL ⟧Pf
    ⟦ ∀intro {Γt}{K}{Γ} PfK ⟧Pf  =
        let PfK' = substp (λ z -> M.Pf z ⟦ K ⟧For) (trans (⟦[]C⟧ {Γt}{Γt ▸t}{Γ}{pt}) (cong (λ z → ⟦ Γ ⟧Conp M.[ z ]C) (⟦pt⟧ {Γt}))) ⟦ PfK ⟧Pf in 
        M.∀intro PfK'
    ⟦ ∀elim {Γt}{K}{Γ} PfK ⟧Pf = substp (λ z -> M.Pf z ⟦ K ⟧For) (sym (trans (⟦[]C⟧ {Γ = Γ} {γt = pt}) (cong (⟦ Γ ⟧Conp M.[_]C) (⟦pt⟧ {Γt})))) (M.∀elim ⟦ PfK ⟧Pf)
    ⟦ _[_]p {Γt}{K}{Γp} PfK {Δt} γt ⟧Pf  = substp (λ z -> M.Pf (proj₁ z) (proj₂ z)) (mk,= (sym (⟦[]C⟧ {Γt}{Δt}{Γp}{γt})) (sym (⟦[]F⟧ {Γt}{Δt}{K}{γt}))) (⟦ PfK ⟧Pf M.[ ⟦ γt ⟧Subt ]p)
    ⟦ PfK [ γ ]P ⟧Pf = ⟦ PfK ⟧Pf M.[ ⟦ γ ⟧Subp ]P
    ⟦ qp ⟧Pf = M.qp

    Ite : Morphism I M
    Ite = record
        { ⟦_⟧Cont = ⟦_⟧Cont
        ; ⟦_⟧Subt = ⟦_⟧Subt
        ; ⟦_⟧For = ⟦_⟧For
        ; ⟦_⟧Tm = ⟦_⟧Tm
        ; ⟦_⟧Tms = ⟦_⟧Tms
        ; ⟦_⟧Conp = ⟦_⟧Conp
        ; ⟦_⟧Subp = ⟦_⟧Subp
        ; ⟦_⟧Pf = ⟦_⟧Pf
        ; ⟦◆t⟧ = refl
        ; ⟦▸t⟧ = refl
        ; ⟦idt⟧ = λ {Γt} -> ⟦idt⟧ {Γt}
        ; ⟦∘t⟧ = λ {Γt}{Δt}{Θt}{γt}{δt} -> ⟦∘t⟧ {Γt}{Δt}{Θt}{γt}{δt}
        ; ⟦εt⟧ = sym transport-refl
        ; ⟦[]F⟧ = λ {Γt}{Δt}{K}{γt} -> ⟦[]F⟧ {Γt}{Δt}{K}{γt}
        ; ⟦[]t⟧ = λ {Γt}{Δt}{t}{γt} -> ⟦[]t⟧ {Γt}{Δt}{t}{γt}
        ; ⟦,t⟧ = sym transport-refl 
        ; ⟦pt⟧ = λ {Γt} -> trans (⟦pt⟧ {Γt}) (sym transport-refl)
        ; ⟦qt⟧ = sym transport-refl
        ; ⟦[]ts⟧ = λ {Γt}{Δt}{n}{γt} -> ⟦[]ts⟧ {Γt}{Δt}{n}{γt}
        ; ⟦εs⟧ = refl
        ; ⟦,s⟧ = refl
        ; ⟦π₁⟧ = λ {Γt}{n}{ts} -> ⟦π₁⟧ {Γt}{n}{ts}
        ; ⟦π₂⟧ = λ {Γt}{n}{ts} -> ⟦π₂⟧ {Γt}{n}{ts}
        ; ⟦fun⟧ = refl
        ; ⟦rel⟧ = refl
        ; ⟦◆p⟧ = refl
        ; ⟦▸p⟧ = refl
        ; ⟦[]C⟧ = λ {Γt}{Δt}{Γ}{γt} -> ⟦[]C⟧ {Γt}{Δt}{Γ}{γt}
        ; ⟦⊤⟧ = refl
        ; ⟦⊃⟧ = refl
        ; ⟦∧⟧ = refl
        ; ⟦∀⟧ = cong M.∀' (sym transport-refl)
        }
    
      