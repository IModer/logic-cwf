{-# OPTIONS --prop #-}

open import lib

module FirstOrderLogic.IntFullSplit.Iterator 
    (funar : ℕ → Set)
    (relar : ℕ → Set)
    where

open import FirstOrderLogic.IntFullSplit.Model funar relar
open import FirstOrderLogic.IntFullSplit.Syntax funar relar

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
        -- fun rel

        ⟦◆p⟧    : ∀{Γt} -> ⟦ M.◆p {Γt} ⟧Conp ≡ N.◆p
        ⟦▸p⟧    : ∀{Γt}{Γ : M.Conp Γt}{K : M.For Γt} -> ⟦ Γ M.▸p K ⟧Conp ≡ ⟦ Γ ⟧Conp N.▸p ⟦ K ⟧For
        ⟦[]C⟧   : ∀{Γt Δt}{Γ : M.Conp Γt}{γt : M.Subt Δt Γt} -> ⟦ Γ M.[ γt ]C ⟧Conp ≡ (⟦ Γ ⟧Conp N.[ ⟦ γt ⟧Subt ]C)
        
        ⟦⊥⟧     : ∀{Γt} -> ⟦ M.⊥ {Γt} ⟧For ≡ N.⊥
        ⟦⊤⟧     : ∀{Γt} -> ⟦ M.⊤ {Γt} ⟧For ≡ N.⊤
        ⟦⊃⟧     : ∀{Γt}{K L : M.For Γt} -> ⟦ K M.⊃ L ⟧For ≡ ⟦ K ⟧For N.⊃ ⟦ L ⟧For
        ⟦∧⟧     : ∀{Γt}{K L : M.For Γt} -> ⟦ K M.∧ L ⟧For ≡ ⟦ K ⟧For N.∧ ⟦ L ⟧For
        ⟦∨⟧     : ∀{Γt}{K L : M.For Γt} -> ⟦ K M.∨ L ⟧For ≡ ⟦ K ⟧For N.∨ ⟦ L ⟧For
        ⟦∀⟧     : ∀{Γt}{K : M.For (Γt M.▸t)} -> ⟦ M.∀' K ⟧For ≡ N.∀' (transport N.For ⟦▸t⟧ ⟦ K ⟧For) 
        ⟦∃⟧     : ∀{Γt}{K : M.For (Γt M.▸t)} -> ⟦ M.∃' K ⟧For ≡ N.∃' (transport N.For ⟦▸t⟧ ⟦ K ⟧For) 

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

    ⟦ ◆t ⟧Cont = M.◆t
    ⟦ Γt ▸t ⟧Cont = ⟦ Γt ⟧Cont M.▸t

    ⟦ εt ⟧Subt = M.εt -- M.εt
    ⟦ γ ,t t ⟧Subt = ⟦ γ ⟧Subt M.,t ⟦ t ⟧Tm    

    ⟦idt⟧ : ∀{Γt} -> ⟦ I.idt {Γt} ⟧Subt ≡ M.idt
    ⟦idt⟧ {Γt} = {!   !}

    ⟦ ⊥ ⟧For = M.⊥
    ⟦ ⊤ ⟧For = M.⊤
    ⟦ K ⊃ L ⟧For = ⟦ K ⟧For M.⊃ ⟦ L ⟧For
    ⟦ K ∧ L ⟧For = ⟦ K ⟧For M.∧ ⟦ L ⟧For
    ⟦ K ∨ L ⟧For = ⟦ K ⟧For M.∨ ⟦ L ⟧For
    ⟦ ∀' K ⟧For = M.∀' ⟦ K ⟧For
    ⟦ ∃' K ⟧For = M.∃' ⟦ K ⟧For
    ⟦ Eq t t' ⟧For = M.Eq ⟦ t ⟧Tm ⟦ t' ⟧Tm
    ⟦ rel n a ts ⟧For = M.rel n a ⟦ ts ⟧Tms

    ⟦ var V.vz ⟧Tm = M.qt
    ⟦ var (V.vs t) ⟧Tm = ⟦ var t ⟧Tm M.[ M.pt ]t
    ⟦ fun n a ts ⟧Tm = M.fun n a ⟦ ts ⟧Tms

    ⟦_⟧Tms {Γt} {zero} * = M.εs
    ⟦_⟧Tms {Γt} {suc n} (ts ,Σ t) = ⟦ ts ⟧Tms M.,s ⟦ t ⟧Tm

    ⟦ ◆p ⟧Conp = M.◆p
    ⟦ Γ ▸p K ⟧Conp = ⟦ Γ ⟧Conp M.▸p ⟦ K ⟧For

    ⟦ εp       ⟧Subp = M.εp
    ⟦ idp      ⟧Subp = M.idp
    ⟦ γ ∘p δ   ⟧Subp = ⟦ γ ⟧Subp M.∘p ⟦ δ ⟧Subp
    ⟦ pp       ⟧Subp = M.pp
    ⟦ γ ,p PfK ⟧Subp = ⟦ γ ⟧Subp M.,p ⟦ PfK ⟧Pf
    
    ⟦[]C⟧ : ∀{Γt Δt}{Γ : I.Conp Γt}{γt : I.Subt Δt Γt} -> ⟦ Γ I.[ γt ]C ⟧Conp ≡ (⟦ Γ ⟧Conp M.[ ⟦ γt ⟧Subt ]C)
    ⟦[]C⟧ {◆t}    {Δt} {Γ} {εt} = {!   !}
    ⟦[]C⟧ {Γt ▸t} {Δt} {Γ} {γt ,t t} = trans ({!   !}) {!   !}

    ⟦[]F⟧   : ∀{Γt Δt}{K : I.For Γt}{γt : I.Subt Δt Γt} -> ⟦ K I.[ γt ]F ⟧For ≡ ⟦ K ⟧For M.[ ⟦ γt ⟧Subt ]F
    ⟦[]F⟧ {Γt} {Δt} {K} {γt} = {!   !}     

    ⟦pt⟧ : ∀{Γt : I.Cont} -> ⟦ I.pt {Γt} ⟧Subt ≡ M.pt -- transport (λ z -> M.Subt z ⟦ Γt ⟧Cont) refl M.pt
    ⟦pt⟧ {◆t} = {!   !}
    ⟦pt⟧ {Γt ▸t} = {!   !}

    ⟦ exfalso PfK ⟧Pf = M.exfalso ⟦ PfK ⟧Pf
    ⟦ tt ⟧Pf = M.tt
    ⟦ ⊃intro PfK ⟧Pf = M.⊃intro ⟦ PfK ⟧Pf
    ⟦ PfKL $ PfK ⟧Pf = (M.⊃elim ⟦ PfKL ⟧Pf) M.[ M.idp M.,p ⟦ PfK ⟧Pf ]P
    ⟦ ∧intro PfK PfL ⟧Pf = M.∧intro ⟦ PfK ⟧Pf ⟦ PfL ⟧Pf
    ⟦ ∧elim₁ PfKL ⟧Pf = M.∧elim₁ ⟦ PfKL ⟧Pf
    ⟦ ∧elim₂ PfKL ⟧Pf = M.∧elim₂ ⟦ PfKL ⟧Pf
    ⟦ ∨elim PfKC PfLC PfKL ⟧Pf = M.∨elim ⟦ PfKC ⟧Pf ⟦ PfLC ⟧Pf ⟦ PfKL ⟧Pf
    ⟦ ∨intro₁ PfK ⟧Pf = M.∨intro₁ ⟦ PfK ⟧Pf
    ⟦ ∨intro₂ PfL ⟧Pf = M.∨intro₂ ⟦ PfL ⟧Pf
    ⟦ ∀intro {Γt}{K}{Γ} PfK ⟧Pf  =
        let PfK' = substp (λ z -> M.Pf z ⟦ K ⟧For) (trans (⟦[]C⟧ {Γt}{Γt ▸t}{Γ}{pt}) (cong (λ z → ⟦ Γ ⟧Conp M.[ z ]C) (⟦pt⟧ {Γt}))) ⟦ PfK ⟧Pf in 
        M.∀intro PfK'
    ⟦ un∀ PfK t ⟧Pf = {!    !}
    ⟦ ∃intro {Γt}{K}{Γ} t PfK ⟧Pf = M.∃intro ⟦ t ⟧Tm (substp (M.Pf ⟦ Γ ⟧Conp) (trans (⟦[]F⟧ {Γt ▸t} {Γt} {K} {idt ,t t}) (cong (λ z → ⟦ K ⟧For M.[ z M.,t ⟦ t ⟧Tm ]F) (⟦idt⟧ {Γt}))) ⟦ PfK ⟧Pf)
    ⟦ ∃elim PfK PfKL ⟧Pf = M.∃elim ⟦ PfK ⟧Pf {!   !}
    ⟦ ref ⟧Pf = M.Eqrefl
    ⟦ subst' {Γt} K {t}{t'}{Γ} PfK PfL ⟧Pf = 
        substp (M.Pf ⟦ Γ ⟧Conp) (sym (trans (⟦[]F⟧ {Γt ▸t} {Γt} {K} {idt ,t t'}) (cong (λ z → ⟦ K ⟧For M.[ z M.,t ⟦ t' ⟧Tm ]F) (⟦idt⟧ {Γt})))) 
        (M.subst' {⟦ Γt ⟧Cont} ⟦ K ⟧For {⟦ t ⟧Tm}{⟦ t' ⟧Tm}{⟦ Γ ⟧Conp} ⟦ PfK ⟧Pf 
        (substp (M.Pf ⟦ Γ ⟧Conp) (trans (⟦[]F⟧ {Γt ▸t} {Γt} {K} {idt ,t t}) ((cong (λ z → ⟦ K ⟧For M.[ z M.,t ⟦ t ⟧Tm ]F) (⟦idt⟧ {Γt})))) ⟦ PfL ⟧Pf))
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
      ; ⟦idt⟧ = {!   !}
      ; ⟦∘t⟧ = {!   !}
      ; ⟦εt⟧ = (sym transport-refl)
      ; ⟦[]F⟧ = {!   !}
      ; ⟦[]t⟧ = {!   !}
      ; ⟦,t⟧ = sym transport-refl
      ; ⟦pt⟧ = {!   !} -- trans {!   !} (sym transport-refl)
      ; ⟦qt⟧ = sym transport-refl
      ; ⟦[]ts⟧ = {!   !}
      ; ⟦εs⟧ = refl
      ; ⟦,s⟧ = refl
      ; ⟦π₁⟧ = {!   !}
      ; ⟦π₂⟧ = {!   !}
      ; ⟦◆p⟧ = refl
      ; ⟦▸p⟧ = refl
      ; ⟦[]C⟧ = {!   !}
      ; ⟦⊥⟧ = refl
      ; ⟦⊤⟧ = refl
      ; ⟦⊃⟧ = refl
      ; ⟦∧⟧ = refl
      ; ⟦∨⟧ = refl
      ; ⟦∀⟧ = cong M.∀' (sym transport-refl)
      ; ⟦∃⟧ = cong M.∃' (sym transport-refl)
      }
    
     