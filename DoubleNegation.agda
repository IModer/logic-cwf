{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

open import lib
open import FirstOrderClassical
open import FirstOrderIntuinistic

module DoubleNegation
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  --(Atom : Set)
  where

-- We give the translation as a function from the syntax of intuinistic logic to models of classical logic

-- Open the syntax of intuinistic logic


DNT : FirstOrderClassical.Model funar relar lzero lzero lzero lzero
DNT = record
  { Con = Con
  ; Sub = Sub
  ; _∘_ = _∘_
  ; id  = id
  ; ass = mk,sp= ass
  ; idl = mk,sp= idl
  ; idr = mk,sp= idr
  ; ◆  = ◆
  ; ε   = ε
  ; ◆η = ◆η
  -- Formulas now 
  ; For     = λ (Γt ,Σ Γp) → Σsp (For Γt) λ A → Pf (◆p ▸p (¬ (¬ A))) A
  ; _[_]F   = λ (K ,Σ Pk) (γt ,Σ γp) → (K [ γt ]F) ,Σ (Pk [ γt ]P)
  ; [∘]F    = mk,sp= [∘]F
  ; [id]F   = mk,sp= [id]F
  ; Pf      = λ (_ ,Σ Γp) (K ,Σ _) → Pf Γp K
  ; _[_]p   = λ Pk (γt ,Σ γp) → (Pk [ γt ]P) [ γp ]p
  ; _▸p_    = λ (Γt ,Σ Γp) (K ,Σ Pk) → (Γt ,Σ (Γp ▸p K))
  ; _,p_    = λ (Γt ,Σ Γp) Pk → Γt ,Σ (Γp ,p Pk)
  ; pp      = λ {Γ@(Γt ,Σ Γp)} {(K ,Σ Pk)} → proj₁ (id {Γ}) ,Σ substp (λ x → Subp (Γp ▸p K) x) (sym [id]C) (pp {Γt} {Γp} {K})
  ; qp      = λ {Γ@(Γt ,Σ Γp)} {(K ,Σ Pk)} → substp (λ x → Pf (Γp ▸p K) x) (sym [id]F) (qp {Γt} {Γp} {K})
  ; ▸pβ₁    = mk,sp= idl
  ; ▸pη     = mk,sp= idl
  -- We give the translation here basically, we also prove the lemma as we go
  ; ⊥       = ⊥ ,Σ (qp $ ⊃intro qp)
  ; ⊥[]     = refl
  ; exfalso = exfalso
  ; ⊤       = ⊤ ,Σ tt
  ; ⊤[]     = refl
  ; tt      = tt
  ; _⊃_     = 
    λ (A ,Σ Pa) (B ,Σ Pb) → (A ⊃ B) ,Σ 
    ⊃intro (((⊃intro Pb) [ proj₂ ε ]p) $ ⊃intro (db2 $ ⊃intro (db1 $ (db0 $ db2))))
  ; ⊃[]     = refl
  ; ⊃intro  = λ {Γ@(Γt ,Σ Γp)} {(K ,Σ Pk)} {(L ,Σ Pl)} x → substp (Pf Γp) (cong (K ⊃_) [id]F) (⊃intro x)
  ; ⊃elim   = λ {Γ@(Γt ,Σ Γp)} {(K ,Σ Pk)} {(L ,Σ Pl)} x → substp (Pf (Γp ▸p K)) (sym [id]F) (⊃elim x)
  ; _∧_     = 
    λ (A ,Σ Pa) (B ,Σ Pb) → (A ∧ B) ,Σ 
    ∧intro 
      (((⊃intro Pa) [ pp ]p) $ ⊃intro (db1 $ (⊃intro (db1 $ (∧elim₁ db0))))) 
      (((⊃intro Pb) [ pp ]p) $ ⊃intro (db1 $ (⊃intro (db1 $ (∧elim₂ db0)))))
  ; ∧[]     = refl
  ; ∧intro  = ∧intro
  ; ∧elim₁  = ∧elim₁
  ; ∧elim₂  = ∧elim₂
  ; _∨_     = λ (A ,Σ Pa) (B ,Σ Pb) → (¬ ¬ (A ∨ B)) ,Σ 
    join¬¬ db0
  ; ∨[]     = refl
  ; ∨elim   = λ {(Γt ,Σ Γp)} {(K ,Σ Pfk)} {(L ,Σ Pfl)} {(C ,Σ Pfc)} PfKC' PfLC' Pf¬¬K∨C → 
    let PfKC = substp (Pf (Γp ▸p K)) [id]F PfKC' in
    let PfLC = substp (Pf (Γp ▸p L)) [id]F PfLC' in
    ((⊃intro Pfc) [ proj₂ ε ]p) $ ⊃intro ((Pf¬¬K∨C [ pp ]p) $ (⊃intro (db1 $ (∨elim (PfKC [ pp⁺ (pp ∘p pp) ]p) (PfLC [ pp⁺ (pp ∘p pp) ]p) db0))))
  ; ∨intro₁ = λ x → ⊃intro (db0 $ ((∨intro₁ x) [ pp ]p))
  ; ∨intro₂ = λ x → ⊃intro (db0 $ ((∨intro₂ x) [ pp ]p))
  -- This is the same
  ; Tm    = λ (Γt ,Σ Γp) → Tm Γt
  ; _[_]t = λ t (γt ,Σ γp) → t [ γt ]t
  ; [∘]t  = λ {(Γt ,Σ Γp)} {t} → [∘]t {Γt} {t}
  ; [id]t = [id]t
  ; _▸t   = λ (Γt ,Σ Γp) → (Γt ▸t) ,Σ Γp [ pt ]C
  ; _,t_  = λ {Γ} {Δ} (γt ,Σ γp) t → (γt ,t t) ,Σ substp (λ x → Subp (proj₂ Δ) x) (sym (trans (sym [∘]C) (cong (λ x → (proj₂ Γ) [ x ]C) ▸tβ₁))) γp
  ; pt    = λ {(Γt ,Σ Γp)} → pt {Γt} ,Σ (idp {Γt ▸t} {Γp [ pt ]C })
  ; qt    = λ {(Γt ,Σ Γp)} → qt {Γt}
  ; ▸tβ₁  = mk,sp= ▸tβ₁
  ; ▸tβ₂  = refl
  ; ▸tη   = mk,sp= ▸tη
  -- We also negate fun and rel
  ; fun   = fun
  ; fun[] = λ {Γ} {_} {_} {_} {Δ} {γ} → funLemma {Γ} {Δ = Δ} {γ = γ}
  ; rel   = λ n x tms → (¬ ¬ rel n x tms) ,Σ 
    join¬¬ db0
  ; rel[] = λ {Γ} {_} {_} {_} {Δ} {γ} → mk,sp= (cong (λ x → ¬ (¬ x)) (relLemma {Γ} {Δ = Δ} {γ = γ}))
  -- 
  ; ∀' = λ {(Γt ,Σ Γp)} (K ,Σ Pk) → ∀' K ,Σ 
    -- there is a bug here where i cannot Cc-Cr db1
    ∀intro (((⊃intro Pk) [ pp ]p) $ ⊃intro ( (db1) $ ⊃intro (db1 $ ((∀elim db0) [ proj₂ ε ,p qp ]p))))
  ; ∀[] = refl
  ; ∀intro = ∀intro
  ; ∀elim = ∀elim
  ; ∃' = λ (K ,Σ Pk) → (¬ ¬ (∃' K)) ,Σ 
    join¬¬ db0
  ; ∃[] = refl
  ; ∃intro = λ {(Γt ,Σ Γp)} {(K ,Σ Pk)} t K[x:=t] → ⊃intro (db0 $ (∃intro t (K[x:=t] [ pp ]p)))
  ; ∃elim = λ {(Γt ,Σ Γp)} {(K ,Σ Pk)} {(L ,Σ Pl)} ¬¬∃K x → ((⊃intro Pl) [ proj₂ ε ]p) $ ⊃intro ((¬¬∃K [ pp ]p) $ ⊃intro (db1 $ (∃elim db0 (substp (λ z → Pf (Γp [ ⌜ V.wk V.id ⌝ ]C ▸p K) (L [ z ]F)) (▸tβ₁) x))))
  ; Eq = λ t t' → (¬ ¬ (Eq t t')) ,Σ 
    join¬¬ db0
  ; Eq[] = mk,sp= refl
  ; Eqrefl = ⊃intro (db0 $ ref)
  ; subst' = λ {Γ} (K ,Σ Pfk) {t}{t'} ¬¬Eq K[x:=t] → (⊃intro (Pfk [ idt ,t t' ]P) [ proj₂ ε ]p) $ ⊃intro ((¬¬Eq [ pp ]p) $ (⊃intro (db1 $ (subst' K db0 (K[x:=t] [ pp ∘p pp ]p))))) 
    -- un∀ (∀intro (((⊃intro Pfk) [ proj₂ ε ]p) $ ⊃intro (db0 $ {!   !}))) t' -- exfalso (¬¬Eq $ ⊃intro {! subst' K db0 (K[x:=t] [ pp ]p)  !} )
    --exfalso (¬¬Eq $ ⊃intro (((subst' (¬ (¬ K)) db0 (⊃intro (db0 $ (K[x:=t] [ pp ∘p pp ]p))))) $ ⊃intro ({!   !})))
    -- un∀ (∀intro ((⊃intro Pfk [ proj₂ ε ]p) $ ⊃intro (?))) t'
  -- Finally we prove lem
  ; dni = λ {(Γt ,Σ Γp)} {(X ,Σ Px)} → (⊃intro Px) [ proj₂ ε ]p
  }
  where
    module Syntax = FirstOrderIntuinistic.I funar relar
    open Syntax 
    {-
    renaming 
      ( pt to ptᵢ; qt to qtᵢ; pp to ppᵢ; qp to qpᵢ; ⊥ to ⊥ᵢ; ⊤ to ⊤ᵢ; _∧_ to _∧ᵢ_; _∨_ to _∨ᵢ_; _$_ to _$ᵢ_;
      ⊃intro to ⊃introᵢ;⊃elim to ⊃elimᵢ;∧intro to ∧introᵢ; ∧elim₁ to ∧elim₁ᵢ; ∧elim₂ to ∧elim₂ᵢ; 
      ∨intro₁ to ∨intro₁ᵢ;∨intro₂ to ∨intro₂ᵢ;∨elim to ∨elimᵢ; exfalso to exfalsoᵢ; tt to ttᵢ)
    -}