{-# OPTIONS --prop --allow-unsolved-metas #-}

open import lib
open import FirstOrderIntuinistic

-- Tarski Model or Tarski semantics, everything is interpreted via the "standard" interpretation
-- Whatever that means, thats why its also called StandardModel
module FI-TarskiModel
  (funar : ℕ → Set)
  (relar : ℕ → Set)  
  (D : Set)
  (rel : (n : ℕ) → relar n → D ^ n → Prop)
  (fun : (n : ℕ) → funar n → D ^ n → D) where

  StandardModel : Model funar relar _ _ _ _ _
  StandardModel = record
    -- this should be Sigma, so Σp Set Prop, the second component models the Pf Contexts
    { Con = Set 
    ; Sub = λ Γ Δ → Γ → Δ
    ; _∘_ = λ γ δ θ → γ (δ θ)
    ; id = λ γ → γ
    ; ass = refl
    ; idl = refl
    ; idr = refl
    ; ◆ = 𝟙 -- 𝟙
    ; ε = λ _ → *
    ; ◆η = λ _ → refl
    ; For = λ Γ → Γ → Prop
    ; _[_]F = λ K γ δ → K (γ δ)
    ; [∘]F = refl
    ; [id]F = refl
    ; Pf = λ Γ A → (γ : Γ) → A γ
    ; _[_]p = λ Γ δ γ → Γ (δ γ)
    ; _▸p_ = λ Γ A → Σsp Γ A
    ; _,p_ = λ γ X δ → (γ δ) ,Σ X δ
    ; pp = proj₁
    ; qp = proj₂
    ; ▸pβ₁ = refl
    ; ▸pη = refl
    ; ⊥ = λ _ → 𝟘p
    ; ⊥[] = refl
    ; exfalso = λ x γ → ind𝟘p (x γ)
    ; ⊤ = λ _ → 𝟙p
    ; ⊤[] = refl
    ; tt = λ γ → *
    ; _⊃_ = λ A B γ → A γ → B γ
    ; ⊃[] = refl
    ; ⊃intro = λ kl γ k → kl (γ ,Σ k)
    ; ⊃elim = λ kl (γ ,Σ k ) → kl γ k
    ; _∧_ = λ A B γ → (A γ) ×p (B γ)
    ; ∧[] = refl
    ; ∧intro = λ k l  γ → k γ ,Σ l γ
    ; ∧elim₁ = λ kl γ → proj₁ (kl γ)
    ; ∧elim₂ = λ kl γ → proj₂ (kl γ)
    ; _∨_ = λ A B γ → (A γ) +p (B γ)
    ; ∨[] = refl
    ; ∨elim = λ {Γ}{K}{L}{C} f g kl γ → ind+p (λ _ → C γ) (λ x → f (γ ,Σ x)) (λ x → g (γ ,Σ x)) (kl γ)
    ; ∨intro₁ = λ k γ → inj₁ (k γ)
    ; ∨intro₂ = λ l γ → inj₂ (l γ)
    ; Tm = λ Γ → Γ → D
    ; _[_]t = λ d γ δ → d (γ δ)
    ; [∘]t = refl
    ; [id]t = refl
    ; _▸t = λ Γ → Γ × D
    ; _,t_ = λ γ d δ → (γ δ) ,Σ d δ
    ; pt = proj₁
    ; qt = proj₂
    ; ▸tβ₁ = refl
    ; ▸tβ₂ = refl
    ; ▸tη = refl
    ; Tms = λ Γ n → Γ → D ^ n
    ; _[_]ts = λ ts γ δ* → ts (γ δ*)
    ; [∘]ts = refl
    ; [id]ts = refl
    ; εs = λ _ → *
    ; ◆sη = λ _ → refl
    ; _,s_ = λ ts t γ* → t γ* ,Σ (ts γ*)
    ; π₁ = λ ts γ* → proj₂ (ts γ*)
    ; π₂ = λ ts γ* → proj₁ (ts γ*)
    ; ▸sβ₁ = refl
    ; ▸sβ₂ = refl
    ; ▸sη = refl
    ; ,[] = refl
    ; fun = λ n x ts γ → fun n x (ts γ)
    ; fun[] = refl
    ; rel = λ n x ts γ → rel n x (ts γ)
    ; rel[] = refl
    ; ∀' = λ X γ → (d : D) → X (γ ,Σ d)
    ; ∀[] = refl
    ; ∀intro = λ x γ d → x (γ ,Σ d)
    ; ∀elim = λ x (γ ,Σ d) → x γ d
    ; ∃' = λ X γ → ∃ D λ d → X (γ ,Σ d)
    ; ∃[] = refl
    ; ∃intro = λ γd x γ → (γd γ) ,∃ (x γ)
    ; ∃elim = λ x y γ → with∃ (x γ) (λ d Kγd → y ((γ ,Σ d) ,Σ Kγd))
    ; Eq = λ f g x → f x ≡ g x
    ; Eq[] = refl
    ; Eqrefl = λ γ → refl
    ; subst' = λ K eq K' γ → substp (λ z → K (γ ,Σ z)) (eq γ) (K' γ)
    }
    where
{-
-}
      funHelp' : 
        {Γ : Set} →
        {n : ℕ}  →
        {a : funar n}  →
        {ts : (Γ → D) ^ n}  →
        {Δ : Set}  →
        {γ : Δ → Γ}  →
        (x : Δ) →  
        ind^' {lzero} {n} {Γ → D} {λ n → D ^ n} * (λ d ds → d (γ x) ,Σ ds) ts ≡
        ind^' {lzero} {n} {Δ → D} {λ n → D ^ n} * (λ d ds → d x ,Σ ds) 
          (ind^ {lzero} {n} {Γ → D} {λ n → (Δ → D) ^ n} (λ _ → *) (λ _ t ts₁ → (λ δ → t (γ δ)) ,Σ ts₁) ts)
      funHelp' {Γ} {zero} {a} {ts} {Δ} {γ} x = refl
      funHelp' {Γ} {suc n} {a} {ts} {Δ} {γ} x = mk,= refl {!   !}

      funHelp : 
        {Γ : Set} →
        {n : ℕ}  →
        {a : funar n}  →
        {ts : (Γ → D) ^ n}  →
        {Δ : Set}  →
        {γ : Δ → Γ}  →
        (x : Δ) → 
        (fun n a (ind^' {lzero} {n} {Γ → D} {λ n → D ^ n} * (λ d ds → d (γ x) ,Σ ds) ts)) 
        ≡ 
        (fun n a (ind^' {lzero} {n} {Δ → D} {λ n → D ^ n} * (λ d ds → d x ,Σ ds) 
        (ind^ {lzero} {n} {Γ → D} {λ n → (Δ → D) ^ n} (λ _ → *) (λ _ t ts₁ → (λ δ → t (γ δ)) ,Σ ts₁) ts)))
      funHelp {Γ} {n} {a} {ts} {Δ} {γ} x = cong (fun n a) {!   !}
