{-# OPTIONS --prop #-}

open import lib
open import FirstOrderLogic.IntFull.Model

module FirstOrderLogic.IntFull.KripkeModel
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  -- W is a category, the interpretation of Contexts/Formulas will be a Presheaf over W
  (W    : Set)
  (_≥_  : W → W → Set)
  (id≥  : {w : W} → w ≥ w)
  (_∘≥_ : {v w z : W} → w ≥ v → z ≥ w → z ≥ v)
  (idl≥ : {v w : W}{v≥w : v ≥ w} -> id≥ ∘≥ v≥w ≡ v≥w)
  (idr≥ : {v w : W}{v≥w : v ≥ w} -> v≥w ∘≥ id≥ ≡ v≥w)
  (ass≥ : {v w z y : W}{w≥v : w ≥ v}{z≥w : z ≥ w}{y≥z : y ≥ z} -> (w≥v ∘≥ z≥w) ∘≥ y≥z ≡ w≥v ∘≥ (z≥w ∘≥ y≥z))
  where
  
  -- PSh is a presheaf over W
  record PSh : Set₁ where
    constructor Psh
    field
      P      : W → Set
      _⟨_⟩ : ∀{v w} →  P v → w ≥ v → P w
      ⟨id⟩ : ∀{w} -> (Pw : P w) -> Pw ⟨ id≥ ⟩ ≡ Pw
      ⟨∘⟩  : ∀{v w z} -> (Pv : P v)(w≥v : w ≥ v)(z≥w : z ≥ w) -> Pv ⟨ w≥v ∘≥ z≥w ⟩ ≡ (Pv ⟨ w≥v ⟩) ⟨ z≥w ⟩ 

  open PSh public renaming (P to ∣_∣; _⟨_⟩ to _∶_⟨_⟩; ⟨id⟩ to _∶⟨id⟩; ⟨∘⟩ to _∶⟨∘⟩)
  
  -- We can define the presheaf in advance because Con and For are both Psh
  
  𝟙PSh : PSh
  ∣ 𝟙PSh ∣ w = 𝟙
  𝟙PSh ∶ t ⟨ γ ⟩ = *
  (𝟙PSh ∶⟨id⟩) Pw = refl
  (𝟙PSh ∶⟨∘⟩) Pv w≥v z≥w = refl

  𝟘PSh : PSh
  ∣ 𝟘PSh ∣ x = 𝟘
  𝟘PSh ∶ () ⟨ γ ⟩
  (𝟘PSh ∶⟨id⟩) ()
  (𝟘PSh ∶⟨∘⟩) () w≥v z≥w
  
  _×PSh_ : PSh → PSh → PSh
  ∣ A ×PSh B ∣ w         = ∣ A ∣ w × ∣ B ∣ w
  (A ×PSh B) ∶ w ⟨ x ⟩   = (A ∶ (proj₁ w) ⟨ x ⟩) ,Σ (B ∶ (proj₂ w) ⟨ x ⟩)
  ((A ×PSh B) ∶⟨id⟩) Pw  = mk,= ((A ∶⟨id⟩) (proj₁ Pw)) ((B ∶⟨id⟩) (proj₂ Pw))
  ((A ×PSh B) ∶⟨∘⟩)  Pv  = λ w≥v z≥w -> mk,= ((A ∶⟨∘⟩) (proj₁ Pv) w≥v z≥w) ((B ∶⟨∘⟩) (proj₂ Pv) w≥v z≥w)

  _+PSh_ : PSh → PSh → PSh
  ∣ A +PSh B ∣ w         = ∣ A ∣ w + ∣ B ∣ w
  (A +PSh B) ∶ inj₁ Av ⟨ x ⟩   = inj₁ (A ∶ Av ⟨ x ⟩)
  (A +PSh B) ∶ inj₂ Bv ⟨ x ⟩   = inj₂ (B ∶ Bv ⟨ x ⟩)
  ((A +PSh B) ∶⟨id⟩) (inj₁ Av) = cong inj₁ ((A ∶⟨id⟩) Av)
  ((A +PSh B) ∶⟨id⟩) (inj₂ Bv) = cong inj₂ ((B ∶⟨id⟩) Bv)
  ((A +PSh B) ∶⟨∘⟩) (inj₁ Av)  = λ w≥v z≥w → cong inj₁ ((A ∶⟨∘⟩) Av w≥v z≥w)
  ((A +PSh B) ∶⟨∘⟩) (inj₂ Bv)  = λ w≥v z≥w → cong inj₂ ((B ∶⟨∘⟩) Bv w≥v z≥w)
  
  _⇒PSh_ : PSh → PSh → PSh
  ∣ A ⇒PSh B ∣ w         = ∀ {v} -> v ≥ w -> ∣ A ∣ v -> ∣ B ∣ v -- Plus naturality
  (A ⇒PSh B) ∶ t ⟨ w≥v' ⟩   = λ v≥w Av → t (w≥v' ∘≥ v≥w) Av
  ((A ⇒PSh B) ∶⟨id⟩) Pw  = funext-imp (λ {w} -> funext (λ w≥w' → funext (λ Aw → cong (λ z -> Pw z Aw) idl≥)))
  ((A ⇒PSh B) ∶⟨∘⟩)  Pv  = λ w≥v z≥w → funext-imp (λ {w} -> funext (λ w≥z → funext (λ Aw → cong (λ z → Pv z Aw) ass≥)))
  
  Con : Set₁
  Con = PSh

  Sub : Con -> Con -> Set
  Sub Γ Δ = ∀ w -> ∣ Γ ∣ w -> ∣ Δ ∣ w -- naturality

  _∘_ : {Γ Δ Θ : Con} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
  (δ ∘ γ) w Θw = δ w (γ w Θw)

  id : {Γ : Con} → Sub Γ Γ
  id = λ w z → z

  ◆ : Con
  ◆ = 𝟙PSh

  ε : {Γ : Con} → Sub Γ ◆
  ε _ _ = *

  -- Dep PshP over Con defined
  For : Con -> Set₁
  For Γ = ∀ w -> ∣ Γ ∣ w -> PSh -- PShP

  _[_]F : {Γ Δ : Con} → For Γ → Sub Δ Γ → For Δ
  (A [ γ ]F) w Δw = A w (γ w Δw)

  {-
  [∘]F : {Γ : Con}{K : For Γ}{Δ : Con}{γ : Sub Δ Γ} {Θ : Con}{δ : Sub Θ Δ} →
    (_[_]F {Γ}{Θ} K (_∘_ {Γ}{Δ}{Θ} γ δ)) ≡ (_[_]F {Δ}{Θ} (_[_]F {Γ}{Δ} K γ) δ)
  [∘]F = refl

  [id]F : {Γ : Con} {K : For Γ} → (_[_]F {Γ}{Γ} K (id {Γ})) ≡ K
  [id]F = refl
  -}
  
  Pf : (Γ : Con) -> For Γ -> Prop
  Pf Γ K = ∀ w -> (Γw : ∣ Γ ∣ w) -> Squash (∣ K w Γw ∣ w)

  _[_]p : {Γ : Con} {K : For Γ} →
      Pf Γ K → {Δ : Con} (γ : Sub Δ Γ) → Pf Δ (_[_]F {Γ}{Δ} K γ)
  (PfK [ γ ]p) w Γw = PfK w (γ w Γw)

  _▸p_ : (Γ : Con) → For Γ → Con
  ∣ Γ ▸p K ∣ v = ∀ {w} (w≥v : w ≥ v) -> Σ (∣ Γ ∣ w) λ Γw → ∣ K w Γw ∣ w
  (Γ ▸p K) ._∶_⟨_⟩ {v}{w} = λ x w≥v {z} z≥w → x (w≥v ∘≥ z≥w)
  ((Γ ▸p K) ∶⟨id⟩) = λ Pw → funext-imp (λ {w} -> funext (λ w≥w' → cong Pw idl≥))
  ((Γ ▸p K) ∶⟨∘⟩)  = λ Pv w≥v z≥w → funext-imp (λ {w} -> funext (λ w≥z → cong Pv ass≥))

  _,p_ : {Γ Δ : Con} (γ : Sub Δ Γ) {K : For Γ} →
    Pf Δ (_[_]F {Γ}{Δ} K γ) → Sub Δ (Γ ▸p K)
  _,p_ {Γ}{Δ} γ {K} PfK w Δw {v} v≥w = let PfKapp = (PfK v (Δ ∶ Δw ⟨ v≥w ⟩)) in 
    (γ v (Δ ∶ Δw ⟨ v≥w ⟩)) ,Σ unsquash PfKapp  

  pp : {Γ : Con} {K : For Γ} → Sub (Γ ▸p K) Γ
  pp w Γw = proj₁ (Γw id≥) 

  qp : {Γ : Con} {K : For Γ} → Pf (Γ ▸p K) (_[_]F {Γ}{Γ ▸p K} K (pp {Γ}{K}))
  qp w Γw = squash (Γw id≥ .proj₂)

  ▸pβ₁ : {Γ Δ : Con} {γ : Sub Δ Γ} {K : For Γ} {k : Pf Δ (_[_]F {Γ}{Δ} K γ)} →
      _∘_ {Γ}{(Γ ▸p K)}{Δ} (pp {Γ}{K}) (_,p_ {Γ}{Δ} γ {K} k) ≡ γ -- (_∘_ (pp {Γ}{K}) (_,p_ {Γ}{Δ} γ k)) ≡ γ
  ▸pβ₁ {Γ} {Δ} {γ} {K} {k} = funext (λ w → funext (λ Δw → cong (λ z → γ w z) ((Δ ∶⟨id⟩) Δw)))

{-
  ▸pη : {Γ : Con} {K : For Γ} →
      (id {Γ ▸p K}) ≡ _,p_ {Γ}{Γ ▸p K} (pp {Γ}{K}) {K} (qp {Γ}{K}) ∈ Sub (Γ ▸p K) (Γ ▸p K)
  ▸pη = funext (λ w → funext (λ x → funext-imp (λ {v} -> funext (λ v≥w → mk,= (cong proj₁ refl) {!   !}))))
-}

  Kripke : Model funar relar _ _ _ _ _
  Kripke = record
    { Con = Con
    ; Sub = Sub
    ; _∘_ = λ {Γ}{Δ}{Θ} -> _∘_ {Γ}{Δ}{Θ}
    ; id = λ {Γ} -> id {Γ}
    ; ass = refl
    ; idl = refl
    ; idr = refl
    ; ◆ = ◆
    ; ε = λ {Γ} -> ε {Γ}
    ; ◆η = λ σ → refl
    ; For = For
    ; _[_]F = λ {Γ}{K} -> _[_]F {Γ}{K}
    ; [∘]F = refl
    ; [id]F = refl
    ; Pf = Pf
    ; _[_]p = λ {Γ}{K} -> _[_]p {Γ}{K}
    ; _▸p_ = _▸p_
    ; _,p_ = λ {Γ}{K} -> _,p_ {Γ}{K}
    ; pp = λ {Γ}{K} -> pp {Γ}{K}
    ; qp = λ {Γ}{K} -> qp {Γ}{K}
    ; ▸pβ₁ = λ {Γ}{Δ}{γ}{K}{k} -> ▸pβ₁ {Γ}{Δ}{γ}{K}{k}
    ; ▸pη = {!   !}
    ; ⊥ = {!   !}
    ; ⊥[] = {!   !}
    ; exfalso = {!   !}
    ; ⊤ = {!   !}
    ; ⊤[] = {!   !}
    ; tt = {!   !}
    ; _⊃_ = {!   !}
    ; ⊃[] = {!   !}
    ; ⊃intro = {!   !}
    ; ⊃elim = {!   !}
    ; _∧_ = {!   !}
    ; ∧[] = {!   !}
    ; ∧intro = {!   !}
    ; ∧elim₁ = {!   !}
    ; ∧elim₂ = {!   !}
    ; _∨_ = {!   !}
    ; ∨[] = {!   !}
    ; ∨elim = {!   !}
    ; ∨intro₁ = {!   !}
    ; ∨intro₂ = {!   !}
    ; Tm = {!   !}
    ; _[_]t = {!   !}
    ; [∘]t = {!   !}
    ; [id]t = {!   !}
    ; _▸t = {!   !}
    ; _,t_ = {!   !}
    ; pt = {!   !}
    ; qt = {!   !}
    ; ▸tβ₁ = {!   !}
    ; ▸tβ₂ = {!   !}
    ; ▸tη = {!   !}
    ; Tms = {!   !}
    ; _[_]ts = {!   !}
    ; [∘]ts = {!   !}
    ; [id]ts = {!   !}
    ; εs = {!   !}
    ; ◆sη = {!   !}
    ; _,s_ = {!   !}
    ; π₁ = {!   !}
    ; π₂ = {!   !}
    ; ▸sβ₁ = {!   !}
    ; ▸sβ₂ = {!   !}
    ; ▸sη = {!   !}
    ; ,[] = {!   !}
    ; fun = {!   !}
    ; fun[] = {!   !}
    ; rel = {!   !}
    ; rel[] = {!   !}
    ; ∀' = {!   !}
    ; ∀[] = {!   !}
    ; ∀intro = {!   !}
    ; ∀elim = {!   !}
    ; ∃' = {!   !}
    ; ∃[] = {!   !}
    ; ∃intro = {!   !}
    ; ∃elim = {!   !}
    ; Eq = {!   !}
    ; Eq[] = {!   !}
    ; Eqrefl = {!   !}
    ; subst' = {!   !}
    }

  {-
  𝟘PSh : PSh
  ∣ 𝟘PSh ∣ = λ _ → 𝟘p
  _∶_⟨_⟩ 𝟘PSh = λ x _ → x

  _×PSh_ : PSh → PSh → PSh
  ∣ Γ ×PSh K ∣ = λ w → ∣ Γ ∣ w ×p ∣ K ∣ w
  _∶_⟨_⟩ (Γ ×PSh K) = λ (Γw ,Σ Kw) γ → (Γ ∶ Γw ⟨ γ ⟩) ,Σ (K ∶ Kw ⟨ γ ⟩)

  _+PSh_ : PSh → PSh → PSh
  ∣ Γ +PSh K ∣ = λ w → ∣ Γ ∣ w +p ∣ K ∣ w
  _∶_⟨_⟩ (Γ +PSh K) =  λ A γ → ind+p _ (λ Γw → inj₁ (Γ ∶ Γw ⟨ γ ⟩)) (λ Kw → inj₂ (K ∶ Kw ⟨ γ ⟩)) A

  _⇒PSh_ : PSh → PSh → PSh
  ∣ Γ ⇒PSh K ∣ = λ w → {w' : W} → w' ≥ w → ∣ Γ ∣ w' → ∣ K ∣ w'
  _∶_⟨_⟩ (Γ ⇒PSh K) = λ A γ δ Γw' → A (γ ∘≥ δ) Γw'

  Kripke : Model Atom _ _ _ _
  Kripke = record
    { Con = PSh
    ; Sub = λ Γ Δ → {w : W} → ∣ Γ ∣ w → ∣ Δ ∣ w
    ; _∘_ = λ δ θ θw → δ (θ θw)
    ; id = λ x → x
    ; ◆ = 𝟙PSh
    ; ε = λ x → *
    ; For = PSh
    ; Pf = λ Γ K → {w : W} → ∣ Γ ∣ w → ∣ K ∣ w
    ; _[_] = λ PfK γ Δw → PfK (γ Δw)
    ; _▸_ = _×PSh_
    ; _,_ = λ γ PfK Δw → (γ Δw) ,Σ PfK Δw
    ; p = proj₁
    ; q = proj₂
    ; ⊥ = 𝟘PSh
    ; exfalso = λ Pf⊥ Γw → ind𝟘p (Pf⊥ Γw)
    ; ⊤ = 𝟙PSh
    ; tt = λ _ → *
    ; _⊃_ = _⇒PSh_
    ; ⊃intro = λ {Γ}{K}{L} PfL Γw γ Kw' → PfL ((Γ ∶ Γw ⟨ γ ⟩) ,Σ Kw')
    ; ⊃elim = λ PfKL (Γw ,Σ Kw) → PfKL Γw id≥ Kw
    ; _∧_ = _×PSh_
    ; ∧intro = λ PfK PfL Γw → (PfK Γw) ,Σ (PfL Γw)
    ; ∧elim₁ = λ PfKL Γw → proj₁ (PfKL Γw)
    ; ∧elim₂ = λ PfKL Γw → proj₂ (PfKL Γw)
    ; _∨_ = _+PSh_
    ; ∨intro₁ = λ u Γw → inj₁ (u Γw)
    ; ∨intro₂ = λ u Γw → inj₂ (u Γw)
    ; ∨elim = λ PfKC PfLC PfKL Γw → ind+p _ (λ Kw → PfKC (Γw ,Σ Kw)) (λ Lw → PfLC (Γw ,Σ Lw)) (PfKL Γw)
    ; atom = λ x → Psh (∣ x ∣pv) (_pv:_⟨_⟩ x)
    }
    -}  