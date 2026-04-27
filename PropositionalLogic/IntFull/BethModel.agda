open import lib
open import PropositionalLogic.IntFull.Model

module PropositionalLogic.IntFull.BethModel 
    (Atom : Set) 
    where

record Preorder : Set₁ where
    no-eta-equality

    infix 4 _≥_
    infixl 9 _∘≥_
    field
        W : Set
        _≥_ : W → W → Prop
        id≥ : ∀ {i} → i ≥ i
        _∘≥_ : ∀ {i j k} → j ≥ i → k ≥ j → k ≥ i

-- Over a Category we have
-- Sieve, Topology, Sheaf

module Sh (P : Preorder) where
    open Preorder P

    -- A Sieve is an upper set of an element, with proof that its higher up

    -- A Sieve is also an "ideal" in a sense that its all morphisms with cod i in P that are closed under precomposition 
    
    record Sieve (i : W) : Set₁ where
        field
            R     : (w : W) -> w ≥ i -> Prop -- all morphisms with cod i st.
            restr : ∀ {j j≥i k} -> R j j≥i -> (k≥j : k ≥ j) -> R k (j≥i ∘≥ k≥j) -- they can be procomposed

    {-
    Sieves on objects are an equivalent way to talk about subobjects of representable functors 
    in a presheaf category in terms of the total sets of elements of such a subfunctor.
    -}

    open Sieve public renaming (R to ∣_∣)

    infix 0 ⟨_,_⟩⊩_
    ⟨_,_⟩⊩_ : ∀ {i} j → j ≥ i → Sieve i → Prop
    ⟨ j , j≥i ⟩⊩ R = ∣ R ∣ j j≥i

    infixl 9 _[_]ˢ
    _[_]ˢ : ∀ {i j} → Sieve i → j ≥ i → Sieve j
    ∣ R [ j≥i ]ˢ ∣ k k≥j = ⟨ k , j≥i ∘≥ k≥j ⟩⊩ R
    (R [ j≥i ]ˢ) .restr j⊩A k≥j = R .restr j⊩A k≥j

    -- A Topology over a category is choosing with morphisms are covers

    record Top : Set₁ where
        infix 4 _◁_
        infixl 9 _[_]ᶜ
        field
            _◁_     : (i : W) -> Sieve i -> Prop -- a subset of points can be a cover st.
            _[_]ᶜ   : ∀{i j R} -> i ◁ R -> (j≥i : j ≥ i) -> j ◁ (R [ j≥i ]ˢ)
            -- The whole set is always an cover
            maximal : ∀{i R} -> ⟨ i , id≥ ⟩⊩ R -> i ◁ R
            -- the union of covers is a cover
            local   : ∀{i R S} -> i ◁ R -> (∀{j} (j≥i : j ≥ i) -> ⟨ j , j≥i ⟩⊩ R -> j ◁ S [ j≥i ]ˢ) -> i ◁ S

    -- Then a Sheaf is just a presheaf that has glue
    record Sheaf(J : Top) : Set₁ where
        
        open Top J
        
        field
            A     : W -> Prop
            restr : ∀{i j} -> A i -> j ≥ i -> A j
            glue  : ∀{i R} -> i ◁ R -> (∀{j} (j≥i : j ≥ i) -> ⟨ j , j≥i ⟩⊩ R -> A j) -> A i 

    open Sheaf public renaming (A to ∣_∣)

module Semantics
    (P : Preorder)
    (open Sh P)
    (J : Top)
    (val : Atom -> Sheaf J)
    where

    open Preorder P
    open Top J

    𝟙Sh : Sheaf J
    𝟙Sh .Sh.∣_∣ _ = 𝟙p
    𝟙Sh .Sh.restr = λ _ _ -> *
    𝟙Sh .Sh.glue  = λ i◁R u -> *

    𝟘Sh : Sheaf J
    𝟘Sh .Sh.∣_∣ i = i ◁ sieve
        where
        sieve : Sieve i
        ∣ sieve ∣ j j≥i = 𝟘p
        sieve .restr () k≥j
    𝟘Sh .Sh.restr = _[_]ᶜ
    𝟘Sh .Sh.glue  = local

    _×Sh_ : Sheaf J -> Sheaf J -> Sheaf J
    (A ×Sh B) .Sh.∣_∣ i = ∣ A ∣ i ×p ∣ B ∣ i
    (A ×Sh B) .Sh.restr = λ {(Ai ,Σ Bi) j≥i → (Sh.restr A Ai j≥i) ,Σ Sh.restr B Bi j≥i}
    (A ×Sh B) .Sh.glue  = λ i◁R f -> (A .glue i◁R λ j≥i x → proj₁ (f j≥i x)) ,Σ (B .glue i◁R λ j≥i x → proj₂ (f j≥i x))
    
    _⇒Sh_ : Sheaf J -> Sheaf J -> Sheaf J
    (A ⇒Sh B) .Sh.∣_∣ i = ∀{j} -> j ≥ i -> ∣ A ∣ j -> ∣ B ∣ j
    (A ⇒Sh B) .Sh.restr = λ f j≥i k≥j Ak → f (j≥i ∘≥ k≥j) Ak
    (A ⇒Sh B) .Sh.glue  = λ i◁R f j≥i Aj -> B .glue (i◁R [ j≥i ]ᶜ) λ j≥k Rj → f (j≥i ∘≥ j≥k) Rj id≥ (Sh.restr A Aj j≥k)

    _+Sh_ : Sheaf J -> Sheaf J -> Sheaf J
    (A +Sh B) .Sh.∣_∣ i = i ◁ sieve
        where
        sieve : Sieve i
        sieve .Sh.∣_∣   = λ j j≥i → ∣ A ∣ j +p ∣ B ∣ j
        sieve .Sh.restr (inj₁ Aj) = λ k≥j → inj₁ (Sh.restr A Aj k≥j)
        sieve .Sh.restr (inj₂ Bj) = λ k≥j → inj₂ (Sh.restr B Bj k≥j)
    (A +Sh B) .Sh.restr = _[_]ᶜ
    (A +Sh B) .Sh.glue  = local

    Con : Set₁
    Con = Sheaf J

    Sub : Sheaf J -> Sheaf J -> Prop
    Sub Δ Γ = ∀{i} -> ∣ Δ ∣ i -> ∣ Γ ∣ i
    
    ◆ : Con
    ◆ = 𝟙Sh

    ε : ∀{Γ} -> Sub Γ ◆
    ε = λ _ → *

    id : ∀{Γ} -> Sub Γ Γ
    id = λ z → z

    _∘_ : ∀{Γ Δ Θ} -> Sub Δ Γ -> Sub Θ Δ -> Sub Θ Γ
    (δ ∘ γ) Θi = δ (γ Θi)

    For : Set₁
    For = Sheaf J

    Pf  : Con -> For -> Prop
    Pf  = Sub

    _[_] : ∀{Γ K} → Pf Γ K → ∀{Δ} -> Sub Δ Γ → Pf Δ K
    (t [ γ ]) Δi = t (γ Δi)

    _▸_ : Con -> For -> Con
    _▸_ = _×Sh_

    _,_ : {Γ Δ : Con} → Sub Δ Γ → {K : For} → Pf Δ K → Sub Δ (Γ ▸ K)
    _,_ = λ γ p Δi → γ Δi ,Σ p Δi

    p : {Γ : Con} {K : For} → Sub (Γ ▸ K) Γ
    p = proj₁
    q : {Γ : Con} {K : For} → Pf (Γ ▸ K) K
    q = proj₂

    ⊥ : For
    ⊥ = 𝟘Sh

    exfalso : {Γ : Con} {K : For} → Pf Γ ⊥ → Pf Γ K
    exfalso {Γ} {K} Pf⊥ {i} Γi = K .glue (Pf⊥ Γi) λ j≥i ()

    ⊤ : For
    ⊤ = 𝟙Sh

    tt : ∀{Γ} -> Pf Γ ⊤
    tt = λ _ → *

    _⊃_ : For -> For -> For
    _⊃_ = _⇒Sh_

    ⊃intro : ∀{Γ K L} → Pf (Γ ▸ K) L → Pf Γ (K ⊃ L)
    ⊃intro {Γ} pfl Γi j≥i Kj = pfl (Γ .restr Γi j≥i ,Σ Kj)
    
    ⊃elim  : ∀{Γ K L} → Pf Γ (K ⊃ L) → Pf (Γ ▸ K) L
    ⊃elim pfkl (Γi ,Σ Ki) = pfkl Γi id≥ Ki

    _∧_ : For -> For -> For
    _∧_ = _×Sh_

    ∧intro : ∀{Γ K L} → Pf Γ K → Pf Γ L → Pf Γ (K ∧ L)
    ∧intro = λ PfK PfL Γi → PfK Γi ,Σ PfL Γi
    
    ∧elim₁  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ A
    ∧elim₁ = λ PfAB Γi → proj₁ (PfAB Γi)
    
    ∧elim₂  : ∀{Γ A B} → Pf Γ (A ∧ B) → Pf Γ B
    ∧elim₂ = λ PfAB Γi → proj₂ (PfAB Γi)

    _∨_ : For -> For -> For
    _∨_ = _+Sh_
    
    ∨intro₁ : ∀{Γ K L} → Pf Γ K → Pf Γ (K ∨ L)
    ∨intro₁ PfK Γi = maximal (inj₁ (PfK Γi))

    ∨intro₂ : ∀{Γ K L} → Pf Γ L → Pf Γ (K ∨ L)
    ∨intro₂ PfL Γi = maximal (inj₂ (PfL Γi))

    ∨elim   : ∀{Γ K L C} → Pf (Γ ▸ K) C → Pf (Γ ▸ L) C → Pf Γ (K ∨ L) → Pf Γ C
    ∨elim {Γ} {K} {L} {C} PfKC PfLC PfKL {i} Γi = C .glue (PfKL Γi) λ 
        { j≥i (inj₁ x) → PfKC (Sh.restr Γ Γi j≥i ,Σ x)
        ; j≥i (inj₂ x) → PfLC (Sh.restr Γ Γi j≥i ,Σ x)}

    atom : Atom → For
    atom = val

    Beth : Model Atom _ _ _ _
    Beth = record
        { Con = Con
        ; Sub = Sub
        ; _∘_ = λ {Γ}{Δ}{Θ} -> _∘_ {Γ}{Δ}{Θ}
        ; id = λ {Γ} -> id {Γ}
        ; ◆ = ◆
        ; ε = λ {Γ} -> ε {Γ}
        ; For = For
        ; Pf = Pf
        ; _[_] = λ {Γ}{K} -> _[_] {Γ}{K}
        ; _▸_ = _▸_
        ; _,_ = λ {Γ}{K} -> _,_ {Γ}{K}
        ; p = λ {Γ}{K} -> p {Γ}{K}
        ; q = λ {Γ}{K} -> q {Γ}{K}
        ; ⊥ = ⊥
        ; exfalso = λ {Γ} {K} -> exfalso {Γ} {K}
        ; ⊤ = ⊤
        ; tt = λ {Γ} -> tt {Γ}
        ; _⊃_ = _⊃_
        ; ⊃intro = λ {Γ}{K}{L} -> ⊃intro {Γ}{K}{L}
        ; ⊃elim = λ {Γ}{K}{L} -> ⊃elim {Γ}{K}{L}
        ; _∧_ = _∧_
        ; ∧intro = λ {Γ}{K}{L} -> ∧intro {Γ}{K}{L}
        ; ∧elim₁ = λ {Γ}{K}{L} -> ∧elim₁ {Γ}{K}{L}
        ; ∧elim₂ = λ {Γ}{K}{L} -> ∧elim₂ {Γ}{K}{L}
        ; _∨_ = _∨_
        ; ∨intro₁ = λ {Γ}{K}{L}    -> ∨intro₁ {Γ}{K}{L}
        ; ∨intro₂ = λ {Γ}{K}{L}    -> ∨intro₂ {Γ}{K}{L}
        ; ∨elim   = λ {Γ}{K}{L}{C} -> ∨elim   {Γ}{K}{L}{C}
        ; atom = atom
        }

module Completeness where

    import PropositionalLogic.IntFull.Syntax Atom as I
    -- We open Semantics with the specific W that allows us to show its iso to the Syntax

    P : Preorder
    P .Preorder.W = I.Con
    P .Preorder._≥_ = I.Sub
    P .Preorder.id≥ = I.id
    P .Preorder._∘≥_ = I._∘_

    open Sh P

    infix 4 _◁_
    data _◁_ (Γ : I.Con)(R : Sieve Γ) : Prop where
        maximal : ⟨ Γ , I.id ⟩⊩ R -> Γ ◁ R
        ◁-⊥ : I.Pf Γ I.⊥ -> Γ ◁ R
        ◁-∨ : ∀ {A B} -> 
            (∀ {Δ} -> (γ : I.Sub Δ Γ) -> I.Pf Δ A -> Δ ◁ R [ γ ]ˢ) ->
            (∀ {Δ} -> (γ : I.Sub Δ Γ) -> I.Pf Δ B -> Δ ◁ R [ γ ]ˢ) ->
            I.Pf Γ (A I.∨ B) -> Γ ◁ R

    _[_]ᶜ : ∀{Γ Δ R} -> Γ ◁ R → (γ : I.Sub Δ Γ) → Δ ◁ R [ γ ]ˢ
    (_[_]ᶜ {Γ}{Δ}{R} (maximal x) γ) = maximal (R .restr x γ)
    ◁-⊥ x [ γ ]ᶜ = ◁-⊥ (x I.[ γ ])
    ◁-∨ x y z [ γ ]ᶜ = ◁-∨ (λ {Θ} δ l → x (γ I.∘ δ) l) (λ {Θ} δ k → y (γ I.∘ δ) k) (z I.[ γ ])

    local : ∀{Γ R S} -> Γ ◁ R →
      ({Δ : I.Con} (γ : I.Sub Δ Γ) → ⟨ Δ , γ ⟩⊩ R → Δ ◁ S [ γ ]ˢ) → Γ ◁ S
    local (maximal x) f = f I.id x
    local (◁-⊥ x) f = ◁-⊥ x
    local (◁-∨ f g x) h = 
        ◁-∨ (λ γ a → local (f γ a) λ δ k -> h (γ I.∘ δ) k)
            (λ γ b → local (g γ b) λ δ l -> h (γ I.∘ δ) l) 
            x

    J : Top
    J .Sh.Top._◁_ = _◁_
    J .Sh.Top._[_]ᶜ = _[_]ᶜ
    J .Sh.Top.maximal = maximal
    J .Sh.Top.local = local

    val : Atom -> Sheaf J
    ∣ val A ∣ Γ   = Γ ◁ sieve
        where
            sieve : Sieve Γ
            ∣ sieve ∣ Δ γ = I.Pf Δ (I.atom A)
            restr sieve x k≥j = x I.[ k≥j ]
    restr (val a) = _[_]ᶜ
    glue  (val a) = local

    open Semantics P J val
    import PropositionalLogic.IntFull.Iterator as IT
    open IT.Ite Atom Beth

    reify   : ∀{Γ} (A : I.For) -> ∣ ⟦ A ⟧F ∣ Γ -> I.Pf Γ A
    reify-∨    : ∀{Γ} (A B : I.For) -> ∣ ⟦ A I.∨ B ⟧F ∣ Γ -> I.Pf Γ (A I.∨ B)
    reify-⊥    : ∀{Γ} -> ∣ ⟦ I.⊥ ⟧F ∣ Γ -> I.Pf Γ I.⊥
    reify-atom : ∀{Γ} (A : Atom) -> ∣ ⟦ I.atom A ⟧F ∣ Γ -> I.Pf Γ (I.atom A)
    
    reflect : ∀{Γ} (A : I.For) -> I.Pf Γ A -> ∣ ⟦ A ⟧F ∣ Γ

    reify-∨ A B (maximal (inj₁ x)) = I.∨intro₁ (reify A x)
    reify-∨ A B (maximal (inj₂ x)) = I.∨intro₂ (reify B x)
    reify-∨ A B (◁-⊥ x) = I.exfalso x
    reify-∨ A B (◁-∨ f g x) = I.∨elim (reify-∨ A B (f I.p I.q)) (reify-∨ A B (g I.p I.q)) x
    
    reify-⊥ (◁-⊥ x) = I.exfalso x
    reify-⊥ (◁-∨ f g x) = I.∨elim (reify-⊥ (f I.p I.q)) (reify-⊥ (g I.p I.q)) x
    
    reify-atom A (maximal x) = x
    reify-atom A (◁-⊥ x) = I.exfalso x
    reify-atom A (◁-∨ f g x) = I.∨elim (reify-atom A (f I.p I.q)) (reify-atom A (g I.p I.q)) x

    reify I.⊤        _         = I.tt
    reify I.⊥        p         = reify-⊥ p
    reify (A I.⊃ B)  p         = I.⊃intro (reify B (p I.p (reflect A I.q)))
    reify (A I.∧ B) (pa ,Σ pb) = I.∧intro (reify A pa) (reify B pb)
    reify (A I.∨ B)  p         = reify-∨ A B p
    reify (I.atom a) p         = reify-atom a p
    
    reflect I.⊤        _ = *
    reflect I.⊥        p = ◁-⊥ p
    reflect (A I.⊃ B)  p = λ γ pa -> reflect B (I.⊃elim p I.[ γ I., (reify A pa) ])
    reflect (A I.∧ B)  p = (reflect A (I.∧elim₁ p)) ,Σ (reflect B (I.∧elim₂ p))
    reflect (A I.∨ B) p = ◁-∨ (λ γ x → maximal (inj₁ (reflect A x))) (λ γ x → maximal (inj₂ (reflect B x))) p
    reflect (I.atom a) p = maximal p

    reflect-Con : ∀{Γ} Δ -> I.Sub Γ Δ -> ∣ ⟦ Δ ⟧C ∣ Γ
    reflect-Con I.◆       _ =  *
    reflect-Con (Δ I.▸ x) γ = (reflect-Con Δ (I.p I.∘ γ)) ,Σ (reflect x (I.q I.[ γ ]))

    module M = Model Beth
    open M

    completeness : ∀{Γ} A -> M.Pf ⟦ Γ ⟧C ⟦ A ⟧F -> I.Pf Γ A
    completeness {Γ} A p = reify A (p (reflect-Con Γ I.id))

    soundness : ∀{Γ} A -> I.Pf Γ A -> M.Pf ⟦ Γ ⟧C ⟦ A ⟧F
    soundness A = ⟦_⟧Pf 