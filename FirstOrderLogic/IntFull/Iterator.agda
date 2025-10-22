{-# OPTIONS --prop #-}

open import lib
open import FirstOrderLogic.IntFull.Model

module FirstOrderLogic.IntFull.Iterator
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

record Morphism (i j k l m : Level)(M N : Model funar relar i j k l m) : Set (lsuc (i ⊔ j ⊔ k ⊔ l ⊔ m)) where
    private module M = Model M
    private module N = Model N
    
    field
        ⟦_⟧C : M.Con -> N.Con
        ⟦_⟧S : {Γm Δm : M.Con} -> M.Sub Δm Γm -> N.Sub (⟦ Δm ⟧C) (⟦ Γm ⟧C)
        ⟦id⟧ : {Γm : M.Con} -> ⟦ M.id {Γm} ⟧S ≡ N.id {⟦ Γm ⟧C}
        ⟦∘⟧  : {Γm Δm Θm : M.Con}{γm : M.Sub Δm Γm}{δm : M.Sub Θm Δm} -> ⟦ γm M.∘ δm ⟧S ≡ ⟦ γm ⟧S N.∘ ⟦ δm ⟧S
        ⟦◆⟧  : ⟦ M.◆ ⟧C ≡ N.◆
        ⟦ε⟧   : {Γm : M.Con} -> ⟦ M.ε {Γm} ⟧S ≡ transport (N.Sub ⟦ Γm ⟧C) (sym ⟦◆⟧) (N.ε {⟦ Γm ⟧C})
        ⟦_⟧F  : {Γm : M.Con} -> M.For Γm -> N.For ⟦ Γm ⟧C
        ⟦[]F⟧ : {Γm Δm : M.Con}{Am : M.For Γm}{γm : M.Sub Δm Γm} -> ⟦ (Am M.[ γm ]F) ⟧F ≡ (⟦ Am ⟧F) N.[ (⟦ γm ⟧S) ]F
        ⟦_⟧Pf : {Γm : M.Con}{Am : M.For Γm} -> M.Pf Γm Am -> N.Pf (⟦ Γm ⟧C) (⟦ Am ⟧F)
        -- Not needed cos Pf Γ A:  Prop
        -- ⟦[]p⟧ : {Γm Δm : M.Con}{Am : M.For Γm}{γm : M.Sub Δm Γm}{PfAm : M.Pf Γm Am} -> ⟦ (PfAm M.[ γm ]p) ⟧Pf ≡ ⟦ PfAm ⟧Pf N.[ ⟦ γm ⟧S ]p
        ⟦▸p⟧ : {Γm : M.Con}{Am : M.For Γm} -> ⟦ Γm M.▸p Am ⟧C ≡ ⟦ Γm ⟧C N.▸p ⟦ Am ⟧F
        ⟦,p⟧ : {Γm Δm : M.Con}{Am : M.For Γm}{γm : M.Sub Δm Γm}{PfAm : M.Pf Δm (Am M.[ γm ]F )} -> ⟦ γm M.,p PfAm ⟧S ≡ transport (N.Sub ⟦ Δm ⟧C) (sym ⟦▸p⟧) (⟦ γm ⟧S N.,p substp (N.Pf ⟦ Δm ⟧C) ⟦[]F⟧ ⟦ PfAm ⟧Pf)
        ⟦pp⟧ : {Γm : M.Con}{Am : M.For Γm} -> ⟦ M.pp {Γm} {Am} ⟧S ≡ transport (λ z -> N.Sub z ⟦ Γm ⟧C) (sym ⟦▸p⟧) (N.pp {⟦ Γm ⟧C} {⟦ Am ⟧F})
        
        ⟦⊥⟧  : {Γm : M.Con} -> ⟦ M.⊥ {Γm} ⟧F ≡ N.⊥ {⟦ Γm ⟧C}
        ⟦⊤⟧  : {Γm : M.Con} -> ⟦ M.⊤ {Γm} ⟧F ≡ N.⊤ {⟦ Γm ⟧C}
        ⟦∧⟧  : {Γm : M.Con}{Am Bm : M.For Γm} -> ⟦ Am M.∧ Bm ⟧F ≡ ⟦ Am ⟧F N.∧ ⟦ Bm ⟧F
        ⟦∨⟧  : {Γm : M.Con}{Am Bm : M.For Γm} -> ⟦ Am M.∨ Bm ⟧F ≡ ⟦ Am ⟧F N.∨ ⟦ Bm ⟧F
        ⟦⊃⟧  : {Γm : M.Con}{Am Bm : M.For Γm} -> ⟦ Am M.⊃ Bm ⟧F ≡ ⟦ Am ⟧F N.⊃ ⟦ Bm ⟧F

        ⟦_⟧Tm : {Γm : M.Con} -> M.Tm Γm -> N.Tm ⟦ Γm ⟧C
        ⟦[]t⟧ : {Γm Δm : M.Con}{γm : M.Sub Δm Γm}{tm : M.Tm Γm} -> ⟦ tm M.[ γm ]t ⟧Tm ≡ ⟦ tm ⟧Tm N.[ ⟦ γm ⟧S ]t

        ⟦▸t⟧  : {Γm : M.Con} -> ⟦ Γm M.▸t ⟧C ≡ ⟦ Γm ⟧C N.▸t
        ⟦,t⟧  : {Γm Δm : M.Con}{γm : M.Sub Δm Γm}{tm : M.Tm Δm} -> ⟦ γm M.,t tm ⟧S ≡ transport (N.Sub ⟦ Δm ⟧C) (sym ⟦▸t⟧) (⟦ γm ⟧S N.,t ⟦ tm ⟧Tm)
        ⟦pt⟧  : {Γm : M.Con} -> ⟦ M.pt {Γm} ⟧S  ≡ transport (λ z -> N.Sub z ⟦ Γm ⟧C) (sym ⟦▸t⟧) (N.pt {⟦ Γm ⟧C})
        ⟦qt⟧  : {Γm : M.Con} -> ⟦ M.qt {Γm} ⟧Tm ≡ transport N.Tm (sym ⟦▸t⟧) (N.qt {⟦ Γm ⟧C})
        
        ⟦_⟧Tms : {Γm : M.Con}{n : ℕ} -> M.Tms Γm n -> N.Tms ⟦ Γm ⟧C n
        ⟦[]ts⟧ : {Γm Δm : M.Con}{γm : M.Sub Δm Γm}{n : ℕ}{tmsm : M.Tms Γm n} -> ⟦ tmsm M.[ γm ]ts ⟧Tms ≡ ((⟦ tmsm ⟧Tms) N.[ ⟦ γm ⟧S ]ts)
        ⟦εs⟧   : {Γm : M.Con} -> ⟦ M.εs {Γm} ⟧Tms ≡ N.εs {⟦ Γm ⟧C}
        ⟦,s⟧   : {Γm Δm : M.Con}{γm : M.Sub Δm Γm}{n : ℕ}{tmsm : M.Tms Γm n}{tm : M.Tm Γm} -> ⟦ tmsm M.,s tm ⟧Tms ≡ (⟦ tmsm ⟧Tms N.,s ⟦ tm ⟧Tm)
        ⟦π₁⟧   : {Γm Δm : M.Con}{n : ℕ}{tmsm : M.Tms Γm (suc n)} -> ⟦ M.π₁ tmsm ⟧Tms ≡ N.π₁ ⟦ tmsm ⟧Tms
        ⟦π₂⟧   : {Γm Δm : M.Con}{n : ℕ}{tmsm : M.Tms Γm (suc n)} -> ⟦ M.π₂ tmsm ⟧Tm  ≡ N.π₂ ⟦ tmsm ⟧Tms

        ⟦fun⟧  : {Γm : M.Con}{n : ℕ}{ar : funar n}{tmsm : M.Tms Γm n} -> ⟦ M.fun n ar tmsm ⟧Tm ≡ N.fun n ar ⟦ tmsm ⟧Tms
        ⟦rel⟧  : {Γm : M.Con}{n : ℕ}{ar : relar n}{tmsm : M.Tms Γm n} -> ⟦ M.rel n ar tmsm ⟧F  ≡ N.rel n ar ⟦ tmsm ⟧Tms

        ⟦∀⟧    : {Γm : M.Con}{Am : M.For (Γm M.▸t)} -> ⟦ M.∀' Am ⟧F ≡ N.∀' (transport N.For ⟦▸t⟧ ⟦ Am ⟧F)
        ⟦∃⟧    : {Γm : M.Con}{Am : M.For (Γm M.▸t)} -> ⟦ M.∃' Am ⟧F ≡ N.∃' (transport N.For ⟦▸t⟧ ⟦ Am ⟧F)

        ⟦Eq⟧   : {Γm : M.Con}{tm tm' : M.Tm Γm} -> ⟦ M.Eq tm tm' ⟧F ≡ N.Eq ⟦ tm ⟧Tm ⟦ tm' ⟧Tm

