{-# OPTIONS --prop #-}

open import lib
open import FirstOrderIntuinistic
open import FI-KripkeModel

module FI-KripkeModel.Completeness
  (funar : ℕ → Set)
  (relar : ℕ → Set)
  where

  module IM = Model (IM funar relar)

  toTms : ∀{n Γ} → IM.Tm Γ ^ n → IM.Tms Γ n
  toTms {zero}  _         = *
  toTms {suc n}{Γ} (t ,Σ ts) = IM._,s_ {Γ} (toTms {n}{Γ} ts) t

  open FI-KripkeModel
    funar
    relar
    IM.Con
    (λ Δ Γ → Squash (IM.Sub Δ Γ))
    (squash IM.id)
    (λ γ δ → squash-elim _ _ (squash-elim _ _ (λ δ γ → squash (γ IM.∘ δ)) δ) γ)
    (IM.Tm IM.◆)
    (λ n ar ts Γ → IM.Pf Γ (IM.rel {Γ} n ar (IM._[_]ts {IM.◆}{n} (toTms {n}{IM.◆} ts) {Γ} IM.ε)) )
    (λ {n}{ar}{ts}{Γ}{Δ} r γ → squash-elim _ _ (λ γ → substp (IM.Pf Δ) (trans (IM.rel[] {_}{_}{_}{toTms ts IM.[ IM.ε {Γ} ]ts}{_}{γ}) (cong (I.rel n ar) (sym (IM.[∘]ts {IM.◆}{_}{_}{Γ}{IM.ε {Γ}}{Δ}{γ})))) (IM._[_]p r γ)) γ)
    (λ n ar ts → IM.fun {IM.◆} n ar (toTms {n}{IM.◆} ts))
    
  reflect : ∀{Γ}(A : IM.For Γ) → IM.Pf Γ A → {!!} -- we need the evaluation of types
