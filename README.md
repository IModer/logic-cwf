# First order logic formalization in agda in the CwF style

This repo is *WIP*.

We present FOL as a algebraic theory (first and second order). We prove formulas in the second order version where its convenient to work with variables. We realize this notion of varibales by translating [1] the second order presentation into a first order on. We also give double negation translation [2] [3] [4] in the first order presentation and show some common models of our theory.

## Repo outline

- lib : common datatypes (plus, times, eq, ...) used in all files
- old - old files
- FirstOrderClassical/FirstOrderIntuinistic - notion of model and syntax
- PropositionalIntuinistic - notion of model and syntax
- FirstOderModels
  - FamModel - Families/Classical model
  - Tarski - Standard model
  - KripkeModel - First order kripke model, we use (Tm : Set)
  - Beth - Sheaf model
  - Iterator - Non dependant iterator (eleminator)
- Doublenegation
- PropositionalKripke/PropositionalKripkePositive - Kripke semantics for propositional logic, self contained, with iterator and completeness ofr the negative fragment (might want to refactor)
- PropositionalBeth - Beth semantics and completeness for full prop logic

## Double negation and (dialectica translation [dropped]) for FOL

Next step:

Iterator:

- FI-Iterator.agda
- Understand better Fors/Pfs, derive equalites for them
- try to use as little transpost as possible

Kripke semantics:

- Formalise notions of Preord, Presheaf, DepPresheaf, NatTransform
- Instead of whats in lib.Extra use Ambrus's notations for stuff

Beth semantics:

- Same as for Kripke
- understand sheafs [5]

Completeness and Soundness

## Extra

Give Terms with Tms (Term telescopes) so we dont need to assume funext, otherwise we need funext to say that ℕ "commutes" with "->" on the meta level - DONE

The result of this is that all rel/fun eqs become refl, so its "better"

Give different double negations for propositional logic : this can be done a lot of ways (considering direction and diff translations) [3/4/5]

Prove associativity of \_+\_ in Peano

- Test is it easier/harder to prove equations in Syntax/Standard Model
- So basically in peano :
  - in any Model (Current)
  - In the syntax
  - In the standard mode with real natural numbers

DROPPED: Ask Amrbus more about the Dialectica translation

## TODO

- Switch Classical to Tms also, redefine double negation in line with this

- DROPPED: Formalise system T, it will be Ambrus's System T with formulas
- Use better names/notation everywhere, this is like a last step refactor
  - mostly in old, there is still a lot of stuff that can be refactored from there
  - no ModelClass
  - rename mk∀, lam ,... to intro, elims in FOCN, FOC
  - rename liftsubst to p⁺
- generally better names would be nice
  - epsilon into epsilonp and epsilont
- Maybe "automatic" db indexes for first order logic : that is db : ℕ -> Pf (Γ ▸ K_1 ▸ K_2 ... ▸ K_n) K_1
- refactor proof so they as minimal as they can be : this is mostly the case
- better import and name imports (renamings)
- Proper fixity management : it would help a lot
- Citations and related work

## Citations and related work

[1] - [Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics](https://drops.dagstuhl.de/storage/00lipics/lipics-vol299-fscd2024/LIPIcs.FSCD.2024.10/LIPIcs.FSCD.2024.10.pdf)

[2] [3] [4] - All three papers relating to double negation translation that was used to understand it

[5] - [Pierre Marie Pedrot - Debunking sheafs](https://www.xn--pdrot-bsa.fr/drafts/sheaftt.pdf)
