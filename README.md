# Double negation and dialectica translation for FOL

Next step:

- Given full Classical, containing everything - DONE
  - Formalise "theorem 6.2.6" in any Model in a way that subs proof are easy - DROPPED
  - good names for un∀ and app - DONE
- Give traslation on (IntuinisticSyntax -> ClassicalModel) in DoubleNeg-2 - DONE
- Try translation IntuinisticModel -> ClassicalModel , the problem is probably transport

- Give Tarski - DONE
- Give Kripke/Beth semantics for FirstOrderClassical/Intuinistic
  - Find good explanation for Kripke/Beth
- Give notion of morphisms (extra : iterator) of Model (from Ambrus/logic)
- Completeness and Soundness

- Reorgenise files : put everything old into an old folder - DONE
- Only Keep FirstOrderClassical/FirstOrderIntuinistic/DoubleNeg-2

- Give Terms with Tms (Term telescopes) so we dont need to assume funext, otherwise we need funext to say that ℕ "commutes" with "->" on the meta level - DONE

Extra :

- Try to give the iterator

- Give different double negations for propositional logic : this can be done a lot of ways (considering direction and diff translations)

- In Peano assoc of _+_
- Test is it easier/harder to prove equations in Syntax/Standard Model
- So basically in peano :
  - in any Model (Current)
  - In the syntax
  - In the standard mode with real natural numbers

- Ask Amrbus more about the Dialectica translation, so far :
  - Give a 

TODO :

- Formalise system T, it will be Ambrus's System T with formulas
- Rename ModelClass back to Model
- Use better names/notation everywhere, this is like a last step refactor
  - No ModelClass
  - rename mk∀, lam ,... to intro, elims in FOCN, FOC
  - rename liftsubst to p⁺
- infix
- generally better names would be nice
  - epsilon into epsilonp and epsilont
- figure out db indexes for first order
- refactor proof so they as minimal as they can be
- better import and name imports (renamings)
- also fixities would help a lot
