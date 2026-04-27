# First order logic formalization in Agda in the CwF style

We present FOL as an algebraic theory (first and second-order). We show some examples working in the second-order version where its convenient to use meta level variables. We use the translation of Kaposi and Xie [^1] to translate the second-order presentation into a first-order one. We also give the double-negation translation [^2] [^3] [^4] in the first-order presentation and show some common models of FOL. We prove completeness for Beth models and Kripke models.

## Outline

```txt
lib.agda
Everything.adga
- FirstOrderLogic
  - Classical
    - Notion of Model
    - Syntax
    - Iterator
  - Intuitionistic (IntFull)
    - Notion of Model
    - Syntax
    - Iterator
    - Models (Beth)
    - Completeness for Beth
  - Intuitionistic Negative fragment (IntNegative)
    - Notion of Model
    - Syntax
    - Iterator
    - Kripke model and completeness for Kripke
  - DoubleNegationTranslation
- PropositionalLogic
  - Classical
    - Notion of Model
    - Syntax
    - Interator
    - Completeness for Bool
  - IntFull
    - Notion of Model
    - Syntax
    - Interator
    - Models (Tarski, Kripke, Beth)
    - Completeness for Beth
  - IntNegative
    - Notion of Model
    - Syntax
    - Interator
    - Models (Tarski, Kripke)
    - Completeness for Kripke
  - Classical
    - Notion of Model
    - Syntax
    - Interator
lib : common datatypes (plus, times, eq, ...) used in all files
sheaf.org : Notes on sheafs
```

## Citations and related work

[^1] : Ambrus Kaposi, Szumi Xie, [Second-Order Generalised Algebraic Theories: Signatures and First-Order Semantics](https://drops.dagstuhl.de/storage/00lipics/lipics-vol299-fscd2024/LIPIcs.FSCD.2024.10/LIPIcs.FSCD.2024.10.pdf)

[^2] :  Richard Moot, Christian Retoré, [Classical logic and intuitionistic logic: equivalent formulations in natural deduction](https://hal-lirmm.ccsd.cnrs.fr/lirmm-01281243)

[^3] : Gilda Ferreira, Paulo Oliva, [On Various Negative Translations](https://doi.org/10.48550/arXiv.1101.5442)

[^5] : Pierre Marie Pedrot, [Debunking sheafs](https://www.xn--pdrot-bsa.fr/drafts/sheaftt.pdf)
