# Route N C18: squarefree Xi unit-germ landing

Date: 2026-08-10

## Formal module

`formal/GaloisForLFunctions/RHTower/HedenmalmGammaSewnSquarefreeXiConormalBridge.lean`
umbrella-wired.

Direct compile, explicit olean generation, and axiom audit pass. Axioms only `propext`, `Classical.choice`, `Quot.sound`.

## Exact result

Define squarefree reporter unit `u_sq(s)=riemannZeta(2s)^-1`.
For `Re s>1/2`, it is analytic and nonzero.
The squarefree Mellin reporter satisfies globally:
`squarefreePartition(s)=riemannZeta(s)*u_sq(s)`.

Hence on strict-right strip `1/2<Re rho<1`:
- `analyticOrderAt squarefreePartition rho = analyticOrderAt riemannZeta rho`;
- existing archimedean unit theorem gives
  `analyticOrderAt squarefreePartition rho = analyticOrderAt xi rho`;
- `squarefreePartition rho=0 iff xi rho=0`.

This includes every multiplicity.

## Honest interpretation

This is corpus consolidation: existing `SquarefreeFixedCurrentLocalization` and Xi order theorems already contained ingredients. It closes algebraic principal-conormal/multiplicity attachment of strict-right Xi germs into squarefree reporter. Do not list “attach every Xi conormal algebraically” as open.

Remaining Route N producer is strictly topological:
- construct strict critical Fourier--Mellin/Cartier completion of this unit-flat germ;
- prove every conormal/multiplicity jet survives normally;
- prove prime coverings/Fourier transport completely nonexpansive;
- prove exceptional specialization conserves squarefree parity modular marginal.

Analytic unit equality alone does not imply critical-sector normality or complete nonexpansivity.

Docs updated through C18 and frontier open core corrected.
