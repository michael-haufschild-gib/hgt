# Theta-Hawking backreaction cubic completion (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBackreactionCubicCompletionEndpoint.lean` and integrated it into `RHTower.lean` plus `docs/reports/endpoints.md`.

## Unconditional theorem
For `lambda >= 1`, the coefficient-faithful reweighted Xi response
`R_full + (lambda-1) R_q` stays positive, strictly radially decreasing, and has strictly increasing radius-weighted profile. Therefore every positive ordered two-node minor of `xiSquaredEulerReweightedFullKernel q lambda` is strictly positive. Specializing `lambda=cosh(r)^2` proves strict pairwise passivity for genuine selective Hawking modular gain at every rapidity.

For any three-node kernel, define Markov/Schur long edge
`r* = Kxy*Kyz/Kyy`. Its energy factorizes into three Schur squares and its determinant is
`((Kxx*Kyy-Kxy^2)*(Kyy*Kzz-Kyz^2))/Kyy`.
Thus theta adjacent strict minors imply completed cubic is strictly positive and completed energy nonnegative. Exact repair law:
`D(r*)-D(r)=Kyy*(r*-r)^2`.

If raw theta/Hawking cubic is negative, then raw `Kxz != r*`; hence nonzero remote-shell mixing is forced, with strictly positive correction cost. This is specialized to the actual causal Hardy stimulated kernel through the source-faithful orbit/scattering equality. Offcritical orbits eventually enter raw negative cubic while the completion remains positive.

## Honest frontier
This proves passivity excludes negative cubic once canonical backreaction edge is present. It does not prove nonlinear Hawking dynamics selects `r*`, nor that all tilted sectors mix. Dynamic selection/equivalent all-tilt mixing remains RH-bearing producer. Generic KMS, CCR, group, inverse, Krein laws cannot supply cubic sign.

## Hostile-test no-go
Generic positive-even Laplace source does not imply anti-Lowner cubic PSD; explicit numerical positive atomic measure counterexample was found. Theta/Xi chamber structure is essential.

## Verification
Direct `lake env lean` passed. All 28 new declarations depend only on standard `propext`, `Classical.choice`, `Quot.sound`. Formal lint sees umbrella integration but exits on five unrelated pre-existing unreachable modules. No git used; temp scratch files removed.