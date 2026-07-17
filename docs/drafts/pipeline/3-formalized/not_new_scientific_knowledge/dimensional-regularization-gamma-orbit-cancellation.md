# One-loop dimensional-regularization kernels share one HT Gamma orbit

- **ID:** `dimensional-regularization-gamma-orbit-cancellation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** M. Wilhelm, *Amplitudes, Form Factors and the Dilatation Operator in N=4 SYM Theory*, arXiv:1410.6309, equations (C.1)--(C.2); Z. Bern, L. Dixon, D. Kosower, *Dimensionally Regulated One-Loop Integrals*, arXiv:hep-ph/9212308
- **Statement:** The exact massless bubble and one-mass triangle Gamma kernels are each HT in the dimensional regulator, but their quotient is DA because both reduce to the same half-shift Gamma translation orbit; arbitrary elementary exponential scale gauges preserve all three conclusions.

## Goal

Apply the integer-scale oriented Gamma normal form to an actual QFT regulator observable and seek a
positive relation surviving the individual HT no-go.  The target is the exact meromorphic regulator
dependence, not a finite Laurent expansion at `epsilon=0`.

## Gates

- [x] 0 → 1 in-progress: exact primary-source bubble and triangle formulas matched to the signed
  `+1/-1/-2` Gamma-family API
- [x] 1 → 2 fully-proven: explicit Gauss/reflection normal forms, individual HT, and quotient DA
- [x] 2 → 3 formalized: exact module build, direct checks, and standard-only axiom audit pass
- [ ] 3 → 4 publication-ready: application note not yet written

## Source formulas

With regulator `epsilon`, the Gamma-dependent parts are

`B(epsilon) = Gamma(epsilon) Gamma(1-epsilon)^2 / Gamma(2-2epsilon)`

and

`T(epsilon) = Gamma(1+epsilon) Gamma(-epsilon)^2 / Gamma(1-2epsilon)`.

The source multiplies these by elementary powers such as `exp(epsilon*gamma_E)` and
`(-q^2)^(-epsilon)`.  For fixed nonzero kinematics their regulator dependence is an exponential
gauge, hence DA and nonzero.

## Exact normal forms

Gauss multiplication at scale two and Euler reflection give

`B = G_B * Gamma(epsilon-1/2)`

and

`T = G_T * Gamma(epsilon+1/2)`,

where `G_B` and `G_T` are explicitly constructed nonzero DA gauges.  Each residual Gamma factor is
HT.  Their quotient is nevertheless DA because

`Gamma(epsilon+1/2) / Gamma(epsilon-1/2)`

is an integer-translate ratio.  This is the positive statement: the two individually HT loop
observables carry the same Gamma orbit charge, so relative observation cancels the HT source.

## Corpus value

This is the first direct QFT consumer of the signed integer-scale Gamma normal form.  It verifies
that the API can expose both an HT obstruction and a nontrivial cross-observable cancellation.  It
also adds the missing exact bridges identifying unit positive and negative natural scales with the
pre-existing unit-scale Gamma elements.

The result applies unchanged after arbitrary elementary exponential regulator gauges.  It does not
claim that a Laurent truncation is HT, nor that every Feynman integral has this orbit.
Moreover, the exact dressed bubble and triangle responses are certified unequal to every rational
or finite-Laurent regulator model.  This gives a direct symbolic-regression/finite-perturbation
boundary without claiming that finite truncations are poor local approximations.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.DimensionalRegularizationGammaBoundary`

- `masslessBubbleGammaMero_normalForm`
- `hypertranscendentalOver_masslessBubbleGammaMero`
- `masslessTriangleGammaMero_normalForm`
- `hypertranscendentalOver_masslessTriangleGammaMero`
- `differentialAlgebraicOver_masslessTriangleGammaMero_div_masslessBubbleGammaMero`
- `hypertranscendentalOver_masslessBubbleOneLoopMero`
- `hypertranscendentalOver_masslessTriangleOneLoopMero`
- `masslessBubbleOneLoopMero_ne_ratFuncModel`
- `masslessTriangleOneLoopMero_ne_ratFuncModel`
- `differentialAlgebraicOver_masslessTriangleOneLoopMero_div_masslessBubbleOneLoopMero`

All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## RH pressure test

The shared-orbit quotient law is useful methodology for distinguishing absolute HT from relative
DA cancellation.  Applied to completed L-functions, the analogous task would be to isolate a
shared archimedean orbit before looking for a genuinely arithmetic residual.  This module itself
provides no prime carrier, zero-free result, or RH implication.

## Log

- 2026-07-17 — exact bubble and triangle normal forms, individual HT, common-orbit quotient DA,
  and exponential-gauge stability formalized and verified.
