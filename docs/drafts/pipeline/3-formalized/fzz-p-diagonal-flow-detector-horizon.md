# FZZ-P stabilized diagonal-flow detector horizon

- **ID:** FZZ-P-HC6
- **Stage:** 3-formalized
- **Type:** THEOREM / exact dynamical cone-crossing law
- **Source:** HC3 Hermitian reflection cone + HC5 rank-one stabilized diagonal generator
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityDiagonalFlowDetectorHorizon`
- **Statement:** The exact flow of the source-gap stabilized generator transports unit diagonal
  energy along a Hermitian coefficient parabola that remains a universal reciprocal-radius
  detector through one finite source-defined horizon, including its boundary, and fails at every
  later nonnegative time.

## Main theorem

At positive scale `beta`, write

`P=P(beta)`, `Q=P(2 beta)`, `R=P(4 beta)`.

HC5's stabilized generator is

`A_*=[[P,0],[-PQ/R,0]]`

and satisfies `A_*^2=P A_*`.  Define

`k_beta(t)=(Q/R)(exp(Pt)-1)`

and

`Phi_t(u_1,u_2)=(exp(Pt)u_1, u_2-k_beta(t)u_1)`.

Then:

- `Phi_0=id` and `Phi_(s+t)=Phi_s o Phi_t`;
- `Phi_t=I+((exp(Pt)-1)/P)A_*`;
- pulling unit second-coordinate energy back along `Phi_t` gives the Hermitian reporter with
  coefficients `(k_beta(t)^2,-k_beta(t),0,1)`;
- this reporter universally separates every reciprocal-radius pair iff `k_beta(t)^2<=1`;
- for `t>=0`, that condition is equivalent to `t<=T_beta`, where
  `T_beta=log(1+R/Q)/P>0`;
- `k_beta(T_beta)=1`, so the lightlike boundary is still separating;
- every `t>T_beta` is outside the detector cone and admits a blind off-unit reflected pair;
- throughout `0<=t<=T_beta`, evolved diagonal readings on a centered Mellin carrier and its
  functional reflection agree iff `Re rho=1/2`.

## Paper proof

The rank-one polynomial law gives the exact exponential reduction

`exp(t A_*)=I+((exp(Pt)-1)/P)A_*`.

Applying it to a vector gives the displayed triangular flow.  The identity

`k(s+t)=k(t)+exp(Pt)k(s)`

proves the semigroup law directly.  Expanding

`|u_2-k u_1|^2`

gives the Hermitian coefficients `(k^2,-k,0,1)`.  HC3's sharp Lorentz-cone classification reduces
universal reciprocal-radius separation to `k^2<=1`.

For nonnegative time, `P,Q,R>0` imply `k>=0`, and positivity of exponential makes `k` strictly
order-reflecting.  Since

`exp(P T_beta)=1+R/Q`,

direct substitution gives `k(T_beta)=1`.  Therefore `k^2<=1` iff `t<=T_beta`.  HC3's constructive
outside-cone theorem supplies a blind reflected radial pair after the horizon.  Inside the closed
window, HC3's Mellin-carrier theorem converts cone membership into the pointwise equivalence with
`Re rho=1/2`.

## New route knowledge

- source-gap stabilization creates an exact semigroup but not an all-time reflection detector;
- the transported reporter follows a coefficient parabola and crosses the sharp detector cone
  exactly once;
- detector validity has an explicit positive lifetime depending only on source moments;
- critical-line detection survives at the lightlike boundary, so failure is strictly late-time;
- equilibrium or asymptotic matching cannot be inferred from this finite stabilized block;
- the surviving FZZ-P burden is a reset, renormalization, nonlocal coupling, or invariant cone law
  that prevents the transported reporter from escaping.

This advances the route by replacing a vague dynamical concern with an exact maximal validity
window and a sharp post-horizon obstruction.  It does not prove reflected matching on actual Xi
zeros or RH.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "FZZ diagonal Riesz stabilized flow semigroup reflection detector Lorentz cone time horizon"`
- `scripts/formal_tools.py research "rank one Krein generator exponential pullback Hermitian reporter cone phase blindness"`
- `scripts/formal_tools.py research "FZZ source gap triangular generator flow Mellin reflection energy matching"`
- `scripts/formal_tools.py research "Hermitian quadratic detector reciprocal radius affine shear finite time cone crossing"`

Corpus contained HC3's static cone and HC5's stabilized generator, but no exact semigroup,
pullback parabola, finite detector horizon, or post-horizon theorem.

## Literature boundary

Primary and close neighbors checked:

- Hikida--Schomerus, FZZ duality and correlation matching, arXiv:0805.3931:
  https://arxiv.org/abs/0805.3931
- Mostafazadeh, Krein-space and pseudo-Hermitian formulation, arXiv:quant-ph/0606173:
  https://arxiv.org/abs/quant-ph/0606173
- Constantinescu--Gheondea, invariant Hermitian kernels and semigroup actions,
  arXiv:math/0007183:
  https://arxiv.org/abs/math/0007183
- Abraham--Bhagwat, classification and quadrics of `2x2` pseudo-Hermitian matrices,
  arXiv:2410.18530:
  https://arxiv.org/abs/2410.18530
- Pakman, FZZ scattering and reflection coefficients, arXiv:hep-th/0606067:
  https://arxiv.org/abs/hep-th/0606067

Exact-object searches found no source-specific FZZ rank-one flow, transported reporter parabola,
or finite reciprocal-radius detector horizon.  Status is “no collision located,” not an absolute
priority claim.

## Lean closure

Main declarations:

- `fzzCigarParityDilatedSecondDiagonalStabilizedFlow_add`
- `fzzCigarParityDilatedSecondDiagonalStabilizedFlow_eq_generator`
- `fzzCigarParityDilatedSecondDiagonalStabilizedFlow_pullback`
- `fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff`
- `fzzCigarParityDilatedSecondDiagonalDetectorHorizon_pos`
- `fzzCigarParityDilatedSecondDiagonalFlowShear_horizon`
- `fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_iff_time_le`
- `fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_horizon`
- `not_fzzCigarParityDilatedSecondDiagonalFlowUniversallySeparating_of_horizon_lt`
- `fzzCigarParityDilatedSecondDiagonalStabilizedFlow_mellinReading_eq_reflection_iff`

Verification on 2026-08-28:

- direct `lake env lean` passed;
- targeted module build passed;
- axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`;
- scoped forbidden-token and `git diff --check` audits passed;
- module wired into `GaloisForLFunctions.RHTower` umbrella;
- frontier map untouched.

## Gates

- [x] 0 -> 1 in-progress: source-pure conjecture frozen after corpus search
- [x] 1 -> 2 fully-proven: flow, pullback, cone crossing, and horizon proof complete
- [x] 2 -> 3 formalized: unconditional Lean theorem package and audit
- [ ] 3 -> 4 publication-ready: independent specialist priority/physics audit

## Log

- 2026-08-28 — Conjectured after HC5 separated local spectral stability from reflection matching.
- 2026-08-28 — Exact closed detector horizon and strict late-time failure proved and formalized.
