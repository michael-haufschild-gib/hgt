# HB finite physical-clock-step covariance rigidity

- **ID:** HB-FINITE-CLOCK-COVARIANCE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB open core
- **Statement:** For literal anti-linear source-FE transport and centered Birmingham--Mokhtari QNM physical evolution, covariance at one fixed real time `t` holds on a unit Xi packet iff `t = 0` or that Xi copy lies on `Re s = 1/2`; hence covariance at any one source-predeclared `t ≠ 0` on every Xi copy is equivalent to RH.

## Goal

Kill the finite-time sampling/phase-alias escape in HB and reduce the remaining source-dynamical
burden. Full chain under test:

`literal mixed-Casimir spin-two Einstein--Teukolsky source`
`→ one source-predeclared nonzero physical clock step covariant under FE--Schwarz reflection`
`→ every Xi copy has zero transverse tilt`
`→ canonical left-branch covariance / optical darkness / Ward extinction`
`→ RH`.

This is source-pure at theorem level: clock generator, source cocycle, anti-linear FE transport,
and Xi-copy reflection are already literal corpus constructions. It does not assume divisor
placement. It is not a claimed producer until the finite covariance law is derived from the
Einstein--Teukolsky PDE.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `hbXiPeierlsUnitSourceFEUnitPhysicalClockStepCovariant_iff_rh`, `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit and conjecture loop

1. **Failed conjecture HB-FC0 — two-sided passivity.** Corpus search found
   `ThetaCuspHawkingBMRadiativeSourceFEPositiveHermitianMetricNoGo`: actual radiative transport is
   an anti-linear involution and can be made antiunitary for an explicit positive Hermitian form,
   while bright off-line cancellation persists. Positivity/contractivity without a fixed physical
   clock is terminal.
2. **Failed conjecture HB-FC1 — infinitesimal clock covariance as new producer.** Corpus search
   found `ThetaCuspHawkingBMSourceFECenteredQNMClockRigidity`: the exact generator
   anticommutator is already the Xi tilt times a nowhere-zero source cocycle, so global
   anticommutation is an RH-equivalent receiver.
3. **Surviving conjecture HB-FC2 — one finite physical clock step.** Exponentiating the physical
   generator with `exp(-i t H)` changes the anti-linear reflection defect from a periodic phase to
   the positive real factor `exp(-t (Re s - 1/2))`. Therefore a single nonzero real clock sample
   has no aliases. This strictly weakens the PDE burden from an infinitesimal or all-time identity
   to one finite-time equality.

Corpus searches used:

- `scripts/formal_tools.py research "HB finite time clock sample exponential centered QNM source FE covariance phase alias"`
- `scripts/formal_tools.py research "source-predeclared clock fixed clock generator reflection antiunitary causal semigroup HB no-go"`
- `scripts/formal_tools.py research "universal one clock step reflection covariance RH centered QNM finite time"`

No declaration or gap marker states the finite one-step classification.

## External novelty audit

- Birmingham--Mokhtari, *Exact Gravitational Quasinormal Frequencies of Topological Black Holes*,
  arXiv:hep-th/0609028, gives the exact gravitational QNM tower used by the corpus.
- Green--Hollands--Sberna--Toomani--Zimmerman, *Conserved currents for Kerr and orthogonality of
  quasinormal modes*, arXiv:2210.15935, derives conserved bilinear forms and the geometric
  `t-phi` reflection symmetry for Teukolsky perturbations.
- Ma--Yang, *The excitation of quadratic quasinormal modes for Kerr black holes*,
  arXiv:2401.15516, treats second-order Teukolsky excitation but does not identify an Xi/FE finite
  clock law.

Searches found no source-FE/Xi finite-time covariance classification, no single-sample RH
criterion, and no proof that nonlinear Einstein--Teukolsky dynamics supplies this equality.

## Paper proof

Let `R` be Xi-copy reflection, `kappa(q)` the nowhere-zero literal source-FE cocycle, and
`T` the anti-linear packet transport

`T(c e_q) = kappa(q) conjugate(c) e_(Rq)`.

Let the centered BM frequency be `lambda(q) = xiSpectralPoint(q)/2`. Corpus theorems give

1. `lambda(Rq) = -lambda(q)`;
2. `conjugate(lambda(q)) + lambda(Rq) = i delta(q)`, where
   `delta(q) = Re(q) - 1/2`;
3. `kappa(q) ≠ 0`.

For real `t`, define physical centered-clock evolution

`U_t(c e_q) = exp(-i t lambda(q)) c e_q`.

Then

`T U_t(e_q) = kappa(q) exp(i t conjugate(lambda(q))) e_(Rq)`

and

`U_t T(e_q) = kappa(q) exp(-i t lambda(Rq)) e_(Rq)`
`             = kappa(q) exp(i t lambda(q)) e_(Rq)`.

After cancelling `kappa(q)`, equality is equivalent to

`exp(i t conjugate(lambda(q))) = exp(i t lambda(q))`.

Multiplying by the nonzero inverse of the right side and using exponential addition turns this
into

`exp(i t (conjugate(lambda(q)) - lambda(q))) = 1`.

By (1)--(2), `conjugate(lambda(q)) - lambda(q) = i delta(q)`, so the condition is

`exp(-t delta(q)) = 1`.

The exponent is real. Real exponential equals one iff its exponent is zero, hence
`t delta(q) = 0`, equivalently `t = 0` or `Re(q) = 1/2`. This proves the fibrewise
classification. For `t ≠ 0`, universal unit-packet covariance is therefore exactly the statement
that every Xi zero lies on the critical line, which is the corpus definition/equivalent form of
RH. Conversely RH makes `delta(q)=0` on every copy and gives covariance.

The same coefficient identity proves full finite-packet covariance under RH by extensionality.

**[PROVED HERE]** No analytic, PDE, or spectral premise remains in this classification proof.

## No-go closure

- **Exact killing theorem/mechanism:** one finite physical-time sample cannot conceal an off-wall
  Xi copy by periodic phase aliasing; anti-linearity changes the discrepancy into positive real
  gain `exp(-t delta)`, injective at value one for every `t ≠ 0`.
- **Strongest positive survivor:** it suffices to derive FE--Schwarz covariance at one arbitrary
  fixed nonzero source-predeclared physical time. No generator derivative, all-time covariance, or
  small-time bound is needed.
- **New insight:** Euclidean/exponential-clock intuition suggests phase aliases, but real physical
  QNM time and anti-linear source reflection turn horizontal Xi displacement into dissipative gain.
  Remaining HB producer can be posed as one finite source-to-source scattering equality.
- **Status:** dependency-closed paper proof and Lean formalization in
  `ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity`. Whole HB route remains live only
  at source-dynamical derivation of this one-step equality.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity`
- Fibrewise classification:
  `hbXiPeierlsUnitSourceFEPhysicalClockStep_single_commute_iff`
- Arbitrary-time global classification:
  `hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff`
- Nonzero-time RH endpoint:
  `hbXiPeierlsUnitSourceFEPhysicalClockStepCovariant_iff_rh`
- Closed unit-time endpoint:
  `hbXiPeierlsUnitSourceFEUnitPhysicalClockStepCovariant_iff_rh`
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity.lean`
  — PASS.
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity`
  — PASS.
- Axiom audit: all four theorem certificates use only `propext`, `Classical.choice`, and
  `Quot.sound`; no project axiom or hypothesis.
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- Global static lint: new module passes forbidden-token/reachability scan. Repository lint remains
  red only because two unrelated pre-existing HTGeometry modules are not umbrella-reachable:
  `RatFuncChainRule` and `RittTreeChannelMap`.

## Log

- 2026-08-30 — created in 1-in-progress after HB-FC0/HB-FC1 hostile pivots; HB-FC2 paper proof closed.
- 2026-08-30 — finite-packet Lean classification closed, module-only build and axiom audit passed;
  moved to 3-formalized.
