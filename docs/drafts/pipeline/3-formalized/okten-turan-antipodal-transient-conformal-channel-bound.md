# Okten--Turan transient antipodal conformal-channel bound

- **ID:** `okten-turan-antipodal-transient-conformal-channel-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM (published literature) / `[LITERATURE]`
- **Source:** M. B. Okten and A. S. Turan, *Antipodal constraints on transient Hawking radiation in a conformal channel*, arXiv:2608.19244v1, equations (4)--(108)
- **Statement:** A restored Hilbert-valued peeling path whose centred antipodal mismatch reaches squared norm `Mmax` forces integrated conformal-channel defect at least `cCFT/(24*pi) * 2/(1 + Jmin^(-1/2)) * (sqrt Mmax - epsilonEnd) - remainderBudget`.

## Goal

Formalize every non-duplicate proved proposition in the paper: exact robust lower bound,
exact-endpoint specialization, positive-threshold corollary, conformal forcing-scale form,
time-averaged form, equality calibration, and their analytic/geometric dependencies. Preserve the
paper's mathematical assumptions exactly; do not promote its selected channel and remainder model
to an unconditional four-dimensional Hawking theorem.

## Exact abstract claim

Let `H` be a real Hilbert space, `I = [u0,u1]`, `kappa : I -> H` an absolutely continuous path,
`P : H ->L[R] H` an orthogonal projection, and `T : H ->L[R] H` the fixed antipodal-composition
operator with `||T x|| <= alpha ||x||`, where `alpha = Jmin^(-1/2)`. Put

```text
q(u) = P (kappa(u) - T(kappa(u))),
Mmax = sup_u ||q(u)||^2.
```

Assume `||q(u0)|| <= epsilonEnd`, `||q(u1)|| <= epsilonEnd`, and almost everywhere

```text
deltaF(u) = cCFT/(24*pi) * kappa'(u) + remainder(u),
```

with the displayed norms integrable and `cCFT > 0`. Then

```text
integral_I ||deltaF(u)|| du
  >= cCFT/(24*pi) * 2/(1 + alpha) * (sqrt Mmax - epsilonEnd)
       - integral_I ||remainder(u)|| du.
```

Exact restoration is `epsilonEnd = 0`. The paper's geometric form substitutes
`alpha = Jmin^(-1/2)` and `Mmax = sup_u Mcent[kappa(u)]`.

## Gates

- [x] 0 -> 1 in-progress: exact source, hypotheses, capstone, and dependency audit lane fixed
- [x] 1 -> 2 fully-proven: independent dependency-closed paper proof survives hostile audit
- [x] 2 -> 3 formalized: exact Lean declarations, targeted module build, complete axiom audit, and
  owned-file lint restrictions pass
- [ ] 3 -> 4 publication-ready: out of scope unless separately requested

## Paper-proof dependencies

1. Closed in `BanachIntervalIntegralAbsoluteContinuity`: Banach-valued endpoint excursion
   `integral ||q'|| >= 2 * sup ||q|| - ||q(u0)|| - ||q(u1)||`.
2. Reused from mathlib: contractivity of orthogonal projections and bounded-linear-map calculus.
3. Reused from mathlib: fixed-operator differentiation of `P (kappa - T kappa)` almost everywhere.
4. Closed from measure-level change of variables in `AntipodalL2SpectralBounds`:
   `||f o A||_2 <= Jmin^(-1/2) ||f||_2`.
5. Closed in `TransientAntipodalConformalChannel`: reverse-triangle remainder estimate and all
   algebraic substitutions through equations (99), (101), (103), and (108).
6. Closed in `CompactSineSquaredPulse` and `RoundSphereDipoleCalibration`: global compact pulse,
   endpoint differentiability, exact total variation, signed cancellation, supremum attainment,
   and saturation.

## Full-paper proposition ledger

Claim-by-claim audit found Borsuk--Ulam already in corpus and standard calculus/algebra in mathlib.
All residual proved propositions are dependency-closed in these modules:

| Paper claims | Disposition |
|---|---|
| Peeling invariance and Schwarzian flux, (4)--(8), (12)--(21), (68)--(71) | `PeelingSchwarzianFlux` |
| Ray-map reconstruction, (9)--(11) | `RayMapPeelingReconstruction` |
| Scalar compact pulse and cancellation, (26)--(32) | `CompactSineSquaredPulse` |
| Induced antipode, Borsuk--Ulam, and Jacobian consequences, (38)--(41), (43)--(50) | `InducedAntipodalConformalGeometry`; Borsuk--Ulam reused from `GaloisForLFunctions.BorsukUlam` |
| `L2` distortion, conformal cancellation, spectral conversion, (53)--(58) | `AntipodalL2SpectralBounds` |
| Dipole and odd-harmonic calibration, (59)--(64) | `RoundSphereDipoleCalibration` |
| Extracted-channel chain rule, (67) | `ExtractedChannelChainRule` |
| Exact compact-dipole calibration, (76)--(88) | `CompactSineSquaredPulse`, `RoundSphereDipoleCalibration` |
| Endpoint excursion and robust/exact bounds, (90)--(108) | `TransientAntipodalConformalChannel` |

Equations (22)--(25), (33)--(37), (42), (51)--(52), (65)--(66), (72)--(75), and (89) are
definitions, cited background geometry/field theory, selected-model assumptions, or regime
indicators rather than new proved propositions. In particular, balanced uniformisation and the
four-dimensional remainder estimate are inputs, not paper theorems. No false closure claim is made.

## Hostile audit

- Paper's central result is conditional on channel closure, regularity, extraction, endpoint, and
  remainder assumptions. Formal theorem must quantify these exact assumptions; deleting them is
  false, while adding stronger route assumptions is forbidden.
- Balanced uniformisation existence/branch selection is background input, not proved in paper.
  Formalize only consequences actually established from a selected conformal diffeomorphism unless
  a dependency-closed uniformisation theorem is already in mathlib/corpus or is built separately.
- Four-dimensional remainder control is not supplied by paper. No theorem may claim a positive
  physical Hawking-flux bound without the explicit remainder budget.
- Spherical-harmonic statements may require substantial sphere/measure/spectral infrastructure;
  exact normalization and scalar-versus-spin-two scope must remain visible.
- Paper writes defect identity pointwise but only supplies almost-everywhere derivatives for
  absolutely continuous paths. Lean capstones require the identity almost everywhere on the
  restricted interval: mathematically correct, minimally sufficient reading.
- Change-of-variables equality is not assumed as a scalar black box. It is derived from measure
  identity `Measure.map A mu = mu.withDensity (ofReal (J ^ -1))`.

## Open core

`[CLOSED]` Reused `BanachIntervalIntegralAbsoluteContinuity` for Hilbert/Banach endpoint excursion;
reused mathlib interval-integral monotonicity, bounded-linear-map calculus, and orthogonal
projection estimates. No new axiom or derivative oracle remains.

## Log

- 2026-08-22 -- created after full primary-source read. No exact paper/title hits in formal corpus
  or pipeline. Broad generated-API search found only unrelated uses of `antipodal`, `conformal`,
  `transient`, and `Schwarzian`; claim-by-claim audit remains active.
- 2026-08-22 -- relevant failed routes read. Prior Hawking no-go forbids upgrading ideal conformal
  channel identities into complete four-dimensional thermality; present card retains explicit
  extracted-channel closure and remainder budget.
- 2026-08-22 -- completed full-paper proposition ledger. Exact residual claims formalized across
  eight theorem modules and imported by `GaloisForLFunctions.HTGeometry`.
- 2026-08-22 -- hostile audit strengthened change-of-variables input to a measure identity and
  corrected defect hypotheses from pointwise to almost everywhere, matching absolute-continuity
  regularity in the paper.
- 2026-08-22 -- targeted `lake build` passed for all eight modules. `/tmp` `#print axioms` audit
  covered all 82 public theorem declarations; every result uses only `propext`,
  `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe`
  declaration occurs in owned modules.
- 2026-08-22 -- project-wide `scripts/formal_tools.py lint` passed owned modules, then reached an
  unrelated concurrent umbrella omission, currently `HTGeometry.TensorFamilyInertia`. Owned
  modules satisfy lint restrictions and are reachable from the `HTGeometry` umbrella; unrelated
  worktree state was preserved.
