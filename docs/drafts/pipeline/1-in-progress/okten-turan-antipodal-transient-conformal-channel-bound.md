# Okten--Turan transient antipodal conformal-channel bound

- **ID:** `okten-turan-antipodal-transient-conformal-channel-bound`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / `[LITERATURE] [NOVELTY UNVERIFIED]`
- **Source:** M. B. Okten and A. S. Turan, *Antipodal constraints on transient Hawking radiation in a conformal channel*, arXiv:2608.19244v1, equations (90)--(108)
- **Statement:** A restored Hilbert-valued peeling path whose centred antipodal mismatch reaches squared norm `Mmax` forces integrated conformal-channel defect at least `cCFT/(24*pi) * 2/(1 + Jmin^(-1/2)) * (sqrt Mmax - epsilonEnd) - remainderBudget`.

## Goal

Formalize exact robust lower bound, exact-endpoint specialization, positive-threshold corollary,
conformal forcing-scale form, time-averaged form, and equality calibration after independently
closing every paper-proof dependency. Add no hypotheses beyond paper's mathematical assumptions.

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
- [ ] 1 -> 2 fully-proven: independent dependency-closed paper proof survives hostile audit
- [ ] 2 -> 3 formalized: exact Lean declarations, targeted module build, axiom audit, and lint pass
- [ ] 3 -> 4 publication-ready: out of scope unless separately requested

## Paper-proof dependencies

1. Banach/Hilbert absolutely-continuous endpoint-excursion estimate:
   `integral ||q'|| >= 2 * sup ||q|| - ||q(u0)|| - ||q(u1)||`.
2. Contractivity of mean-zero orthogonal projection.
3. Fixed-operator differentiation: `(P (kappa - T kappa))' = P (kappa' - T kappa')` almost
   everywhere.
4. Antipodal composition bound `||f o A||_2 <= Jmin^(-1/2) ||f||_2` from change of variables.
5. Reverse triangle inequality for conformal defect plus remainder.
6. Algebraic substitutions producing equations (99), (101), (103), and (108).

## Full-paper proposition ledger

Each item must be classified as `[CORPUS]`, mathlib, or residual before implementation. Residual
items get separate one-claim cards if they are not merely definitions or direct rewrites.

- peeling invariance under positive channelwise affine reparametrization, equations (6)--(8)
- reconstruction of ray-map derivative and ray map from peeling field, equations (9)--(10)
- Schwarzian--peeling identity and conformal defect, equations (15)--(21), (68)--(71)
- compact scalar pulse absolute and signed defect integrals, equations (26)--(32)
- induced antipode involution and Borsuk--Ulam coincidence, equations (38)--(41)
- conformal factor, Jacobian reciprocity, and extremal reciprocity, equations (42)--(47)
- centred mismatch mean-zero law and functional, equations (48)--(50)
- composition `L2` distortion, conformal Dirichlet invariance, and spectral mismatch bound,
  equations (53)--(58)
- round-sphere dipole and odd-harmonic calibrations, equations (59)--(64)
- extracted-channel chain rule and conformal defect decomposition, equations (65)--(74)
- exact round-sphere compact-dipole calibration and saturation, equations (76)--(89)
- endpoint-excursion, exact and robust integrated bounds, positivity threshold, forcing-scale and
  time-averaged forms, equations (90)--(108)

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

## Open core

`[OPEN CORE]` Determine minimal existing mathlib/corpus interface for the Hilbert-valued
absolutely-continuous endpoint-excursion inequality. This controls whether capstone can reuse
Bochner/interval-integral infrastructure or needs a new reusable analytic layer.

## Log

- 2026-08-22 -- created after full primary-source read. No exact paper/title hits in formal corpus
  or pipeline. Broad generated-API search found only unrelated uses of `antipodal`, `conformal`,
  `transient`, and `Schwarzian`; claim-by-claim audit remains active.
- 2026-08-22 -- relevant failed routes read. Prior Hawking no-go forbids upgrading ideal conformal
  channel identities into complete four-dimensional thermality; present card retains explicit
  extracted-channel closure and remainder budget.
