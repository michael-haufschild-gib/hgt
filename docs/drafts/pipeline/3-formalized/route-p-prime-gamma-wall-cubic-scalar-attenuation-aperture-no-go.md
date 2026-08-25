# Prime/Gamma wall cubic scalar-attenuation aperture no-go

- **ID:** route-p-prime-gamma-wall-cubic-scalar-attenuation-aperture-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED]` `[LEAN-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[CONORMAL]` `[NO-GO]` `[NOVELTY-UNVERIFIED]`
- **Source:** primitive Burnol cubic conormals, strict-right Xi conormals, and radial aperture
  translation characters
- **Statement:** No nonzero constant scalar attenuation can make an aperture-translation
  intertwiner carry a primitive Euler conormal to a strict-right Xi conormal.

## Exact source statement

For every strict-right Xi zero copy `q`, primitive prime/depth label `pe`, and real vertical clock
`kappa`, there do not exist `alpha : C` and a complex-linear map

`T : (R -> C) ->_C (R -> C)`

such that:

1. `alpha != 0`;
2. `T` commutes with every radial aperture translation;
3. `T` sends the primitive Burnol cubic conormal to `alpha` times the Xi conormal at `q`.

This includes arbitrarily small `alpha`, hence excludes constant scalar repair of the factor-`2000`
raw-magnitude overshoot.

## Closed paper proof

Assume such `alpha` and `T`. Define `T' = alpha^(-1) T`. Scalar multiplication preserves complex
linearity and commutation with every radial translation. Since `alpha != 0`, the landing law becomes
the unscaled identity

`T'(primitive conormal) = strict-right Xi conormal`.

Existing aperture-character rigidity rules this out: primitive centered real rate is at least
`log 2 > 1/2`, while a strict-right Xi centered rate lies below `1/2`; their squared translation
characters cannot be intertwined. Contradiction.

The surviving nonstationary law is exact. If a linear map sends mode `z` to `alpha` times mode `w`,
its aperture covariance defect at radius zero is

`alpha * 2c exp(-wc) (exp(-zc) - exp(-wc))`.

Thus attenuation scales boundary work but cannot erase it unless `alpha=0` or rates agree.

## Hostile audit

- `alpha` is arbitrary complex and may have arbitrarily small norm; no positivity or fitted
  magnitude is assumed.
- `T` need not be continuous, bounded, local, or represented by a kernel.
- Obstruction uses exact radial translation character, not numerical rate estimates beyond the
  proved disjoint half-plane bounds.
- Zero scalar is excluded because it erases target conormal and is not a landing.
- Result does not rule out nonstationary polar--Gamma transport; it proves such boundary work is
  mandatory.

## No-go closure

- **Exact killing theorem/mechanism:** rescaling by `alpha^(-1)` reduces every nonzero scalar landing
  to already impossible aperture-covariant identity landing.
- **Strongest positive survivor:** exact scaled covariance-defect law
  `alpha * 2c exp(-wc)(exp(-zc)-exp(-wc))`; viable contraction must be aperture-dependent and retain
  this polar--Gamma boundary work.
- **New insight:** factor-`2000` magnitude aperture cannot be supplied by constant scalar damping,
  stationary convolution, multiplier functional calculus, or any other translation intertwiner.
- **Status:** dependency-closed paper proof and exact unconditional Lean theorems. Corpus and
  primary-source audit found no exact scalar-attenuated primitive-to-Xi aperture theorem.

## Corpus and literature audit

- Corpus excludes unscaled aperture intertwiners and gives the unscaled covariance-defect law, but
  contains no arbitrary-nonzero-scalar classification or scaled defect formula.
- Primary-source searches found general irregular Riemann--Hilbert solvability and Stokes connection
  maps, but no Riemann-Xi/Euler conormal scalar-attenuation theorem.
- Relevant background: Bolibruch--Malek--Mitschi, arXiv:math/0410483; Xu,
  arXiv:1507.07149 and arXiv:1701.08113.
- Absence is audit inference, not priority claim.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure claim and attack frozen
- [x] 1 -> 2 fully-proven: dependency-closed proof and hostile audit above
- [x] 2 -> 3 formalized: unconditional Lean theorem and new-declaration axiom audit
- [ ] 3 -> 4 publication-ready: standalone paper and independent novelty review

## Lean realization

- `xiWardCubicApertureCovarianceDefect_scaled_mode_landing_apply_zero`
- `not_exists_nonzero_scalar_apertureIntertwiner_primitive_to_strictRight`
- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicScalarAttenuationApertureNoGo.lean`
- Direct Lean check and direct `.olean` emission passed; no Lake target or umbrella build ran.
- Axiom audit of both new public theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Log

- 2026-08-25 — scalar normalization proof and exact scaled covariance defect derived.
- 2026-08-25 — corpus and primary-literature audits completed; promoted through Stage 1 to Stage 2.
- 2026-08-25 — exact Lean theorems, direct module check, and new-declaration axiom audit passed;
  promoted to Stage 3.
