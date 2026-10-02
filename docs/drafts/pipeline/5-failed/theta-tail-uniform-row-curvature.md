# RN: normalized kernel rows have opposite discrete curvature signs

- **ID:** RN-P-7b-row
- **Stage:** 5-failed
- **Type:** FALSIFIED (uniform row-curvature mechanism); THEOREM (Lean, opposite-gap survivor)
- **Source:** RN-P-7b actual simultaneous Schur residual equations.
- **Statement:** For every positive spacing, the same actual source-normalized kernel row has a negative centered midpoint gap and a positive right-shifted midpoint gap arbitrarily far along the positive ray.

## Goal

For two earlier nodes, simultaneous vanishing of the source and
coordinate-source residuals requires both normalized kernel rows to meet
their affine extrapolations at the same new node. Uniform row convexity or
concavity would offer a pointwise exclusion. The literal source instead
has both curvature signs in every sufficiently far translated test row.
This closes that proposed exclusion mechanism; the common two-row
intersection and all-rank residual-product problems remain open.

## Gates

- [x] Source-pure, based on the literal kernel and its audited first correction.
- [x] Dependency-closed paper proof below.
- [x] Corpus search completed and returned candidate/source sections inspected;
  no applicable duplicate found. Compiler/semantic coverage remains partial.
- [x] Lean leaf, targeted build, umbrella wiring and axiom audit.
- [x] Final direct leaf audit passed with exit 0 and no output.

## Paper proof [PROVED HERE]

Let `L(x,y)=H(x,y)/(k(x)k(y))`, where `H` is the actual first-moment kernel,
and let `E(r)=exp(-2r)`. The corpus's exact first correction gives

    L(x+r,y+r)/E(r) - (2r+x+y)/(2π(exp(2x)+exp(2y))) → 0.

Indeed the difference divided by `r E(r)` tends to
`7/(2π²(exp(2x)+exp(2y))²)`, and `r E(r)→0`.

Fix `h>0` and put `v=exp(2h)>1`. For the centered row gap

    D₀(r)=L(r,r-h)+L(r,r+h)-2L(r,r),

the terms linear in `r` cancel exactly, because
`1/(1+v)+1/(1+1/v)=1`. The remaining clock term gives

    D₀(r)/E(r) → -h(v-1)/(2π(1+v)) < 0.

For the right-shifted midpoint gap

    D₁(r)=L(r,r)+L(r,r+2h)-2L(r,r+h),

the leading Cauchy limit gives

    D₁(r)/(r E(r)) → (v-1)³/(2π(1+v)(1+v²)) > 0.

The identity in the last line is the exact simplification of
`(1/2+1/(1+v²)-2/(1+v))/π`. Thus for every sufficiently large `r>h`,
both gaps have the stated strict signs. Convexity of the row on
`[r-h,r+2h]` would force `D₀≥0`; concavity would force `D₁≤0`.
Neither holds.

## No-go closure

- **Killing mechanism:** Actual far-row midpoint gaps have both signs, so
  uniform convexity and uniform concavity are both false even on positive tails.
- **Strongest positive survivor:** Exact opposite-sign asymptotic laws at
  every fixed positive spacing, and eventual nonconvexity/nonconcavity of
  the same complete-source row on the same four-node interval.
- **New insight:** The actual residual equations require coupled comparison
  of two rows. Their pointwise curvature cannot be replaced by a uniform sign.
- **Status:** Formalized in `ThetaTailNormalizedRowCurvature.lean`, namespace
  `RHTower.ThetaTailRow`: `centeredGap_limit`, `rightGap_limit`,
  `opposite_gaps_eventually`, `row_neither_convex_nor_concave_eventually`.
  Targeted `lake --old build` passed. All four public theorems have only
  `propext`, `Classical.choice`, and `Quot.sound` in the axiom audit.
  The leaf is wired in `RHTower.lean`; final direct leaf audit passed.
  No conclusion about RH or the actual all-rank Schur-product conjecture.

## Verification scope

`lake --old build GaloisForLFunctions.RHTower.ThetaTailNormalizedRowCurvature`
and final `lake env lean GaloisForLFunctions/RHTower/ThetaTailNormalizedRowCurvature.lean`
passed. No umbrella build, numerical experiment, new axiom, or heartbeat
increase. Lint found no new-leaf error but failed on 12 unrelated unwired
modules listed in the RN working log. The positive replacement under study
is ordered row decrease, with its paper proof in
`../2-fully-proven/rn-ordered-normalized-row-monotonicity.md`.

## Log

- 2026-10-02 — Derived from `ThetaTailCauchyFirstCorrection.kernel_first_correction_limit`
  and `ThetaTailCauchy.kernel_normalized_limit`; deep search covered 64,359
  indexed files, mostly source-only/pending compiler metadata, semantic
  coverage unmeasured. Lean implementation built, axiom-audited and directly
  checked in `ThetaTailNormalizedRowCurvature.lean`.
