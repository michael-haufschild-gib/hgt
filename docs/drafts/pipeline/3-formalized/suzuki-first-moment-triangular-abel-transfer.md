# Suzuki first-moment to triangular Abel transfer

- **ID:** CCM-FU-FIRST-MOMENT-ABEL
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` routes CCM-FU / G-CE / PPM
- **Statement:** Linear growth of exact event-label-weighted Suzuki curvature prefixes uniformly bounds the CCM-FU third-grade triangular transform; bounded central unit-Riesz barycenters therefore imply RH.

## Exact RH chain

`|suzukiCheckpointWeightedSignedCurvaturePrefix N| = O(N)`
→ reciprocal-log Abel transfer at powers two and three
→ `CCMFUSuzukiTriangularCurvatureTransformBound`
→ `CCMFUSuzukiCanonicalCheckpointAffineTailBound`
→ RH.

The existing source identity

`normalized curvature first moment = central unit-Riesz barycenter - vanishing archimedean renormalization`

adds a second entrance: a uniform bound on
`unitRieszCompletedCoherentBarycenter (N+2) 0` implies the first premise and hence RH.

## Corpus audit

- `[CORPUS]` `suzukiCheckpointWeightedSignedCurvaturePrefix_eq_terminalSlope_sub_cesaro`
  identifies the exact event-label first moment with the terminal affine slope minus its Cesaro
  history.
- `[CORPUS]` `normalizedSignedCurvatureFirstMoment_eq_unitRieszCenter_sub_arch` lands the same
  moment in the central unit-Riesz incoming source.
- `[CORPUS]` `abs_suzukiCheckpointWeightedArchRenormalization_le` bounds the source-free error by
  `8 sqrt(N+2)+5`, hence by a linear function.
- `[CORPUS]` `sum_mul_weight_eq` is exact finite Abel summation.
- `[CORPUS]` `burnolSummable_shifted_one_div_mul_log_sq` and
  `summable_one_div_mul_log_pow_succ` establish the critical reciprocal-log summability threshold.
- `[CORPUS]` `ccmFUSuzukiCanonicalCheckpointAffineTailBound_iff_triangularCurvatureTransformBound`
  and `riemannHypothesis_of_suzukiCheckpointTriangularCurvatureTransformBound` close the RH chain.
- `[CORPUS]` searches found no theorem transferring first-moment linear growth to the triangular
  transform or making central unit-Riesz barycenter boundedness an RH-sufficient source premise.

## Literature audit

Suzuki's screw-function papers arXiv:2206.03682 and 2209.04658, and the 2026 Weil-form synthesis
arXiv:2606.09096, give continuous screw/Weil equivalences but no event-label first-moment Abel
transfer. The August 2026 checkpoint papers Zenodo 21859280, 21979513, and 22076088 isolate exact
Chebyshev balances and recovery witnesses but do not contain the CCM-FU triangular kernel or this
unit-Riesz/first-moment criterion. Priority remains provisional pending expert review.

## Theorem C-FM-ABEL

Assume a constant `C >= 0` satisfies, for every `N >= 1`,

`|P_N| <= C (N+2)`,

where

`P_N = sum_{3 <= k < N+2} k * suzukiCheckpointSignedCurvatureCell (k-1)`.

Then the family

`T(H) = sum_{2 <= j < floor(exp H)} Delta_j *
  32 / log(j+1)^3 * (1 - log(j+1)/H)`

is uniformly bounded for `H >= 2`.

## Hostile audit

Verdict: `SURVIVES`.

- The argument never separates positive and negative Jordan masses; it uses only signed prefix
  cancellation.
- Writing `b_k = k Delta_(k-1)` splits the reporter exactly into the two Abel weights
  `1/(k log(k)^3)` and `1/(H k log(k)^2)`.
- Finite Abel summation uses prefix bounds on `sum b_k`, not absolute bounds on cells.
- The power-two tail is the sharp convergent threshold `sum 1/(k log(k)^2)`; the power-three tail
  is smaller. No hidden divergent harmonic majorant is used.
- The first-moment hypothesis is not claimed unconditional. False-RH escape remains possible only
  through failure of this one source-specific linear-growth estimate.

## Dependency-closed paper proof

Put `b_k = k Delta_(k-1)` for `k >= 3` and
`B_m = sum_{3 <= k <= m} b_k`. The premise gives `|B_m| <= C(m+1)` after the harmless index shift.
For integer `p >= 2`, set

`w_p(k) = 1 / (k log(k)^p)`.

For every finite endpoint `M`, Abel summation gives

`sum_{k=3}^M b_k w_p(k)
 = B_M w_p(M+1) - sum_{k=3}^M B_k (w_p(k+1)-w_p(k))`,

with an equivalent boundary indexing if the terminal zero term is omitted. Since `w_p` is
positive decreasing,

`|sum b_k w_p(k)|
 <= C (M+1) w_p(M+1)
    + C sum_{k=3}^M (k+1)(w_p(k)-w_p(k+1))`.

Write `u_p(k)=1/log(k)^p`, so `w_p(k)=u_p(k)/k`. Direct algebra gives

`(k+1)(w_p(k)-w_p(k+1))
 = w_p(k) + u_p(k)-u_p(k+1)`.

Hence the second term is bounded by

`C (sum_{k=3}^M w_p(k) + u_p(3))`,

while the boundary term is at most `C u_p(3)`. For `p>=2`, `log k>=1` on `k>=3`, so
`0 <= w_p(k) <= 1/(k log(k)^2)`. The latter series converges. Thus there is a constant `K_p`,
independent of `M`, with

`|sum_{k=3}^M b_k/(k log(k)^p)| <= K_p`.

For `H>=2`, let `M=floor(exp H)`. Reindexing `k=j+1` and expanding the exact reporter weight gives

`T(H)
 = 32 sum_{k=3}^M b_k/(k log(k)^3)
   - (32/H) sum_{k=3}^M b_k/(k log(k)^2)`.

Since `1/H <= 1/2`, the two uniform Abel bounds yield one uniform bound for `T(H)`. The existing
triangular-transform endpoint then proves RH.

Finally, if the central unit-Riesz barycenter is uniformly bounded, the exact normalized landing
and `|arch_N| <= 8 sqrt(N+2)+5` give

`|P_N|/(N+2) <= C_0 + 8/sqrt(N+2) + 5/(N+2)`,

which is uniformly bounded for `N>=1`. This supplies the first-moment premise and closes the same
RH chain.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, explicit RH chain, corpus/literature audit, hostile proof
- [x] 1 → 2 fully-proven: Lean-independent proof checked against exact endpoint indices
- [x] 2 → 3 formalized: closed Lean theorem, umbrella import, targeted build and axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and external expert novelty review

## Lean realization

Module:
`GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstMomentTriangularAbelTransfer`

Principal closed theorems:

- `HTGeometry.abs_sum_mul_weight_le_of_linear_partialSum`: generic signed Abel transfer from
  linear prefix growth through a summable reciprocal-scale reporter.
- `suzukiCheckpointTriangularCurvatureTransform_eq_reciprocalLogSums`: exact decomposition into
  cubic and quadratic reciprocal-log channels.
- `ccmFUSuzukiTriangularCurvatureTransformBound_of_weightedFirstMomentLinearBound`: discharges the
  full CCM-FU triangular-transform premise from one exact first-moment bound.
- `weightedFirstMomentLinearBound_of_unitRieszCentralBarycenterNaturalBound`: closes the source
  landing from central unit-Riesz natural-aperture boundedness.
- `riemannHypothesis_of_suzukiWeightedCurvatureFirstMomentLinearBound` and
  `riemannHypothesis_of_unitRieszCentralBarycenterNaturalBound`: record both complete RH chains.

Direct `lake env lean` and targeted
`lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiFirstMomentTriangularAbelTransfer` pass. Axiom audit
for generic Abel transfer, exact decomposition, both premise transfers, and both RH capstones
reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is imported by RHTower
umbrella. Global formal lint reports only unrelated concurrent umbrella-reachability failures; no
forbidden declaration occurs in this module.

## Log

- 2026-08-31 — conjecture frozen after corpus-driven Abel decomposition and hostile threshold audit.
- 2026-08-31 — paper proof and Lean formalization closed; promoted to `3-formalized`.
