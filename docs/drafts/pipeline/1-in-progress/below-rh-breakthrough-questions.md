# Six below-RH questions

- **Stage:** 1-in-progress
- **Type:** CONJECTURES
- **Source:** [Obstacles summary §2.5](../../../reports/review-0511/obstacles-summary.md#25-breakthrough-questions-below-rh-and-quasi-rh)

## Exact targets

1. **B20:** Prove or refute `T⁻¹∫_T^{2T} log|ζ(1/2+it)| dt → 0`,
   equivalently critical-scale clustering for every positive spacing multiple.
2. **B46:** Obtain zero-freeness on `Re(2s)=1` from the actual Mayer/Lewis–Hecke
   carrier without the Euler-product inequality.
3. **B21:** Prove or refute log-free occupancy `D_win`: at most `ε(A)V`
   unit windows contain zeros of depth at least `A/log V`, with `ε(A)→0`.
4. **B7:** Prove or refute eventual full-space tilted-spline positivity at
   `c=2K(log N)^(1/8)` for one `K` above the certified size-only optimum.
5. **TH:** Decide positive definiteness of every signed section of the
   two-atom source `Θ₁+Θ₂`, for every `0<a<1/2`, retaining aperture weight.
6. **B73:** Prove or refute `Λ_X log X → 0` on a density-one set of heights.

Each answer requires its exact Lean theorem, consequences, direct module
check, transitive axiom audit, and umbrella import. Conditional receivers,
finite-rank cases, estimates and equivalences do not settle these targets.

## Established boundaries

- B20 has an eight-way equivalence and long-mollifier receivers. Their
  moment-law premises are not supplied by those theorems.
- B7 has full-space positivity for some small critical multiple. Joint
  pole payment enlarges a window-pencil range; its theorem explicitly
  does not compare that range with the full-space threshold.
- TH has positive first-atom center tails at every rank. An unequal pair
  has a signed cosine spectrum. Neither the negative cross term nor a
  failure with the aperture weight removed decides the two-atom sum.
- B73 concerns `localNewmanConstant`, not `localHeatThreshold`. The latter
  has a vanishing normalized rate in density. The comparison
  `exists_localHeatThreshold_le_localNewmanConstant` bounds the slice
  threshold from above by the Newman constant and cannot transfer that
  density result in the required direction.

## Typical-height saddle candidate for B73

For fixed `ε>0`, heat `t=ε/log X` has horizontal saddle
`Re s=1/2+ε+o(1)`. The proposed input is boundedness in measure of
`ζ′/ζ` on compact boxes strictly right of `1/2`, together with a
typical-height upper bound for the omitted Gaussian tail. Both inputs
must hold throughout the unit window and the heat interval.

The existing four-exceptional-set proof in
`ZetaLogDerivTypicalBoxDensity.lean` has an absolute constant independent
of its level `B`. Its height threshold is also independent of `B` when
`4≤B≤log T` is imposed explicitly. Substituting `ε=B/log T` into that
proof gives, for `0<R≤1/16` and `R log T≥30000`,

`meas{t∈[T,2T] : ¬ZetaLogDerivScaleData(t,R,B)}`
`≤ CT[(log T/B) exp(−R log T/120000)+1/(B²R²)] + C√T`.

For fixed `R`, levels tending to infinity slower than `√log T` would
make both the exceptional density and the local Gaussian variation
small. This is an auxiliary source bound, not a solution to B73.
The actual half-Gauss dominance and its uniformity in heat remain to be
proved; the Euler-anchored sub-Weyl theorem assumes its saddle to the
right of `Re s=1` and cannot be instantiated below that boundary.

## Proof status

All six exact targets remain unproved here. No new premise or numerical
certificate is admitted as a substitute for an unconditional proof.
