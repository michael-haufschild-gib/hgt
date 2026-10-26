# Charged boundaries are critical at a quarter; the square-root boundary law

- **ID:** acg-charged-boundary-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry README §9 topic 2, §8 "boundary laws at square-root scale"
- **Statement:** The gauge mean square of a twisted flat dilation boundary at weight `σ` is the
  escaped mass at `2σ`, finite nonzero iff `σ = 1/4`. The square-root boundary law
  `|Σ_{M<j≤N} μ(j)χ_x(j)/j| ≤ C_θ(M+1)^{−θ}` (all `θ < 1/2`) holds Haar-a.e., fails at the Liouville
  twin, and at `x = 0` is RH; a.e. every boundary of weight `σ > 1/4` decays.

## Proof
Orthogonality (P2) + P10 at weight `2σ`. Abel summation on `(M,N]` with
`j^{−s} − (j+1)^{−s}` bounds (`RHTower.DiscretePacket`), telescoping. At `0`: PNT tail
(`tendsto_sum_range_succ_moebius_div`) + harmonic-to-Mertens transfer
(`BezoutValuationIncidence.abs_sum_moebiusReal_le_of_harmonic_power`) + Littlewood criterion.
Twin: dyadic squarefree mass `≥ 1/100`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/ChargedBoundariesAreCriticalAtAQuarter.lean`:
`integral_normSq_twistedFlatBoundary`, `exists_pos_tendsto_twistedFlatBoundary_iff`,
`norm_sum_Ioc_mul_rpow_neg_le`, `ae_norm_chargedBoundary_le`, `gaugeBoundaryLaw_moebius_zero_iff`,
`not_gaugeBoundaryLaw_moebius_liouville`, `moebius_boundary_trichotomy`. Axioms standard.

## Insight
Gauge charge halves the critical weight (archimedean `1/2` → charged `1/4`). RH says the Möbius
boundary behaves at square-root scale like that of a typical point of its orbit.
