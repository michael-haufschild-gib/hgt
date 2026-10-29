# Atomic touching is not the density-matched paired-lattice boundary

- **Stage:** 5-failed
- **Rejected inference:** Under one physical height and prime-cutoff convention, atomic
  touching `X=T` coincides with the paired SRT lattice's sharp aperture boundary.
- **Obstruction:** Paired lattice density is `L/π`. Matching `log T/(2π)` gives
  `L=log T/2`, so its aperture `L/2` corresponds to prime cutoff `X=√T`.
  At `X=T>1`, the off-line paired lattice already has a negative test.
- **Positive survivor:** Exact agreement of both position and depth mimics holds iff `X²≤T`;
  a negative off-line witness exists iff `X²>T`.
- **Paper status:** Complete, by the corpus's sharp Nyquist criterion and the exact
  calibration `a=log X/2`, `L=log T/2`.
- **Lean status:** Direct check and axiom audits passed in
  `SquareRootThreshold/DensityMatchedLengthHeightBoundary.lean`; umbrella wired.

Declarations: `densityMatched_lattices_agree_iff`, `densityMatched_negative_test_iff`,
`densityMatched_negative_at_atomic_touching`.

This classifies the stated lattice models. It neither proves an estimate for actual zeta zeros
nor places the negative witness inside any fixed-profile atomic family.
