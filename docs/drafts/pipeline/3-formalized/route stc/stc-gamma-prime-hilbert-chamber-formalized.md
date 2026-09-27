# Sharp Hilbert chamber of the literal two-channel Gamma kernel — Lean certificate

- **Paper card:** `stc-gamma-prime-hilbert-chamber.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCGammaPrimeHilbertChamber`,
  `GaloisForLFunctions.RHTower.STCGammaPrimeWallScaling`; shared `GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators`
  (column obstruction, rank-one matrices, weak-null criterion), `HilbertSchmidtMatrix`/`HilbertSchmidtCompact`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`b_u = stcDepthZeroAmplitude u`, `Q_{u,g} = stcGammaKernel u g`, `C_{u,g} = stcStokesSourceKernel u g`.

| Card item | Lean theorem |
|-|-|
| (1) `b_u² = (log p)² p^{-1-u}`, `b_u p^{a/2} = b_{u-a}` | `stcDepthZeroAmplitude_sq`, `stcDepthZeroAmplitude_shift` |
| (2) two-channel decomposition; `g = 0` gives `Q = 0` | `stcGammaKernel_two_channel_real`, `stcGammaKernel_zero_grade` |
| chamber: (1)⇔(2)⇔(3)⇔(4) | `stcGammaChannels_summable_iff`, `summable_sq_col_stcGammaKernel_iff`, `exists_hasLpMatrix_stcGammaKernel_iff` |
| interior: rank ≤ 2, compact, zero Calkin class, unique, transport compact | `stcGammaKernel_chamber_compact` |
| (4) wall form `Q_{a+v,g} = sign(g)(P_{x_v} - P_{y_v})/2` | `hasLpMatrix_stcGammaWallOp` |
| `‖x_v‖ → ∞`, `‖y_v‖ ≤ ‖b_{2a}‖` | `tendsto_norm_stcBoundaryVec`, `norm_stcBoundaryVec_shift_le` |
| (5) `2‖Q‖/‖x_v‖² → 1` | `tendsto_norm_stcGammaWallOp_ratio` |
| `e_v ⇀ 0`; `P_{e_v} → 0` strongly with norm one | `tendsto_inner_stcBoundaryUnit`, `stcBoundaryUnit_projection_strong_zero` |
| (6) `2Q/‖x_v‖² → 0` strongly, norm → 1 | `stcGammaWallOp_rescaled_limits` |
| every bounded strong limit of `c_v Q` is `0` (uniform boundedness) | `stcGammaWall_scalar_strong_limit_eq_zero` |
| `Q` itself has no bounded strong limit | `not_exists_strong_limit_stcGammaWallOp` |
| `C = -2 Q G`; Stokes wall: bounded ⇔ `u > 2|g|`; non-summable columns at `u ≤ 2|g|` | `stcStokesSourceKernel_eq`, `exists_hasLpMatrix_stcStokesSourceKernel_iff`, `not_summable_sq_col_stcStokesSourceKernel` |
| Stokes chamber: rank ≤ 4, compact, zero Calkin class | `stcStokesSourceKernel_chamber` |
| ordered kernel: same threshold; Hilbert--Schmidt and compact in the chamber | `exists_hasLpMatrix_stcOrderedStokesSourceKernel_iff`, `stcOrderedStokesSourceKernel_chamber` |
| ordered packets have unbounded rank | `exists_prime_packet_orderedStokesSource_rank` |
| height-weighted `(h_p - h_q) Q_{u,g}`: finite rank, compact | `stcHeightWeightedGammaKernel_chamber` |
