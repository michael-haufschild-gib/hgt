# Alternating signature of the unique Gamma gap correction — Lean certificate

- **Paper card:** `stc-hyperbolic-gap-krein-signature.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia` (general
  exponential kernels), `GaloisForLFunctions.RHTower.STCHyperbolicGapKreinSignature` (gap-sinc
  packets); inputs `HermitianInertia`, `HaynsworthInertia`, `Zeta5AndreiefTransfer`,
  `NavierStokesRealExponentialVandermonde`, `STCFlatGapSpectralBand`
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` of all 37
  theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`K_N = gapSincPacketMatrix g x`; inertia = `hermPosIndex`/`hermNegIndex`/`hermNullIndex` of the
complexified matrix (equivalently eigenvalue counts).

| Card item | Lean theorem |
|-|-|
| (1) `sign det K_N = (-1)^{N(N-1)/2}`, inertia `(⌈N/2⌉, ⌊N/2⌋)`, nonsingular | `gapSincPacket_inertia`, `gapSincPacket_det_ne_zero` |
| (1) as eigenvalue counts | `gapSincPacket_eigenvalue_counts` |
| prime packets; indices unbounded | `gapSincPrimePacket_inertia`, `gapSincPrimeKernel_negIndex_unbounded` |
| no invertible congruence makes `K_N` PSD (`N ≥ 2`) | `gapSincPacket_not_congruent_posSemidef` |
| two-prime packet: one negative, one positive direction | `hyperbolicGapSinc_pair_indefinite` (existing) and `gapSincPacket_inertia` at `N = 2` |
| (2) `K_g(x,y) = (1/a)∫ e^{ux}e^{-uy} du` | `gapSincPacketMatrix_eq_expKernel`, `band_integral_exp` |
| (3) Andréief identity for the kernel | `det_expKernelMatrix_eq_integral` (from `zeta5_andreief`) |
| ordered exponents: `det[e^{u_j x_i}] > 0` | `det_realExponentialVandermonde_pos` |
| reversed exponents: sign `(-1)^{N(N-1)/2}`; `Σ_i #{j>i} = N(N-1)/2` | `det_realExponentialVandermonde_anti_sign`, `det_realExponentialVandermonde_ne_zero_of_anti`, `sum_card_Ioi_fin` |
| integrand sign, strict off coincidence hyperplanes | `andreief_exp_integrand_sign` |
| strict determinant sign (positive product mass of distinct tuples) | `expKernelMatrix_det_sign` |
| leading-minor pivots and Sylvester inertia (`LDLᵀ` step) | `hermNegIndex_succ_leading`, `inertia_of_alternating_leading_minors`, `hermPosIndex_submatrix_equiv`, `hermNegIndex_submatrix_equiv` |
| general symmetric finite measure on a compact interval, ≥ N support points | `expKernelMatrix_isSymm`, `expKernelMatrix_det_sign`, `expKernelMatrix_inertia` |
| band measure is symmetric with infinite support | `flatGapBandMeasure_isNegInvariant`, `flatGapBand_support` |
| Fourier contrast: imaginary frequencies give a PSD Gram kernel | `fourierKernelMatrix_posSemidef` |
| no finite-negative-index (Pontryagin) carrier of all packet forms | `gapSincPrimeKernel_no_pontryagin_carrier`, `no_finite_negIndex_carrier` |
| finite-channel repair: rank-`r` correction leaves `≥ ⌊N/2⌋ - r` negative directions | `hermNegIndex_le_add_rank`, `gapSincPacket_negIndex_add_ge`, `gapSincPacket_negIndex_add_real_ge`, `rank_map_ofReal_le` |
| no uniformly bounded-rank repair makes all packets PSD | `gapSincPacket_no_finite_rank_repair` |
