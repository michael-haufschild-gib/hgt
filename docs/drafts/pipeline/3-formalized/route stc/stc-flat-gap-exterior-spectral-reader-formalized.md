# Exterior spectral reader forced by the flat Gamma gap — Lean certificate

- **Paper card:** `stc-flat-gap-exterior-spectral-reader.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCFlatGapSpectralBand`,
  `GaloisForLFunctions.RHTower.STCFlatGapMeasureReaderNoGo`,
  `GaloisForLFunctions.RHTower.STCFlatGapPrimeLogReaderNoGo`; uniqueness input
  `eq_zero_of_exponentialPower_of_primeLog_zeros` (`PrimeLogFiniteOrderUniqueness`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`H_a = FlatGapBand a = L²(flatGapBandMeasure a)`, `f_x = flatGapFeature a x`,
`J = flatGapReflection a`, `v_p = flatGapSeamVector a τ p`, `S(s) = hyperbolicGapSinc s`.

| Card item | Lean theorem |
|-|-|
| `(1/a)∫_{-a/2}^{a/2} e^{us} du = S(as/2)` | `band_integral_exp` |
| (1) `⟪f_x,f_y⟫ = S(a(x+y)/2)`, `‖f_x‖² = S(ax)` | `inner_flatGapFeature`, `norm_sq_flatGapFeature` |
| (1) `H_g` positive semidefinite | `flatGapGram_posSemidef` |
| (1) `J` isometric reflection, `J f_y = f_{-y}` | `measurePreserving_neg_flatGapBand`, `flatGapReflection`, `flatGapReflection_feature` |
| (1) `K_g(x,y) = ⟪f_x, J f_y⟫`, `H_g(x,y) = K_g(x,-y)` | `flatGapKernel_eq_reflected_inner`, `flatGapGram_eq_kernel_neg` |
| (2) Krein polarization | `flatGapKernel_krein` |
| (3) `u_p(ρ) = -2 p^{-1/2+iτ} x_p sinh(g x_p)` | `orbitwiseNatPrimeSeamCharge_band` |
| (4) `‖v_p‖² = p^{-1} S(a x_p)`; ratio formula | `norm_sq_flatGapSeamVector`, `norm_seam_div_norm_vector` |
| (5) ratio `≥ √(a/2)(log p)^{3/2} p^{a/2}`; divergence along primes | `flatGapSeamRatio_ge`, `eventually_flatGapSeamRatio_ge` |
| norm cost of a bounded matching functional | `flatGapSeamRatio_le_opNorm` |
| no bounded functional; nonclosability on any domain containing all `v_p` | `no_bounded_flatGap_seam_reader`, `flatGap_seam_reader_not_closable` |
| (6) `x sinh(gx) = sign(g)[f'_x(a) - f'_x(-a)]/2` | `seam_derivative_band_edge` |
| entire Laplace transform, total-variation bound on `iℝ` | `differentiable_spectralLaplace`, `norm_spectralLaplace_le`, `norm_spectralLaplace_imag_le` |
| abstract finite-order no-go | `no_finiteOrder_reader_gradeCharge`, `stc_no_finiteOrder_boundedImaginary_gradeCurrent` |
| (7) compactly supported finite complex measure (density form `w dμ`) | `no_compact_spectral_measure_gradeCharge` |
| (7) Hilbert corollary via Riesz, any finite compactly carried `μ` | `no_bounded_compact_reader_gradeCharge` |
| (8) Gaussian features: `‖E_z‖ = exp(σ²(Re z)²)`; readout bounds; entire | `memLp_gaussian_feature`, `norm_gaussianFeature`, `norm_gaussianReadout_le`, `norm_gaussianReadout_imag_le`, `differentiable_gaussianReadout` |
| (8) no bounded Gaussian reader | `no_bounded_gaussian_reader_gradeCharge` |
| transport current: `cosh(gx) = ∫ e^{ux} dm_g`, `d/dg ∫φ dm_g = [φ'(g) - φ'(-g)]/2`, exponential case | `cosh_eq_atom_average`, `transport_current`, `transport_current_exponential` |
