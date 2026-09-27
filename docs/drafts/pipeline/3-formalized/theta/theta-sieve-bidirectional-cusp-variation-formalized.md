# Prime sieving forces bidirectional signed variation at the theta cusp — Lean certificate

- **Paper card:** `theta-sieve-bidirectional-cusp-variation.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaSieveBidirectionalCuspVariation`
  (on top of `ThetaPrimeDeletionMellin`, `ThetaPrimeDeletionSpectralEscape`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for every listed theorem.

`δ_j = thetaSieveResidual (S j)`, `d_w = thetaEscapedMoment w`, `G = thetaAtomGammaFactor`,
`P_j(R) = thetaCuspPositiveVariation (S j) R`, `N_j(R) = thetaCuspNegativeVariation (S j) R`;
`S` is any `PrimeExhaustion`. A `liminf ≥ L` statement is formalized as
"for every `ε > 0`, eventually `≥ L - ε`".

| Card item | Lean theorem |
|-|-|
| `d_w > 0` | `thetaEscapedMoment_pos` |
| (1) `∫_{x<-R} e^{wx} δ_j → d_w` (all `-1/2 < w ≤ 1/2`, all `R`) | `PrimeExhaustion.tendsto_setIntegral_Iio_exp_mul_thetaSieveResidual` |
| no escaped weighted mass on `[-R,∞)` | `PrimeExhaustion.tendsto_setIntegral_Ici_exp_mul_thetaSieveResidual` |
| (2) `liminf (P+N) ≥ d_w e^{wR}` | `PrimeExhaustion.eventually_variation_add_ge` (via `abs_setIntegral_Iio_exp_mul_le`) |
| (2) `P - N → d_0` | `PrimeExhaustion.tendsto_variation_sub` |
| (3) `liminf min(P,N) ≥ (d_w e^{wR} - d_0)/2` | `PrimeExhaustion.eventually_variation_min_ge` |
| both variations of `δ_j` diverge | `PrimeExhaustion.tendsto_residual_variations` |
| both variations of `k_{S_j}` diverge; signed mass `→ 0` | `PrimeExhaustion.tendsto_thetaPrimeDeletion_variations`; `PrimeExhaustion.tendsto_integral_exp_mul_thetaPrimeDeletion` at `w = 0` |
| (4) `c = min_{[0,1/2]} G > 0` exists | `exists_thetaAtomGammaFactor_lower_bound` |
| (4) critical-scale bounds at `w_R = 1/2 - 1/R` | `PrimeExhaustion.eventually_variation_critical_scale` |
| `c e^{R/2}/(eR) → ∞` | `tendsto_critical_variation_scale` |
