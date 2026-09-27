# Prime deletion preserves the Xi divisor while its boundary spectrum escapes — Lean certificate

- **Paper card:** `theta-prime-deletion-spectral-escape.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin` (shared deletion layer),
  `GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build` of both modules; `#print axioms` on every listed theorem
  gives only `propext`, `Classical.choice`, `Quot.sound`. No hypotheses beyond the card's own
  quantifiers.

## Certified declarations

| Card item | Lean theorem |
|-|-|
| atom Mellin law `∫e^{wx}a_n = n^{-(w+1/2)}G(w)`, `Re w>-5/2` | `integral_cexp_mul_thetaCuspSourceTerm` |
| (1) coprime atom expansion of `k_S` | `thetaPrimeDeletion_thetaCuspFullSource_eq_tsum` |
| (1) `L_w k_S = XiC(iw)∏(1-p^{-1/2-w})`, all complex `w` | `integral_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource` |
| factors zero-free; same zero divisor with multiplicity | `one_sub_natCast_cpow_ne_zero`, `analyticOrderAt_thetaPrimeDeletion_laplace` |
| positive atom sum on `x≥0`, `h ≤ k_S ≤ k` | `thetaCuspSourceTerm_one_le_thetaPrimeDeletion`, `thetaPrimeDeletion_pos_of_nonneg` |
| `k_{S_j} → h` uniformly on compacts | `PrimeExhaustion.tendstoUniformlyOn_thetaPrimeDeletion` |
| (2) seed transform, no zero in the strip | `integral_cexp_mul_thetaSeedAtom`, `thetaAtomMellinFactor_ne_zero`, `thetaPrimeDeletion_keeps_zero_seed_loses_it` |
| (3) `L_w k_{S_j} → 0`, `L_w h < 0` (`-1/2<w<1/2`) | `PrimeExhaustion.tendsto_integral_exp_mul_thetaPrimeDeletion`, `integral_exp_mul_thetaSeedAtom_neg` |
| positive ordinary mass at each stage | `integral_thetaPrimeDeletion_pos` |
| residual: no mass on `[-R,∞)`, total `G(0)/2` | `PrimeExhaustion.tendsto_setIntegral_Ici_thetaPrimeDeletion_sub_seed`, `PrimeExhaustion.tendsto_integral_thetaPrimeDeletion_sub_seed` |
| (4) `L_{1/2}k_S = ½∏(1-1/p) → 0 = L_{1/2}h` | `integral_exp_half_mul_thetaPrimeDeletion`, `integral_exp_half_mul_thetaSeedAtom` (+ limit theorem at `w=1/2`) |
| (5)–(6) reflected deletion: even, transform, zero-free, both charges zero | `thetaSymmetricPrimeDeletion_eq_comp`, `thetaSymmetricPrimeDeletion_neg`, `integral_cexp_mul_thetaSymmetricPrimeDeletion`, `thetaSymmetricPrimeDeletion_factor_ne_zero`, `thetaSymmetricPrimeDeletion_charges_zero` |
| positive mass `(1-p^{-1/2})²∫k` and forced sign change | `integral_thetaSymmetricPrimeDeletion`, `exists_thetaSymmetricPrimeDeletion_neg` |
| positive-convolution rigidity | `thetaTranslationMixture_rigidity` |
| mass-only normalization gauge: positive, even, zero-free, charge changes | `thetaTranslationMixture_twoPoint`, `thetaTwoPointGauge_pos`, `thetaTwoPointGauge_neg`, `integral_cexp_mul_thetaTwoPointGauge`, `thetaTwoPointGauge_multiplier_ne_zero`, `thetaTwoPointGauge_charge_ne` |

"Exhaustion of the primes" is the structure `PrimeExhaustion S`: every `S j` consists of primes
and every prime eventually lies in `S j`.
