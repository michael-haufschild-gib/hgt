# ULF-SRFM-1 — Lean formalization record

**Card:** `superposition-thinning-poisson-formation-recovery-and-gamma-six-polarity-law.md`

**Modules** (all in `formal/GaloisForLFunctions/HTGeometry/`, namespace
`GaloisForLFunctions.HTGeometry`), all imported by `GaloisForLFunctions.HTGeometry` and
`GaloisForLFunctions.HTGeometry.UniversalLawField`:

| Module | Content |
|---|---|
| `PoissonFormationCharacterization.lean` | §2 and Poisson splitting/recovery |
| `PoissonIntensityMarkingIsometry.lean` | §3 and the §4 scalars |
| `HellingerAffinityProduct.lean` | the §4 packet-level statements |
| `GammaSixGlobalPolarity.lean` | §5 |

## Card result → Lean declaration

| Card result | Lean declaration |
|---|---|
| the four source axioms | `IsFormationSpecies` (`vacuum`, `superposition` via `Measure.conv`, `thinning` via `thinLaw`/`ProbabilityTheory.binomial`, `calibration`) |
| **Theorem 2.1** | `eq_poissonMeasure_of_isFormationSpecies` |
| (2.1) PGF multiplicativity | `pgfE_conv` |
| (2.2) small-rate bound | `one_sub_pgf_le` |
| (2.3) continuous multiplicative Cauchy | `eq_mul_of_additive_of_nonneg` |
| (2.4) thinning shifts the argument | `pgfE_thinLaw`, `integral_pow_binomial` |
| PGF determines the law | `measure_eq_of_pgf_eq`, `eq_zero_of_tsum_pow_eq_zero` |
| Poisson PGF | `pgf_poissonMeasure` |
| `D_+`, (3.1) | `intensityDiv` |
| **Theorem 3.1(1)**, (3.2) | `toReal_klDiv_poissonPacket` (via `klDiv_prod`, `klDiv_pi`) |
| **Theorem 3.1(2)**, (3.3) | `intensityDiv_marking` |
| **Theorem 3.1(3)** splitting/recovery | `map_sum_pi_poissonMeasure` |
| **Corollary 3.2**, (3.4) | `intensityDiv_mass_shape` |
| **(3.5)** | `intensityJeffreys_mass_shape` |
| `N_m`, `λ_m`, `x_m`, (4.1) | `gammaSixCount`, `gammaSixClock`, `gammaSixForward`, `gammaSixReflected` |
| (4.2) totals | `gammaSixForward_total`, `gammaSixReflected_total` |
| **Theorem 4.1**, (4.3) | `gammaSix_forward_div`, `gammaSix_packet_klDiv` |
| **(4.4)** | `gammaSix_reflected_div`, `gammaSix_packet_klDiv_reflected` |
| **(4.5)** | `gammaSix_jeffreys` |
| **(4.6)** | `gammaSix_chirality` |
| **(4.7)** | `gammaSix_intensityHellingerSq` |
| **(4.8)** | `gammaSix_packet_affinity` (via `hellingerAffinity_pi`, `hellingerAffinity_prod`) |
| reflection invariance / reversal | `gammaSix_jeffreys_reflection`, `gammaSix_chirality_reflection` |
| `P_δ^±`, (5.1) | `gammaSixLaw` on `GammaSixLabel → ℕ` (`Measure.infinitePi`) |
| **Theorem 5.1**, (5.2) | `gammaSixLaw_eq_iff`, `gammaSixLaw_mutuallySingular` |
| **Corollary 5.2** | `gammaSixLaw_absolutelyContinuous_iff` |

## Method notes

* Theorem 2.1's Cauchy step is done with **monotonicity**, not continuity: the exponent
  `λ ↦ -log G_λ(z)` is additive and nonnegative, hence monotone, hence linear
  (`eq_mul_of_additive_of_nonneg`, proved by a floor sandwich).  The card's small-rate bound
  `(2.2)` is formalized as `one_sub_pgf_le` and is what makes the exponent finite.
* The affine step `(2.4)` needs no two-point argument at `z = 0`: the thinning relation gives
  `c(1-p+pz) = p c(z)` for every `z ∈ (0,1]`, and comparing at `z = 1/2` pins `c(z) = C(1-z)`.
* The normalization `C = 1` is obtained **after** the determinacy step, from the Poisson mean
  (`integral_id_poissonMeasure`), avoiding any monotone-convergence limit at `z ↑ 1`.
* Determinacy (`eq_zero_of_tsum_pow_eq_zero`) is an elementary induction: absolute summability of
  the coefficient differences bounds the tail of `∑ d_k z^k` by `z · M`, so each coefficient
  vanishes in turn.  Only `z ∈ (0,1]` is used.
* §5 is proved by the **label-wise** occupancy dichotomy of
  `HTGeometry.ProductOccupancyDichotomy` (the two Borel--Cantelli lemmas): off the centre the
  occupancy masses are summable in one direction and divergent in the other, so the
  finite-occupancy event separates the two laws.

## Verification

* `lake env lean` on each of the four modules: 0 errors, 0 warnings.
* Axiom audit: `PoissonFormationCharacterization` (26), `PoissonIntensityMarkingIsometry` (24),
  `HellingerAffinityProduct` (10), `GammaSixGlobalPolarity` (16) public declarations — only
  `propext`, `Classical.choice`, `Quot.sound`.
