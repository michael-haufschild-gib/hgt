import GaloisForLFunctions.BiScaleUncertainty.SawtoothPhaseCancellationAndBandSpectralProducer
import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureLargeValues
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem

/-!
# Critical-Band Large-Value Measure, Halász `L¹` Spectral Bounds, and Vinogradov–Korobov Sawtooth Cancellation

This module connects `BiScaleUncertainty` (`ChebyshevGauge` and `SawtoothPhaseCancellationAndBandSpectralProducer`)
to the unconditional Dirichlet polynomial large-values and Vinogradov–Korobov prime number theorem
machinery in `RHTower/Sieve/`:

1. **Critical-Band Large-Value Level-Set Measure Bounds (`volume_largeValues_atomicCoefficient_le_cutoff`,
   `volume_largeValues_Icc_atomicCoefficient_le_cutoff`, `volume_largeValues_criticalBand_le_cutoff`):**
   Combining `atomicFourier_eq_dirPoly` (`HighFrequencyLaplaceEnergyMeanValue.lean:51`) and
   `atomicDiagonal_le_cutoff_mul` (`BandLimitedLaplaceEnergy.lean:49`) with
   `RHTower.Sieve.volume_largeValues_le` and `RHTower.Sieve.volume_largeValues_Icc_le`
   (`DirichletMeasureLargeValues.lean:23, 67`) bounds the Lebesgue measure of the frequency level set
   `{t ∈ (0, T] | V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}`—in particular on the critical
   Nyquist band `T = 2 * π * bandFrequency N`—explicitly in terms of `cutoff N`.

2. **Halász Mean-Value `L¹` Bounds on the Atomic Dirichlet Polynomial
   (`integral_norm_atomicCoefficient_halasz`, `integral_norm_atomicCoefficient_halasz_l1_le_cutoff`):**
   Combining `RHTower.Sieve.integral_norm_dirPoly_halasz` and `integral_norm_dirPoly_halasz_l1`
   (`DirichletMeasureLargeValues.lean:148, 171`) with `atomicDiagonal_le_cutoff_mul` bounds the
   first moment `∫ t in Set.Ioc 0 T, ‖dirPoly (N + 2) (atomicCoefficient N) t‖` on any frequency
   interval `(0, T]`.

3. **Vinogradov–Korobov Rate for `chebyshevErrorSeq`, `dyadicChebyshevDiffSeq`, and the Dyadic
   Sawtooth Phase Difference (`exists_abs_chebyshevErrorSeq_le_vk_rate`,
   `exists_abs_dyadicChebyshevDiffSeq_two_mul_le_vk_rate`,
   `exists_abs_dyadic_sawtooth_phase_diff_le_vk_rate`):**
   Upgrades the $O(n)$ Chebyshev and Stirling bounds in `ChebyshevHeadAndShearCellProducer.lean` and
   `SawtoothPhaseCancellationAndBandSpectralProducer.lean` to the unconditional Vinogradov–Korobov rate
   `B * n * exp(-vkKappa * vkScale n / 24)` (`VinogradovKorobovPrimeNumberTheorem.lean:178`).
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open Zeta23 RHTower RHTower.Sieve
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open scoped RealInnerProductSpace BigOperators CompactlySupported Real FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-! ## §1. Critical-Band Large-Value Level-Set Measure & Halász `L¹` Bounds -/

namespace ChebyshevGauge

/-- Exact identification `cutoff N = Real.log ((N + 2 : ℕ) : ℝ)`. -/
theorem cutoff_eq_log_natCast (N : ℕ) :
    cutoff N = Real.log ((N + 2 : ℕ) : ℝ) := rfl

/-- **Large-Value Level-Set Measure Bound for `atomicCoefficient N` on `(0, T]`
(`volume_largeValues_atomicCoefficient_le`):**
For every `N : ℕ` and `T, V ≥ 0`, the Lebesgue measure of the level set where the atomic Dirichlet
polynomial `dirPoly (N + 2) (atomicCoefficient N)` exceeds `V` on `(0, T]` satisfies
`V^2 * |{t ∈ (0, T] : V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}| ≤ (T + 4(N + 2)(1 + cutoff N)) * atomicDiagonal N`. -/
theorem volume_largeValues_atomicCoefficient_le (N : ℕ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}
      ≤ (T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) * atomicDiagonal N := by
  simpa only [atomicDiagonal, cutoff_eq_log_natCast] using
    volume_largeValues_le (N + 2) (atomicCoefficient N) hT hV

/-- **Mertens-Calibrated Large-Value Level-Set Measure Bound on `(0, T]`
(`volume_largeValues_atomicCoefficient_le_cutoff`):**
Combines `volume_largeValues_atomicCoefficient_le` with `atomicDiagonal_le_cutoff_mul` to bound the
level-set measure explicitly in terms of `cutoff N = log(N + 2)`. -/
theorem volume_largeValues_atomicCoefficient_le_cutoff (N : ℕ) {T V : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}
      ≤ (T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) *
          (cutoff N * (cutoff N + (Real.log 4 + 4))) := by
  have h1 := volume_largeValues_atomicCoefficient_le N hT hV
  have h2 := atomicDiagonal_le_cutoff_mul N
  have hfac : 0 ≤ T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N) := by
    have := cutoff_nonneg N
    positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hfac)

/-- **Mertens-Calibrated Large-Value Level-Set Measure Bound on `[0, T]`
(`volume_largeValues_Icc_atomicCoefficient_le_cutoff`):**
Closed-interval version of `volume_largeValues_atomicCoefficient_le_cutoff`. -/
theorem volume_largeValues_Icc_atomicCoefficient_le_cutoff (N : ℕ) {T V : ℝ}
    (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Icc (0 : ℝ) T | V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}
      ≤ (T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) *
          (cutoff N * (cutoff N + (Real.log 4 + 4))) := by
  have h1 :
      V ^ 2 * volume.real {t ∈ Set.Icc (0 : ℝ) T | V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}
        ≤ (T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) * atomicDiagonal N := by
    simpa only [atomicDiagonal, cutoff_eq_log_natCast] using
      volume_largeValues_Icc_le (N + 2) (atomicCoefficient N) hT hV
  have h2 := atomicDiagonal_le_cutoff_mul N
  have hfac : 0 ≤ T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N) := by
    have := cutoff_nonneg N
    positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hfac)

/-- **Critical-Band Large-Value Level-Set Measure Bound at `T = 2 * π * bandFrequency N`
(`volume_largeValues_criticalBand_le_cutoff`):**
Specializes `volume_largeValues_Icc_atomicCoefficient_le_cutoff` to the Nyquist critical band
`[0, 2 * π * √(N + 2)]`. -/
theorem volume_largeValues_criticalBand_le_cutoff (N : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    V ^ 2 * volume.real
        {t ∈ Set.Icc (0 : ℝ) (2 * π * bandFrequency N) |
          V ≤ ‖dirPoly (N + 2) (atomicCoefficient N) t‖}
      ≤ (2 * π * bandFrequency N + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) *
          (cutoff N * (cutoff N + (Real.log 4 + 4))) := by
  have hT : 0 ≤ 2 * π * bandFrequency N := by
    have := bandFrequency_pos N
    positivity
  exact volume_largeValues_Icc_atomicCoefficient_le_cutoff N hT hV

/-- **Halász Mean-Value `L¹` Bound for `atomicCoefficient N` with Explicit Sup `M`
(`integral_norm_atomicCoefficient_halasz_le_cutoff`):**
For every `N : ℕ`, `T ≥ 0`, `V > 0`, and uniform bound `M` on `‖dirPoly (N + 2) (atomicCoefficient N)‖`,
bounds `∫ t in Set.Ioc 0 T, ‖dirPoly (N + 2) (atomicCoefficient N) t‖` in terms of `cutoff N`. -/
theorem integral_norm_atomicCoefficient_halasz_le_cutoff (N : ℕ) {T V M : ℝ}
    (hT : 0 ≤ T) (hV : 0 < V)
    (hM : ∀ t : ℝ, ‖dirPoly (N + 2) (atomicCoefficient N) t‖ ≤ M) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly (N + 2) (atomicCoefficient N) t‖
      ≤ V * T +
        M * ((T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) *
          (cutoff N * (cutoff N + (Real.log 4 + 4)))) / V ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hbase :
      ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly (N + 2) (atomicCoefficient N) t‖
        ≤ V * T +
          M * ((T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) * atomicDiagonal N) / V ^ 2 := by
    simpa only [atomicDiagonal, cutoff_eq_log_natCast] using
      integral_norm_dirPoly_halasz (N + 2) (atomicCoefficient N) hT hV hM
  have hdiag := atomicDiagonal_le_cutoff_mul N
  have hfac : 0 ≤ T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N) := by
    have := cutoff_nonneg N
    positivity
  have hnum :
      M * ((T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) * atomicDiagonal N) ≤
        M * ((T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) *
          (cutoff N * (cutoff N + (Real.log 4 + 4)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiag hfac) hM0
  exact hbase.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hnum (by positivity)))

/-- **Halász Mean-Value `L¹` Bound for `atomicCoefficient N` with Coefficient `ℓ¹` Norm
(`integral_norm_atomicCoefficient_halasz_l1_le_cutoff`):**
Unconditional `L¹` frequency mean-value bound for the atomic Dirichlet polynomial on `(0, T]` with
no external sup hypothesis. -/
theorem integral_norm_atomicCoefficient_halasz_l1_le_cutoff (N : ℕ) {T V : ℝ}
    (hT : 0 ≤ T) (hV : 0 < V) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly (N + 2) (atomicCoefficient N) t‖
      ≤ V * T +
        (∑ m : Fin (N + 2), ‖atomicCoefficient N m‖) *
          ((T + 4 * ((N + 2 : ℕ) : ℝ) * (1 + cutoff N)) *
            (cutoff N * (cutoff N + (Real.log 4 + 4)))) / V ^ 2 :=
  integral_norm_atomicCoefficient_halasz_le_cutoff N hT hV
    (norm_dirPoly_le_sum_norm (N + 2) (atomicCoefficient N))

end ChebyshevGauge

/-! ## §2. Vinogradov–Korobov Rate for `chebyshevErrorSeq`, `dyadicChebyshevDiffSeq`, and Sawtooth Phase Cancellation -/

/-- Exact identity between `chebyshevErrorSeq n` and `(∑ d ∈ Finset.range (n + 1), vonMangoldt d) - n`. -/
theorem chebyshevErrorSeq_eq_sum_range_sub (n : ℕ) :
    chebyshevErrorSeq n = (∑ d ∈ Finset.range (n + 1), (vonMangoldt d : ℝ)) - (n : ℝ) := by
  unfold chebyshevErrorSeq
  rw [Chebyshev.psi_eq_sum_range, Nat.floor_natCast]

/-- **Vinogradov–Korobov Rate for `chebyshevErrorSeq` (`exists_abs_chebyshevErrorSeq_le_vk_rate`):**
Upgrades the $O(n)$ bound `abs_chebyshevErrorSeq_le` (`ChebyshevHeadAndShearCellProducer.lean:186`)
to the unconditional Vinogradov–Korobov rate:
`|chebyshevErrorSeq n| ≤ B * n * exp(-vkKappa * vkScale n / 24)`. -/
theorem exists_abs_chebyshevErrorSeq_le_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      |chebyshevErrorSeq n| ≤ B * (n : ℝ) * Real.exp (-(vkKappa * vkScale (n : ℝ) / 24)) := by
  obtain ⟨B, hB0, hrate⟩ := exists_abs_sum_vonMangoldt_sub_self_vk_rate
  refine ⟨B, hB0, ?_⟩
  have hev := tendsto_natCast_atTop_atTop.eventually hrate
  filter_upwards [hev] with n hn
  rw [chebyshevErrorSeq_eq_sum_range_sub]
  simpa only [Nat.floor_natCast] using hn

/-- Exact identity expressing `dyadicChebyshevDiffSeq (2 * m)` in terms of `chebyshevErrorSeq m`
and `chebyshevErrorSeq (2 * m)`. -/
theorem dyadicChebyshevDiffSeq_two_mul_eq_two_mul_error_sub (m : ℕ) :
    dyadicChebyshevDiffSeq (2 * m) = 2 * chebyshevErrorSeq m - chebyshevErrorSeq (2 * m) := by
  unfold dyadicChebyshevDiffSeq chebyshevErrorSeq
  rw [chebyshev_psi_even_half_eq m]
  change 2 * chebyshevPsiSeq m - chebyshevPsiSeq (2 * m) =
    2 * (chebyshevPsiSeq m - (m : ℝ)) - (chebyshevPsiSeq (2 * m) - ((2 * m : ℕ) : ℝ))
  push_cast
  ring

/-- **Vinogradov–Korobov Rate for `dyadicChebyshevDiffSeq (2 * m)`
(`exists_abs_dyadicChebyshevDiffSeq_two_mul_le_vk_rate`):**
Upgrades the $O(m)$ Stirling bounds on `dyadicChebyshevDiffSeq (2 * m)` in
`ChebyshevHeadAndShearCellProducer.lean` to the unconditional Vinogradov–Korobov rate. -/
theorem exists_abs_dyadicChebyshevDiffSeq_two_mul_le_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ m : ℕ in atTop,
      |dyadicChebyshevDiffSeq (2 * m)| ≤
        2 * B * (m : ℝ) * Real.exp (-(vkKappa * vkScale (m : ℝ) / 24)) +
          2 * B * (m : ℝ) * Real.exp (-(vkKappa * vkScale ((2 * m : ℕ) : ℝ) / 24)) := by
  obtain ⟨B, hB0, hev⟩ := exists_abs_chebyshevErrorSeq_le_vk_rate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨B, hB0, Filter.eventually_atTop.mpr ⟨max N₀ 1, fun m hm => ?_⟩⟩
  have hm₀ : N₀ ≤ m := le_of_max_le_left hm
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have h2m₀ : N₀ ≤ 2 * m := by omega
  have h1 := hN₀ m hm₀
  have h2 : |chebyshevErrorSeq (2 * m)| ≤
      2 * B * (m : ℝ) * Real.exp (-(vkKappa * vkScale ((2 * m : ℕ) : ℝ) / 24)) := by
    refine (hN₀ (2 * m) h2m₀).trans (le_of_eq ?_)
    have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    linear_combination B * Real.exp (-(vkKappa * vkScale ((2 * m : ℕ) : ℝ) / 24)) * hcast
  rw [dyadicChebyshevDiffSeq_two_mul_eq_two_mul_error_sub]
  have habs :
      |2 * chebyshevErrorSeq m - chebyshevErrorSeq (2 * m)| ≤
        2 * |chebyshevErrorSeq m| + |chebyshevErrorSeq (2 * m)| := by
    calc
      |2 * chebyshevErrorSeq m - chebyshevErrorSeq (2 * m)|
        ≤ |2 * chebyshevErrorSeq m| + |chebyshevErrorSeq (2 * m)| := abs_sub _ _
      _ = 2 * |chebyshevErrorSeq m| + |chebyshevErrorSeq (2 * m)| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Uniform Vinogradov–Korobov Rate for Common-Cutoff Dyadic Sawtooth Phase Cancellation
(`exists_abs_dyadic_sawtooth_phase_diff_le_vk_rate`):**
Upgrades the linear bound `≤ (log 4 + 4) * (2 * m)` in
`SawtoothPhaseCancellationAndBandSpectralProducer.lean` to the unconditional Vinogradov–Korobov rate,
uniformly for **all** cutoff offsets `k : ℕ`. -/
theorem exists_abs_dyadic_sawtooth_phase_diff_le_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ m : ℕ in atTop, ∀ k : ℕ,
      |weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) (2 * m) -
          2 * weightedFractSumSeq vonMangoldtDivisorWeight (2 * m + k) m| ≤
        2 * B * (m : ℝ) * Real.exp (-(vkKappa * vkScale (m : ℝ) / 24)) +
          2 * B * (m : ℝ) * Real.exp (-(vkKappa * vkScale ((2 * m : ℕ) : ℝ) / 24)) := by
  obtain ⟨B, hB0, hev⟩ := exists_abs_dyadicChebyshevDiffSeq_two_mul_le_vk_rate
  refine ⟨B, hB0, ?_⟩
  filter_upwards [hev] with m hm k
  rw [← dyadicChebyshevDiffSeq_two_mul_eq_fractSum_diff m k]
  exact hm

end

end GaloisForLFunctions.BiScaleUncertainty
