import GaloisForLFunctions.RHTower.PMPowerDampedMobiusHaarSeries
import GaloisForLFunctions.RHTower.SteinhausEulerSmoothSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Smooth-number dilated Haar source on the half-line

For `N : ℕ` the source `pmSmoothHaarSource N` is the dilation series
`t ↦ ∑' n, h(n t)` over the `N`-smooth numbers `n` (all prime factors below `N`), where `h` is the
dyadic Haar function supported on `(0, 1]` (equal to `-1` on `(0, 1/2]` and `1` on `(1/2, 1]`).
The module shows this series is a square-integrable and integrable function on `(0, ∞)` with
vanishing integral and support in `(0, 1]`, writes its `L²` energy as a Gram double series, and
shows the energy of the `(N+1)`-smooth source is at least the harmonic number `H_N`, hence at
least `log (N+1)` and unbounded as `N → ∞`.

## Main results

- `memLp_pmSmoothHaarSource`: the smooth Haar source lies in `L²((0, ∞))`.
- `integrable_pmSmoothHaarSource`: the smooth Haar source is integrable on `(0, ∞)`.
- `pmSmoothHaarSource_integral`: `∫_{(0,∞)} pmSmoothHaarSource N = 0`.
- `pmSmoothHaarSource_eq_sum`: for `t > 0` the series is the finite sum over smooth `n ≤ ⌊1/t⌋`.
- `pmSmoothHaarSource_energy_eq_tsum_gram`: the energy equals
  `∑' m, ∑' n, max 0 (2 / max m n - 1 / min m n)` over pairs of `N`-smooth numbers.
- `pmSmoothHaarSource_harmonic_le_energy`: `H_N ≤ ∫ ‖pmSmoothHaarSource (N+1)‖²`.
- `pmSmoothHaarSource_log_le_energy`: `log (N+1) ≤ ∫ ‖pmSmoothHaarSource (N+1)‖²`.
- `tendsto_pmSmoothHaarSource_energy`: the energy of `pmSmoothHaarSource (N+1)` tends to `∞`.

## Hypotheses

All results are unconditional. The only side conditions are positivity of a dilation factor
(`0 < a`) in the single-dilation lemmas and `0 < t` or `1 < t` in the pointwise formulas.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower

/-- The dilated Haar series `t ↦ ∑' n, h(n t)` summed over the `N`-smooth numbers `n`, with `h` the
dyadic Haar function supported on `(0, 1]`. -/
def pmSmoothHaarSource (N : ℕ) : ℝ → ℂ :=
  pmHaarDilationSeries (fun n : N.smoothNumbers => (n : ℝ))

theorem pm_smooth_cast_pos (N : ℕ) (n : N.smoothNumbers) : (0 : ℝ) < (n : ℕ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)

/-- The `L²` norms `n^(-1/2)` of the dilated Haar terms are summable over the `N`-smooth numbers. -/
theorem summable_pmSmoothHaarSource_term_norm (N : ℕ) :
    Summable (fun n : N.smoothNumbers => Real.sqrt (1 / (n : ℝ))) := by
  have heq (n : N.smoothNumbers) : Real.sqrt (1 / (n : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← pmHaarDilationVector_norm _ (pm_smooth_cast_pos N n), pmHaarDilationVector_norm_rpow]
  simpa only [heq] using summable_smoothNumbers_neg_rpow N (σ := 1 / 2) (by norm_num)

/-- The smooth Haar source is square integrable on `(0, ∞)`. -/
theorem memLp_pmSmoothHaarSource (N : ℕ) :
    MemLp (pmSmoothHaarSource N) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  memLp_pmHaarDilationSeries (pm_smooth_cast_pos N) (summable_pmSmoothHaarSource_term_norm N)

/-- The `L²((0,∞))` energy of the `(N+1)`-smooth Haar source is at least the harmonic number `H_N`,
from the diagonal terms `1/n`, `1 ≤ n ≤ N`, of the Gram expansion. -/
theorem pmSmoothHaarSource_harmonic_le_energy (N : ℕ) :
    (harmonic N : ℝ) ≤ (∫ t in Ioi (0 : ℝ), ‖pmSmoothHaarSource (N + 1) t‖ ^ (2 : ℕ)) := by
  classical
  have hmem : ∀ n ∈ Finset.Icc 1 N, n ∈ (N + 1).smoothNumbers := by
    intro n hn
    exact Nat.mem_smoothNumbers_of_lt (Finset.mem_Icc.mp hn).1
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  have h := pmHaarDilationSeries_diagonal_le_energy
    ((Finset.Icc 1 N).subtype (fun n => n ∈ (N + 1).smoothNumbers))
    (pm_smooth_cast_pos (N + 1)) (summable_pmSmoothHaarSource_term_norm (N + 1))
  rw [Finset.sum_subtype_of_mem (fun n : ℕ => 1 / (n : ℝ)) hmem] at h
  simpa only [pmSmoothHaarSource, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div] using h

/-- The energy of the `(N+1)`-smooth Haar source is at least `log (N+1)`. -/
theorem pmSmoothHaarSource_log_le_energy (N : ℕ) :
    Real.log (N + 1 : ℕ) ≤ (∫ t in Ioi (0 : ℝ), ‖pmSmoothHaarSource (N + 1) t‖ ^ (2 : ℕ)) :=
  (log_add_one_le_harmonic N).trans (pmSmoothHaarSource_harmonic_le_energy N)

/-- The `L²` energy of the `(N+1)`-smooth Haar source tends to infinity as `N → ∞`. -/
theorem tendsto_pmSmoothHaarSource_energy :
    Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ), ‖pmSmoothHaarSource (N + 1) t‖ ^ (2 : ℕ))
      atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℕ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  exact tendsto_atTop_mono (fun N => pmSmoothHaarSource_log_le_energy N) hlog

/-- For `t > 0` the smooth Haar series is the finite sum of `h(n t)` over `N`-smooth `n` with
`1 ≤ n ≤ ⌊1/t⌋`, since `h(n t) = 0` once `n t > 1`. -/
theorem pmSmoothHaarSource_eq_sum (N : ℕ) {t : ℝ} (ht : 0 < t) :
    pmSmoothHaarSource N t = ∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊,
      if n ∈ N.smoothNumbers then pmSupportedDyadicHaar ((n : ℝ) * t) else 0 := by
  classical
  unfold pmSmoothHaarSource pmHaarDilationSeries
  rw [tsum_subtype (N.smoothNumbers) (fun n : ℕ => pmSupportedDyadicHaar ((n : ℝ) * t))]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊1 / t⌋₊) (fun n hn => ?_)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [Set.indicator]
  · by_cases hs : n ∈ N.smoothNumbers
    · rw [Set.indicator_of_mem hs]
      have hn0 := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hs)
      have hgt : ⌊1 / t⌋₊ < n := by
        have hh := mt Finset.mem_Icc.mpr hn
        omega
      have hnt : 1 / t < (n : ℝ) := (Nat.lt_floor_add_one (1 / t)).trans_le
        (by exact_mod_cast (show ⌊1 / t⌋₊ + 1 ≤ n by omega))
      exact pmSupportedDyadicHaar_eq_zero (by
        have hh := (div_lt_iff₀ ht).mp hnt
        nlinarith)
    · exact Set.indicator_of_notMem hs _

/-- For `a > 0`, `‖h(a t)‖` is the indicator of `(0, 1/a]`. -/
theorem pmSupportedDyadicHaar_dilation_norm {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖pmSupportedDyadicHaar (a * t)‖ = pmHaarCutoff (1 / a) t := by
  have he : a * t ∈ Ioc (0 : ℝ) 1 ↔ t ∈ Ioc (0 : ℝ) (1 / a) := by
    simp only [Set.mem_Ioc, mul_pos_iff_of_pos_left ha, le_div_iff₀ ha]
    simp [mul_comm]
  by_cases ht : t ∈ Ioc (0 : ℝ) (1 / a)
  · rw [pmHaarCutoff, Set.indicator_of_mem ht, pmSupportedDyadicHaar, Set.indicator_of_mem (he.mpr ht)]
    exact norm_dyadicHaar _
  · have hat := mt he.mp ht
    rw [pmHaarCutoff, Set.indicator_of_notMem ht, pmSupportedDyadicHaar, Set.indicator_of_notMem hat, norm_zero]

theorem integrable_pmSupportedDyadicHaar_dilation {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => pmSupportedDyadicHaar (a * t)) (volume.restrict (Ioi (0 : ℝ))) := by
  apply (integrable_pmHaarCutoff (1 / a)).mono'
    (measurable_pmSupportedDyadicHaar.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => (pmSupportedDyadicHaar_dilation_norm ha t).le)

/-- For `a > 0`, `∫_{(0,∞)} ‖h(a t)‖ dt = 1/a`. -/
theorem pmSupportedDyadicHaar_dilation_integral_norm {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖pmSupportedDyadicHaar (a * t)‖) = 1 / a := by
  simp_rw [pmSupportedDyadicHaar_dilation_norm ha]
  exact pmHaarCutoff_integral (by positivity)

/-- For `a > 0`, the dilated Haar function has integral zero on `(0, ∞)`. -/
theorem pmSupportedDyadicHaar_dilation_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), pmSupportedDyadicHaar (a * t)) = 0 := by
  rw [integral_comp_mul_left_Ioi pmSupportedDyadicHaar 0 ha, mul_zero, pmSupportedDyadicHaar_integral]
  simp

/-- The smooth Haar source has integral zero on `(0, ∞)`; the termwise exchange uses summability of
`1/n` over the `N`-smooth numbers. -/
theorem pmSmoothHaarSource_integral (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), pmSmoothHaarSource N t) = 0 := by
  have hs : Summable (fun n : N.smoothNumbers => 1 / (n : ℝ)) := by
    simpa only [neg_one_mul, Real.rpow_neg_one, one_div] using
      summable_smoothNumbers_neg_rpow N (σ := 1) (by norm_num)
  have hnorm : Summable (fun n : N.smoothNumbers =>
      ∫ t in Ioi (0 : ℝ), ‖pmSupportedDyadicHaar ((n : ℝ) * t)‖) := by
    simpa only [pmSupportedDyadicHaar_dilation_integral_norm (pm_smooth_cast_pos N _)] using hs
  unfold pmSmoothHaarSource pmHaarDilationSeries
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => integrable_pmSupportedDyadicHaar_dilation (pm_smooth_cast_pos N n)) hnorm]
  simp only [pmSupportedDyadicHaar_dilation_integral (pm_smooth_cast_pos N _), tsum_zero]

/-- The smooth Haar source vanishes for `t > 1`. -/
theorem pmSmoothHaarSource_eq_zero (N : ℕ) {t : ℝ} (ht : 1 < t) : pmSmoothHaarSource N t = 0 := by
  have hz (n : N.smoothNumbers) : pmSupportedDyadicHaar ((n : ℝ) * t) = 0 := by
    apply pmSupportedDyadicHaar_eq_zero
    have hn : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
    nlinarith
  simp only [pmSmoothHaarSource, pmHaarDilationSeries, hz, tsum_zero]

/-- The smooth Haar source is integrable on `(0, ∞)`, being `L²` and supported in `(0, 1]`. -/
theorem integrable_pmSmoothHaarSource (N : ℕ) :
    Integrable (pmSmoothHaarSource N) (volume.restrict (Ioi (0 : ℝ))) := by
  have hi : IntegrableOn (pmSmoothHaarSource N) (Ioc (0 : ℝ) 1) :=
    ((memLp_pmSmoothHaarSource N).mono_measure
      (Measure.restrict_mono (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self) le_rfl)).integrable
      (by norm_num)
  have hind := (hi.integrable_indicator measurableSet_Ioc).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi (0 : ℝ)))
  apply (integrable_congr (show (Ioc (0 : ℝ) 1).indicator (pmSmoothHaarSource N) =ᵐ[volume.restrict (Ioi 0)]
    pmSmoothHaarSource N from ?_)).mp hind
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases ht1 : t ≤ 1
  · exact Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩) _
  · rw [Set.indicator_of_notMem (by simp [ht1]), pmSmoothHaarSource_eq_zero N (lt_of_not_ge ht1)]

/-- The `L²((0,∞))` energy of the smooth Haar source equals the double series of Gram entries
`max 0 (2 / max m n - 1 / min m n)` over pairs of `N`-smooth numbers `m, n`. -/
theorem pmSmoothHaarSource_energy_eq_tsum_gram (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖pmSmoothHaarSource N t‖ ^ (2 : ℕ)) =
      ∑' m : N.smoothNumbers, ∑' n : N.smoothNumbers,
        max 0 (2 / max (m : ℝ) (n : ℝ) - 1 / min (m : ℝ) (n : ℝ)) := by
  rw [pmSmoothHaarSource, pmHaarDilationSeries_energy_eq_tsum_gram
    (pm_smooth_cast_pos N) (summable_pmSmoothHaarSource_term_norm N)]
  apply tsum_congr
  intro m
  apply tsum_congr
  intro n
  exact pmHaarDilationGram_eq_max (pm_smooth_cast_pos N m) (pm_smooth_cast_pos N n)

end RHTower
