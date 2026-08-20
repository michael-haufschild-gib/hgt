import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistRate
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The Möbius polynomial on the low-frequency disc

Near zero frequency every prime block of every ladder is essentially its own cardinality, so no
frequency partition helps there.  What does help is that the disc is **short**: the Route-T twisted
Möbius bound holds at every frequency below the length of the sum, so on a disc of bounded radius
the mean square is the pointwise bound squared times the length of the disc.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- A twisted Möbius initial sum is the same over `range (m+1)` and over `Icc 1 m`. -/
theorem sum_range_moebiusTwist_eq_Icc (τ : ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), moebiusTwist τ n = ∑ n ∈ Finset.Icc 1 m, moebiusTwist τ n := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  · intro n hn hn2
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Icc] at hn2
    have hn0 : n = 0 := by omega
    subst hn0
    exact moebiusTwist_zero τ

/-- **The Möbius mean square over a disc of bounded radius.**  Route T at every frequency below the
length of the sum, integrated over a set of measure `2w₀`. -/
theorem exists_setIntegral_disc_normSq_logPoly_moebius_le_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℝ in Filter.atTop, ∀ w₀ : ℝ, 0 ≤ w₀ → 2 * Real.pi * w₀ ≤ N →
      (∫ w in Set.Icc (-w₀) w₀, ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2)
        ≤ 2 * w₀ * (K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20)))) ^ 2 := by
  obtain ⟨K, hK, hmain⟩ := exists_norm_sum_moebiusTwist_le_rate
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain] with N hN
  intro w₀ hw₀ hle
  set C : ℝ := K * N * Real.exp (-((Real.log N) ^ ((1 : ℝ) / 20))) with hC
  have hC0 : 0 ≤ C := by
    have hN0 : (0 : ℝ) ≤ N := le_trans (by positivity) hle
    rw [hC]; positivity
  have hpt : ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2 ≤ C ^ 2 := by
    intro w hw
    rw [Set.mem_Icc] at hw
    have habs : |(-(2 * Real.pi * w))| ≤ N := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      have : |w| ≤ w₀ := abs_le.2 ⟨hw.1, hw.2⟩
      have h2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      calc 2 * Real.pi * |w| ≤ 2 * Real.pi * w₀ := by nlinarith
        _ ≤ N := hle
    have hval := hN (-(2 * Real.pi * w)) habs
    rw [sum_range_moebiusTwist_eq_Icc] at hval
    have heq : logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w
        = ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, moebiusTwist (-(2 * Real.pi * w)) n :=
      logPoly_moebiusCoeff_eq_sum_moebiusTwist _ w
    rw [heq]
    exact pow_le_pow_left₀ (norm_nonneg _) hval 2
  have hcont : Continuous fun w : ℝ => ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2 :=
    ((continuous_logPoly _ _).norm).pow 2
  have hint : IntegrableOn (fun w : ℝ => ‖logPoly moebiusCoeff (Finset.Icc 1 ⌊N⌋₊) w‖ ^ 2)
      (Set.Icc (-w₀) w₀) volume := hcont.integrableOn_Icc
  have hintC : IntegrableOn (fun _ : ℝ => C ^ 2) (Set.Icc (-w₀) w₀) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hmono := setIntegral_mono_on hint hintC measurableSet_Icc hpt
  have hvol : (volume.real (Set.Icc (-w₀) w₀)) = 2 * w₀ := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ w₀ - -w₀)]
    ring
  rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul] at hmono
  exact hmono

/-- **The disc bound at the fibre index set.**  Specialising the length to `√x + h`, which is what
the fibre index set truncates. -/
theorem exists_eventually_setIntegral_disc_fibre_le {hh : ℝ → ℝ}
    (hh0 : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ hh x) {w₀ : ℝ} (hw₀ : 0 ≤ w₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in Filter.atTop,
      (∫ w in Set.Icc (-w₀) w₀,
          ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (Finset.Icc 1 ⌊Real.sqrt x + hh x⌋₊) w‖ ^ 2)
        ≤ 2 * w₀ * (K * (Real.sqrt x + hh x)
            * Real.exp (-((Real.log (Real.sqrt x + hh x)) ^ ((1 : ℝ) / 20)))) ^ 2 := by
  obtain ⟨K, hK, hmain⟩ := exists_setIntegral_disc_normSq_logPoly_moebius_le_rate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hmain
  refine ⟨K, hK, ?_⟩
  set C : ℝ := max (max N₀ (2 * Real.pi * w₀)) 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  filter_upwards [hh0, Filter.eventually_ge_atTop (C ^ 2)] with x hx hxC
  have hsqrt : C ≤ Real.sqrt x := by
    rw [show C = Real.sqrt (C ^ 2) by rw [Real.sqrt_sq hC0]]
    exact Real.sqrt_le_sqrt hxC
  have hN : N₀ ≤ Real.sqrt x + hh x :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (by linarith)
  have hpi : 2 * Real.pi * w₀ ≤ Real.sqrt x + hh x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (by linarith)
  have hbase := hN₀ (Real.sqrt x + hh x) hN w₀ hw₀ hpi
  exact hbase

end

end RHTower.Sieve
