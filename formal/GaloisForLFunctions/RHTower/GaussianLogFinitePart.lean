import GaloisForLFunctions.RHTower.HalfNormalExactScale
import GaloisForLFunctions.HTGeometry.SquaredVariableSubstitution

/-!
# Gaussian logarithmic finite part

The logarithmically divergent Gaussian head becomes the entire exponential integral `Ein` after
the compact square substitution.  Combining this exact identity with the Frullani formula isolates
the finite part and leaves only the exponentially small terminal exponential-integral tail.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

noncomputable section

/-- Restricting a real half-line integral of an interval-supported function to that interval. -/
theorem integral_Ioi_indicator_Ioc_real {h : ℝ → ℝ} :
    (∫ t in Ioi (0 : ℝ), Set.indicator (Ioc (0 : ℝ) 1) h t) =
      ∫ t in Ioc (0 : ℝ) 1, h t := by
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    show Ioc (0 : ℝ) 1 ∩ Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 from
      Set.inter_eq_left.mpr (fun t ht => ht.1)]

/-- Compact square substitution for the scaled exponential-integral profile. -/
theorem integral_Ioc_scaledEinProfile_sq {V : ℝ} (hV : 0 < V) :
    (∫ t in Ioc (0 : ℝ) 1,
        (1 - Real.exp (-(V * t ^ (2 : ℕ)))) / t) = ein V / 2 := by
  let g : ℝ → ℝ := Set.indicator (Ioc (0 : ℝ) 1) (scaledEinProfile V)
  have hsq := GaloisForLFunctions.HTGeometry.integral_Ioi_comp_sq g
  have hleft : (∫ u in Ioi (0 : ℝ), g u) = ein V := by
    rw [show (∫ u in Ioi (0 : ℝ), g u) =
        ∫ u in Ioc (0 : ℝ) 1, scaledEinProfile V u by
      exact integral_Ioi_indicator_Ioc_real]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_scaledEinProfile hV]
  have hright :
      (∫ t in Ioi (0 : ℝ), (2 * t) * g (t ^ (2 : ℕ))) =
        2 * ∫ t in Ioc (0 : ℝ) 1,
          (1 - Real.exp (-(V * t ^ (2 : ℕ)))) / t := by
    rw [← MeasureTheory.integral_const_mul,
      ← integral_Ioi_indicator_Ioc_real
        (h := fun t : ℝ => 2 * ((1 - Real.exp (-(V * t ^ (2 : ℕ)))) / t))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    by_cases ht1 : t ≤ 1
    · have htmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, ht1⟩
      have htsqmem : t ^ (2 : ℕ) ∈ Ioc (0 : ℝ) 1 := by
        constructor
        · positivity
        · nlinarith
      simp only [g, Set.indicator_of_mem htsqmem, Set.indicator_of_mem htmem,
        scaledEinProfile]
      rw [if_neg (pow_ne_zero 2 (ne_of_gt ht0))]
      field_simp
    · have htmem : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
      have htsqmem : t ^ (2 : ℕ) ∉ Ioc (0 : ℝ) 1 := by
        intro h
        have htgt : 1 < t := lt_of_not_ge ht1
        nlinarith [h.2]
      simp [g, Set.indicator_of_notMem htmem, Set.indicator_of_notMem htsqmem]
  rw [hleft, hright] at hsq
  linarith

/-- Exact finite-window logarithmic Gaussian head in terms of `Ein`. -/
theorem integral_Ioc_gaussian_sub_one_div {x : ℝ} (hx : 0 < x) :
    (∫ theta in Ioc (0 : ℝ) Real.pi,
        (Real.exp (-(theta ^ (2 : ℕ) / (4 * Real.pi * x))) - 1) / theta) =
      -ein (Real.pi / (4 * x)) / 2 := by
  let f : ℝ → ℝ := fun theta =>
    (Real.exp (-(theta ^ (2 : ℕ) / (4 * Real.pi * x))) - 1) / theta
  let V : ℝ := Real.pi / (4 * x)
  have hV : 0 < V := by dsimp [V]; positivity
  have hscale := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) f Real.pi_ne_zero
  rw [mul_zero, mul_one, smul_eq_mul] at hscale
  calc
    (∫ theta in Ioc (0 : ℝ) Real.pi,
        (Real.exp (-(theta ^ (2 : ℕ) / (4 * Real.pi * x))) - 1) / theta) =
        ∫ theta in (0 : ℝ)..Real.pi, f theta := by
          rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    _ = Real.pi * ∫ t in (0 : ℝ)..1, f (Real.pi * t) := by
      rw [hscale]
      field_simp
    _ = -(∫ t in (0 : ℝ)..1,
        (1 - Real.exp (-(V * t ^ (2 : ℕ)))) / t) := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      by_cases ht0 : t = 0
      · simp [f, ht0]
      · dsimp [f, V]
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
        ring
    _ = -ein V / 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        integral_Ioc_scaledEinProfile_sq hV]
      ring
    _ = -ein (Real.pi / (4 * x)) / 2 := by rfl

/-- Exact large-argument Frullani decomposition of `Ein`, including its terminal tail. -/
theorem ein_eq_eulerMascheroni_add_log_add_tail {a : ℝ} (ha : 1 ≤ a) :
    ein a = Real.eulerMascheroniConstant + Real.log a +
      ∫ t in Ioi a, Real.exp (-t) / t := by
  rw [ein_eq ha, integral_exp_neg_div_Icc_eq ha,
    ← frullani_eq_eulerMascheroni]
  ring

/-- Exact Gaussian logarithmic finite part.  Its only error is the terminal `E₁` tail. -/
theorem gaussianLogFinitePart_eq_tail {x : ℝ} (hx : 0 < x)
    (hxUpper : x ≤ Real.pi / 4) :
    Real.log Real.pi +
        (∫ theta in Ioc (0 : ℝ) Real.pi,
          (Real.exp (-(theta ^ (2 : ℕ) / (4 * Real.pi * x))) - 1) / theta) =
      (Real.log (4 * Real.pi * x) - Real.eulerMascheroniConstant) / 2 -
        (∫ t in Ioi (Real.pi / (4 * x)), Real.exp (-t) / t) / 2 := by
  have hV : 1 ≤ Real.pi / (4 * x) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * x)).mpr
    linarith
  rw [integral_Ioc_gaussian_sub_one_div hx,
    ein_eq_eulerMascheroni_add_log_add_tail hV]
  have hlog :
      2 * Real.log Real.pi - Real.log (Real.pi / (4 * x)) =
        Real.log (4 * Real.pi * x) := by
    rw [Real.log_div (ne_of_gt Real.pi_pos) (by positivity : (4 * x : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hx),
      Real.log_mul (by positivity : (4 * Real.pi : ℝ) ≠ 0) (ne_of_gt hx),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)]
    ring
  linarith

end

end RHTower
