import GaloisForLFunctions.ArithmeticElectrostatics.ThePolynomialHeatDivisorPaysLogarithmicDepth
import GaloisForLFunctions.ArithmeticElectrostatics.TheLogarithmicDepthThresholdIsALimit
import GaloisForLFunctions.ArithmeticElectrostatics.TheElapsedHeatCoefficientIsSharp

/-!
# Logarithmic thresholds for the polynomial heat divisor

Every positive threshold gives an initial budget for surviving elapsed
squared depths. Normalized smooth logarithmic profiles converge with
uniform scalar error, so finite root sums pass directly to the threshold.
An isolated quadratic pair attains equality and makes the clock coefficient
`2` optimal.
-/

open Polynomial Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

private theorem sum_map_div (S : Multiset ℂ) (F : ℂ → ℝ) (r : ℝ) :
    (S.map (fun z => F z / r)).sum = (S.map F).sum / r := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons z S ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih, add_div]

theorem tendsto_root_sum_logarithmicThreshold (S : Multiset ℂ) (u : ℂ → ℝ)
    (hu : ∀ z ∈ S, 0 ≤ u z) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (S.map (fun z =>
      elapsedLogDepthProfile ((n : ℝ) + 1) (a ^ ((n : ℝ) + 1)) (u z) / ((n : ℝ) + 1))).sum)
      atTop (𝓝 (S.map (fun z => logarithmicDepthThreshold a (u z))).sum) := by
  induction S using Multiset.induction_on with
  | empty => simpa only [Multiset.map_zero, Multiset.sum_zero] using tendsto_const_nhds
  | cons z S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (tendsto_elapsedLogDepthProfile_threshold ha (hu z (Multiset.mem_cons_self z S))).add
      (ih (fun w hw => hu w (Multiset.mem_cons_of_mem hw)))

/-- The complete nonreal divisor spends only its initial threshold budget. -/
theorem polynomial_logarithmicThreshold_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) :
    ((((polyHeat t p).map ofRealHom).roots.filter (fun z => z.im ≠ 0)).map
      (fun z => logarithmicDepthThreshold a (z.im ^ 2 + 2 * t))).sum ≤
      ((p.map ofRealHom).roots.map (fun z => logarithmicDepthThreshold a (z.im ^ 2))).sum := by
  have hl := tendsto_root_sum_logarithmicThreshold
    (((polyHeat t p).map ofRealHom).roots.filter (fun z => z.im ≠ 0))
    (fun z => z.im ^ 2 + 2 * t) (fun z _ => by positivity) ha
  have hr := tendsto_root_sum_logarithmicThreshold (p.map ofRealHom).roots
    (fun z => z.im ^ 2) (fun z _ => sq_nonneg _) ha
  apply le_of_tendsto_of_tendsto' hl hr
  intro n
  rw [sum_map_div, sum_map_div]
  exact div_le_div_of_nonneg_right
    (polynomial_log_elapsed_moment_le_initial hp (r := (n : ℝ) + 1) (by positivity)
      (Real.rpow_pos_of_pos ha _) ht) (by positivity)

/-- The upper divisor obeys the same budget, with multiplicity. -/
theorem polynomial_upper_logarithmicThreshold_le_initial {p : ℝ[X]} (hp : p ≠ 0)
    {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) :
    ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
      (fun z => logarithmicDepthThreshold a (z.im ^ 2 + 2 * t))).sum ≤
      ((RiemannGaussian.realPolynomialUpperRootMultiset p).map
        (fun z => logarithmicDepthThreshold a (z.im ^ 2))).sum := by
  have hl := tendsto_root_sum_logarithmicThreshold
    (RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p))
    (fun z => z.im ^ 2 + 2 * t) (fun z _ => by positivity) ha
  have hr := tendsto_root_sum_logarithmicThreshold
    (RiemannGaussian.realPolynomialUpperRootMultiset p)
    (fun z => z.im ^ 2) (fun z _ => sq_nonneg _) ha
  apply le_of_tendsto_of_tendsto' hl hr
  intro n
  rw [sum_map_div, sum_map_div]
  exact div_le_div_of_nonneg_right
    (polynomial_upper_log_elapsed_moment_le_initial hp (r := (n : ℝ) + 1) (by positivity)
      (Real.rpow_pos_of_pos ha _) ht) (by positivity)

/-- An isolated conjugate pair attains every threshold budget until collision. -/
theorem quadratic_upper_logarithmicThreshold_eq {c t : ℝ} (ht : 0 < c - 2 * t) (a : ℝ) :
    ((RiemannGaussian.realPolynomialUpperRootMultiset
      (polyHeat t (X ^ 2 + C c))).map
        (fun z => logarithmicDepthThreshold a (z.im ^ 2 + 2 * t))).sum =
      logarithmicDepthThreshold a c := by
  rw [polyHeat_quadratic, upperRoots_quadratic ht]
  simp only [Multiset.map_singleton, Multiset.sum_singleton,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, Real.sq_sqrt ht.le, sub_add_cancel]

/-- Any clock coefficient above `2` violates some positive logarithmic threshold. -/
theorem logarithmic_elapsed_coefficient_is_sharp {k : ℝ} (hk : 2 < k) :
    ∃ p : ℝ[X], p ≠ 0 ∧ ∃ t a : ℝ, 0 < t ∧ 0 < a ∧
      ((RiemannGaussian.realPolynomialUpperRootMultiset p).map
        (fun z => logarithmicDepthThreshold a (z.im ^ 2))).sum <
      ((RiemannGaussian.realPolynomialUpperRootMultiset (polyHeat t p)).map
        (fun z => logarithmicDepthThreshold a (z.im ^ 2 + k * t))).sum := by
  refine ⟨X ^ 2 + C 1, ?_, 1 / 4, 1, by norm_num, by norm_num, ?_⟩
  · intro hp
    have h := congrArg (Polynomial.eval 0) hp
    norm_num at h
  · rw [upperRoots_quadratic (show (0 : ℝ) < 1 by norm_num), polyHeat_quadratic,
      upperRoots_quadratic (show (0 : ℝ) < 1 - 2 * (1 / 4) by norm_num)]
    simp only [Multiset.map_singleton, Multiset.sum_singleton,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 2 * (1 / 4) by norm_num)]
    have hlarge : 1 < 1 - 2 * (1 / 4 : ℝ) + k * (1 / 4) := by linarith only [hk]
    rw [logarithmicDepthThreshold_eq_zero (show (0 : ℝ) < 1 by norm_num) le_rfl,
      logarithmicDepthThreshold, div_one, max_eq_right hlarge.le]
    exact Real.log_pos hlarge

#print axioms polynomial_logarithmicThreshold_le_initial
#print axioms polynomial_upper_logarithmicThreshold_le_initial
#print axioms quadratic_upper_logarithmicThreshold_eq
#print axioms logarithmic_elapsed_coefficient_is_sharp

end
end GaloisForLFunctions.ArithmeticElectrostatics
