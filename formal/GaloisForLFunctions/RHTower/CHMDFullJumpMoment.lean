import GaloisForLFunctions.RHTower.CHMDDoobSourceGraph
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# Integrable displacement for the complete CHMD jump measure

The entire prime measure has finite mass and finite second displacement moment.
The archimedean measure has finite second displacement moment despite its diagonal
singularity. These facts are used for graph-domain cutoffs, not a primitive sign bound.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem theta_global_and_exponential_bound :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, riemannKernelReal x ≤ C) ∧
      ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * x)) := by
  obtain ⟨C, hC, hb⟩ := exists_riemannKernelReal_le
  refine ⟨C, hC, fun x => (hb x).trans ?_, fun x => (hb x).trans ?_⟩
  · exact mul_le_of_le_one_right hC
      (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x]))
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [le_abs_self x])) hC

theorem prime_coefficient_moment_bound (n : ℕ) :
    vonMangoldtAtom n * (1 + Real.log n ^ 2) * Real.exp (-(4 * Real.log n)) ≤
      2 * (|ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2) := by
  by_cases hn : 2 ≤ n
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hn0 : (0 : ℝ) < n := by linarith
    have hs : 1 ≤ Real.sqrt n := by
      simpa using Real.sqrt_le_sqrt hn1
    have ha : vonMangoldtAtom n ≤ ArithmeticFunction.vonMangoldt n := by
      rw [vonMangoldtAtom, if_pos hn]
      exact div_le_self ArithmeticFunction.vonMangoldt_nonneg hs
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hl : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
    have hq : 1 + Real.log n ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have he : Real.exp (-(4 * Real.log n)) = ((n : ℝ) ^ 4)⁻¹ := by
      rw [Real.exp_neg, show 4 * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ 4) by
        rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hn0 4)]
    rw [he, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc
      _ ≤ ArithmeticFunction.vonMangoldt n * (2 * (n : ℝ) ^ 2) *
          ((n : ℝ) ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul ha hq (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
          (by positivity)
      _ = _ := by field_simp
  · rw [vonMangoldtAtom, if_neg hn]
    simp only [zero_mul]
    positivity

theorem prime_weight_moment_bound {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * x))) (n : ℕ) (x : ℝ) :
    primeWeight n x * (1 + Real.log n ^ 2) ≤
      (2 * C * (|ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2)) *
        (riemannKernelReal x * Real.exp (-4 * x)) := by
  have hθ := riemannKernelReal_pos x
  calc
    _ ≤ vonMangoldtAtom n * riemannKernelReal x *
        (C * Real.exp (-(4 * (x + Real.log n)))) * (1 + Real.log n ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb _) (mul_nonneg (vonMangoldtAtom_nonneg n) hθ.le))
        (by positivity)
    _ = (C * (riemannKernelReal x * Real.exp (-4 * x))) *
        (vonMangoldtAtom n * (1 + Real.log n ^ 2) * Real.exp (-(4 * Real.log n))) := by
      rw [show -(4 * (x + Real.log n)) = -4 * x + -(4 * Real.log n) by ring,
        Real.exp_add]
      ring
    _ ≤ (C * (riemannKernelReal x * Real.exp (-4 * x))) *
        (2 * (|ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (prime_coefficient_moment_bound n) (by positivity)
    _ = _ := by ring

theorem integrable_prime_weight_moment (n : ℕ) :
    Integrable (fun x => primeWeight n x * (1 + Real.log n ^ 2)) := by
  obtain ⟨C, hC, _, hb⟩ := theta_global_and_exponential_bound
  refine ((integrable_riemannKernelReal_mul_exp (-4)).const_mul
    (2 * C * (|ArithmeticFunction.vonMangoldt n| / (n : ℝ) ^ 2))).mono'
      ((continuous_primeWeight n).mul continuous_const).aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (mul_nonneg (primeWeight_nonneg n x) (by positivity))]
    exact prime_weight_moment_bound hC hb n x

theorem integrable_prime_displacement (n : ℕ) :
    Integrable (fun e : ℝ × ℝ => 1 + e.1 ^ 2) (primeMeasure n) := by
  rw [primeMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    integrable_weighted_iff volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n))]
  exact integrable_prime_weight_moment n

theorem summable_integral_prime_displacement :
    Summable (fun n => ∫ e : ℝ × ℝ, ‖1 + e.1 ^ 2‖ ∂primeMeasure n) := by
  obtain ⟨C, hC, _, hb⟩ := theta_global_and_exponential_bound
  have hs := (summable_vonMangoldt_abs_div_sq.mul_left (2 * C)).mul_right
    (∫ x, riemannKernelReal x * Real.exp (-4 * x))
  apply hs.of_nonneg_of_le (fun n => integral_nonneg fun e => norm_nonneg _) (fun n => ?_)
  have hnorm (e : ℝ × ℝ) : ‖1 + e.1 ^ 2‖ = 1 + e.1 ^ 2 :=
    Real.norm_of_nonneg (by positivity)
  simp_rw [hnorm]
  rw [primeMeasure, integral_map (by fun_prop) (by fun_prop),
    integral_weighted volume (continuous_primeWeight n).measurable
      (Eventually.of_forall (primeWeight_nonneg n)), ← integral_const_mul]
  exact integral_mono (integrable_prime_weight_moment n)
    ((integrable_riemannKernelReal_mul_exp (-4)).const_mul _) (prime_weight_moment_bound hC hb n)

theorem integrable_full_prime_displacement :
    Integrable (fun e : ℝ × ℝ => 1 + e.1 ^ 2) (Measure.sum primeMeasure) :=
  integrable_sum_measure integrable_prime_displacement summable_integral_prime_displacement

instance finite_full_prime_measure : IsFiniteMeasure (Measure.sum primeMeasure) := by
  apply (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
  exact integrable_full_prime_displacement.mono' (by fun_prop)
    (Eventually.of_forall fun e => by simp only [norm_one]; linarith [sq_nonneg e.1])

theorem integrable_arch_displacement_sq :
    Integrable (fun e : ℝ × ℝ => e.1 ^ 2) archMeasure := by
  obtain ⟨C, hC, hb, _⟩ := theta_global_and_exponential_bound
  rw [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
  have hi := (integrableOn_sq_mul_archLevyDensity.mul_prod integrable_riemannKernelReal).const_mul C
  refine hi.mono' (measurable_archWeight.mul (measurable_fst.pow_const 2)).aestronglyMeasurable ?_
  have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ht, archWeight_nonneg_ae] with e he hw
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  change archLevyDensity e.1 * riemannKernelReal e.2 *
    riemannKernelReal (e.2 + e.1) * e.1 ^ 2 ≤ C * ((e.1 ^ 2 * archLevyDensity e.1) * riemannKernelReal e.2)
  nlinarith [mul_le_mul_of_nonneg_left (hb (e.2 + e.1))
    (show 0 ≤ e.1 ^ 2 * archLevyDensity e.1 * riemannKernelReal e.2 by
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (archLevyDensity_pos he).le)
        (riemannKernelReal_pos _).le)]

/-- The literal displacement belongs to the full edge L2 space. -/
theorem memLp_displacement : MemLp (fun e : ℝ × ℝ => e.1) 2 edgeMeasure := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  exact integrable_arch_displacement_sq.add_measure
    (integrable_full_prime_displacement.mono' (by fun_prop)
      (Eventually.of_forall fun e => by rw [Real.norm_of_nonneg (sq_nonneg _)]; linarith))

end RHTower.CHMDDoobGraph
