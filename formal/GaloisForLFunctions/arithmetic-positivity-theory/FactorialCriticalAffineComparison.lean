import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineFrequencyIntervals
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialPhaseWindowAndPhysicalRieszBounds

/-! Whole-span comparison with the affine clock `N+1/12` at the critical physical
weight. Exact harmonic interval energies and the existing weighted-series bound
control the complete profile error by the inverse-scale coefficient mass. -/

open MeasureTheory Set Filter
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

private def criticalAffineMeasure : Measure ℝ :=
  (volume.restrict (Ioi (1 : ℝ))).withDensity fun v => ENNReal.ofReal ((v ^ 2)⁻¹)

private theorem criticalAffineWeight_integrable :
    IntegrableOn (fun v : ℝ => (v ^ 2)⁻¹) (Ioi (1 : ℝ)) := by
  have h := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.rpow_neg (zero_lt_one.trans hv).le, Real.rpow_two]

private instance : IsFiniteMeasure criticalAffineMeasure :=
  isFiniteMeasure_withDensity_ofReal criticalAffineWeight_integrable.2

private theorem criticalAffineMeasure_integral (g : ℝ → ℝ) :
    (∫ v, g v ∂criticalAffineMeasure) = ∫ v in Ioi (1 : ℝ), g v / v ^ 2 := by
  unfold criticalAffineMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun v => ENNReal.ofReal_lt_top) g]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg v)), smul_eq_mul]
  ring

private def affineComparisonWeight (k : ℕ) : ℝ :=
  dyadicHarmonicWeight (k+1) * Real.sqrt ((k+1 : ℕ) : ℝ)

private theorem affineComparisonWeight_summable :
    Summable fun k => |affineComparisonWeight k| := by
  have hs : Summable fun k : ℕ => (((k+1 : ℕ) : ℝ) ^ (-(3/2) : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hs
  have hk : 0 < ((k+1 : ℕ) : ℝ) := by positivity
  unfold affineComparisonWeight
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |dyadicHarmonicWeight (k+1)| * Real.sqrt ((k+1 : ℕ) : ℝ)
      ≤ (1 / ((k+1 : ℕ) : ℝ)^2) * Real.sqrt ((k+1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (abs_dyadicHarmonicWeight_le (k+1))
          (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_two, one_div, ← Real.rpow_neg hk.le,
        ← Real.rpow_add hk]
      congr 1
      norm_num

private def affineNormalizedLayer (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  factorialAffineHarmonicError S b (k+1) v / (Real.sqrt ((k+1 : ℕ) : ℝ) : ℂ)

private theorem affineNormalizedLayer_continuous (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    Continuous (affineNormalizedLayer S b k) := by
  unfold affineNormalizedLayer factorialAffineHarmonicError
  fun_prop

private theorem affineNormalizedLayer_bound (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) (v : ℝ) :
    ‖affineNormalizedLayer S b k v‖ ≤ 2 * ∑ n ∈ S, ‖b n‖ := by
  have hb : ‖factorialAffineHarmonicError S b (k+1) v‖ ≤ 2 * ∑ n ∈ S, ‖b n‖ := by
    unfold factorialAffineHarmonicError
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcos : |Real.cos (2*Real.pi*(k+1)*(factorialShiftedFreq (n+1)*v)) -
        Real.cos (2*Real.pi*(k+1)*((((n+1 : ℕ) : ℝ)+1/12)*v))| ≤ 2 := by
      refine (abs_sub _ _).trans ?_
      calc _ ≤ 1+1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
           _ = 2 := by norm_num
    push_cast at hcos ⊢
    calc _ ≤ ‖b n‖ * 2 := mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
         _ = _ := by ring
  have hk : (1 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ))
  have hs : 1 ≤ Real.sqrt ((k+1 : ℕ) : ℝ) := by
    nlinarith [Real.sqrt_nonneg (((k+1 : ℕ) : ℝ))]
  unfold affineNormalizedLayer
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt ((k+1 : ℕ) : ℝ))).2
  exact hb.trans (by nlinarith [Finset.sum_nonneg (fun n (_ : n ∈ S) => norm_nonneg (b n))])

private theorem affineNormalizedLayer_energy (S : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) :
    (∫ v, ‖affineNormalizedLayer S b k v‖ ^ 2 ∂criticalAffineMeasure) ≤
      Real.pi ^ 2 * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
  have hk : 0 < ((k+1 : ℕ) : ℝ) := by positivity
  have he (v : ℝ) : ‖affineNormalizedLayer S b k v‖ ^ 2 / v ^ 2 =
      (1 / ((k+1 : ℕ) : ℝ)) *
        (‖factorialAffineHarmonicError S b (k+1) v‖ ^ 2 / v ^ 2) := by
    unfold affineNormalizedLayer
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hk.le]
    ring
  rw [criticalAffineMeasure_integral]
  simp_rw [he]
  rw [integral_const_mul]
  calc (1 / ((k+1 : ℕ) : ℝ)) *
      (∫ v in Ioi (1 : ℝ), ‖factorialAffineHarmonicError S b (k+1) v‖ ^ 2 / v ^ 2)
      ≤ (1 / ((k+1 : ℕ) : ℝ)) *
        (Real.pi ^ 2 * (k+1) * ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul_of_nonneg_left (critical_factorialAffineHarmonicError_le S b (k+1))
            (one_div_nonneg.mpr hk.le)
    _ = _ := by push_cast; field_simp

/-- The affine clock model retains both the integer and shifted Bernoulli branches. -/
def factorialAffinePhaseCombination (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) : ℂ :=
  ∑ n ∈ S, b n * ((dyadicCenteredBernoulliFilter ((((n+1 : ℕ) : ℝ)+1/12)*v) -
    dyadicCenteredBernoulliFilter (((n+1 : ℕ) : ℝ)*v) : ℝ) : ℂ)

private theorem factorialAffineDifference_eq (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    factorialPhaseCombination S b v - factorialAffinePhaseCombination S b v =
      ∑ n ∈ S, b n * ((dyadicCenteredBernoulliFilter (factorialShiftedFreq (n+1)*v) -
        dyadicCenteredBernoulliFilter ((((n+1 : ℕ) : ℝ)+1/12)*v) : ℝ) : ℂ) := by
  unfold factorialPhaseCombination factorialAffinePhaseCombination
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [factorialPhaseProfile_eq_centered]
  push_cast
  ring

private theorem factorialAffineDifference_hasSum (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    HasSum (fun k => (dyadicHarmonicWeight k : ℂ) * factorialAffineHarmonicError S b k v)
      (-((Real.pi ^ 2 / 2 : ℝ) : ℂ) *
        (factorialPhaseCombination S b v - factorialAffinePhaseCombination S b v)) := by
  have hn (n : ℕ) :=
    ((dyadicCenteredBernoulliFilter_hasSum (factorialShiftedFreq (n+1)*v)).sub
      (dyadicCenteredBernoulliFilter_hasSum ((((n+1 : ℕ) : ℝ)+1/12)*v)))
  have hh := hasSum_sum (s := S) fun n _ =>
    (Complex.hasSum_ofReal.mpr (hn n)).mul_left (b n)
  apply hasSum_of_eq_of_eq hh
  · intro k
    unfold dyadicHarmonicWeight factorialAffineHarmonicError
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  · rw [factorialAffineDifference_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring

private theorem factorialAffineDifference_eq_tsum
    (S : Finset ℕ) (b : ℕ → ℂ) (v : ℝ) :
    factorialPhaseCombination S b v - factorialAffinePhaseCombination S b v =
      -((2 / Real.pi ^ 2 : ℝ) : ℂ) *
        ∑' k, (affineComparisonWeight k : ℂ) * affineNormalizedLayer S b k v := by
  have h := factorialAffineDifference_hasSum S b v
  have hs : HasSum (fun k => (dyadicHarmonicWeight (k+1) : ℂ) *
      factorialAffineHarmonicError S b (k+1) v)
      (-((Real.pi ^ 2 / 2 : ℝ) : ℂ) *
        (factorialPhaseCombination S b v - factorialAffinePhaseCombination S b v)) := by
    apply (hasSum_nat_add_iff (f := fun k : ℕ =>
      (dyadicHarmonicWeight k : ℂ) * factorialAffineHarmonicError S b k v) 1).2
    simpa [dyadicHarmonicWeight] using h
  have he (k : ℕ) : (affineComparisonWeight k : ℂ) * affineNormalizedLayer S b k v =
      (dyadicHarmonicWeight (k+1) : ℂ) * factorialAffineHarmonicError S b (k+1) v := by
    have hsqrt : Real.sqrt ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hc : (Real.sqrt ((k+1 : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqrt
    unfold affineComparisonWeight affineNormalizedLayer
    push_cast
    field_simp
  simp_rw [he]
  rw [hs.tsum_eq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- Universal coefficient in the critical affine comparison; the defining series converges. -/
def factorialAffineComparisonConstant : ℝ :=
  (4 / Real.pi ^ 2) *
    (∑' k : ℕ, |dyadicHarmonicWeight (k+1) * Real.sqrt ((k+1 : ℕ) : ℝ)|) ^ 2

private theorem factorialAffineComparison_core (S : Finset ℕ) (b : ℕ → ℂ) :
    Integrable (fun v => ‖factorialPhaseCombination S b v -
      factorialAffinePhaseCombination S b v‖ ^ 2) criticalAffineMeasure ∧
    (∫ v, ‖factorialPhaseCombination S b v - factorialAffinePhaseCombination S b v‖ ^ 2
      ∂criticalAffineMeasure) ≤
      factorialAffineComparisonConstant *
        ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
  let E : ℝ := ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2
  let W : ℝ := ∑' k, |affineComparisonWeight k|
  have hW : 0 ≤ W := tsum_nonneg fun _ => abs_nonneg _
  have h := integral_norm_tsum_weighted_sq_le (μ := criticalAffineMeasure)
    affineComparisonWeight_summable (affineNormalizedLayer_continuous S b)
    (affineNormalizedLayer_bound S b)
  have hN (v : ℝ) :
      ‖factorialPhaseCombination S b v - factorialAffinePhaseCombination S b v‖ ^ 2 =
      (4 / Real.pi ^ 4) *
        ‖∑' k, (affineComparisonWeight k : ℂ) * affineNormalizedLayer S b k v‖ ^ 2 := by
    rw [factorialAffineDifference_eq_tsum, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    ring
  refine ⟨(h.1.const_mul _).congr (Eventually.of_forall fun v => (hN v).symm), ?_⟩
  simp_rw [hN]
  rw [integral_const_mul]
  have hsI : Summable fun k => |affineComparisonWeight k| *
      ∫ v, ‖affineNormalizedLayer S b k v‖ ^ 2 ∂criticalAffineMeasure :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (abs_nonneg _) (integral_nonneg fun v => sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_left (affineNormalizedLayer_energy S b k) (abs_nonneg _))
      (affineComparisonWeight_summable.mul_right (Real.pi ^ 2 * E))
  have hsum : (∑' k, |affineComparisonWeight k| *
      ∫ v, ‖affineNormalizedLayer S b k v‖ ^ 2 ∂criticalAffineMeasure) ≤
      W * (Real.pi ^ 2 * E) := by
    rw [show W * (Real.pi ^ 2 * E) =
      ∑' k, |affineComparisonWeight k| * (Real.pi ^ 2 * E) by rw [tsum_mul_right]]
    exact hsI.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (affineNormalizedLayer_energy S b k) (abs_nonneg _))
      (affineComparisonWeight_summable.mul_right _)
  calc (4 / Real.pi ^ 4) *
      (∫ v, ‖∑' k, (affineComparisonWeight k : ℂ) * affineNormalizedLayer S b k v‖ ^ 2
        ∂criticalAffineMeasure)
      ≤ (4 / Real.pi ^ 4) * (W * (W * (Real.pi ^ 2 * E))) := by
        exact mul_le_mul_of_nonneg_left
          (h.2.trans (mul_le_mul_of_nonneg_left hsum hW)) (by positivity)
    _ = _ := by
      change _ = ((4 / Real.pi ^ 2) * W ^ 2) * E
      field_simp

/-- The whole critical affine error is a genuine integrable physical energy. -/
theorem integrable_critical_factorialAffineDifference (S : Finset ℕ) (b : ℕ → ℂ) :
    IntegrableOn (fun v => ‖factorialPhaseCombination S b v -
      factorialAffinePhaseCombination S b v‖ ^ 2 / v ^ 2) (Ioi (1 : ℝ)) := by
  have h := (factorialAffineComparison_core S b).1
  unfold criticalAffineMeasure at h
  have hi := (integrable_withDensity_iff (by fun_prop)
    (Eventually.of_forall fun v => ENNReal.ofReal_lt_top)).1 h
  exact hi.congr (Eventually.of_forall fun v => by
    dsimp only
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg v))]
    rfl)

/-- Whole-source critical comparison, with the exact native defect on the coefficient side. -/
theorem factorial_critical_affine_error_bound (S : Finset ℕ) (b : ℕ → ℂ) :
    (∫ v in Ioi (1 : ℝ), ‖factorialPhaseCombination S b v -
      factorialAffinePhaseCombination S b v‖ ^ 2 / v ^ 2) ≤
      factorialAffineComparisonConstant *
        ∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2 := by
  rw [← criticalAffineMeasure_integral]
  exact (factorialAffineComparison_core S b).2

/-- The affine model has a support-independent inverse-scale error on the full native span. -/
theorem factorial_critical_affine_error_weighted_bound (S : Finset ℕ) (b : ℕ → ℂ) :
    (∫ v in Ioi (1 : ℝ), ‖factorialPhaseCombination S b v -
      factorialAffinePhaseCombination S b v‖ ^ 2 / v ^ 2) ≤
      (factorialAffineComparisonConstant / 140) *
        ∑ n ∈ S, ‖b n‖ ^ 2 / ((n+1 : ℕ) : ℝ) := by
  refine (factorial_critical_affine_error_bound S b).trans ?_
  have hC : 0 ≤ factorialAffineComparisonConstant := by
    unfold factorialAffineComparisonConstant
    positivity
  calc factorialAffineComparisonConstant *
      (∑ n ∈ S, factorialAffineDefect (n+1) * ‖b n‖ ^ 2)
      ≤ factorialAffineComparisonConstant *
        (∑ n ∈ S, (1/(140*((n : ℝ)+1))) * ‖b n‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Finset.sum_le_sum fun n hn =>
          mul_le_mul_of_nonneg_right (factorialAffineDefect_bounds n).2 (sq_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ)+1 ≠ 0 := by positivity
      push_cast
      field_simp

/-- Uniform high-scale comparison, with no restriction on the size of the finite source family. -/
theorem factorial_critical_affine_error_tail_bound
    (S : Finset ℕ) (b : ℕ → ℂ) (m : ℕ) :
    (∫ v in Ioi (1 : ℝ),
      ‖factorialPhaseCombination (S.filter (fun n => m ≤ n)) b v -
        factorialAffinePhaseCombination (S.filter (fun n => m ≤ n)) b v‖ ^ 2 / v ^ 2) ≤
      (factorialAffineComparisonConstant / (140 * ((m+1 : ℕ) : ℝ))) *
        ∑ n ∈ S, ‖b n‖ ^ 2 := by
  let T := S.filter (fun n => m ≤ n)
  have hm : 0 < ((m+1 : ℕ) : ℝ) := by positivity
  have hC : 0 ≤ factorialAffineComparisonConstant := by
    unfold factorialAffineComparisonConstant
    positivity
  refine (factorial_critical_affine_error_weighted_bound T b).trans ?_
  have hsum : (∑ n ∈ T, ‖b n‖ ^ 2) ≤ ∑ n ∈ S, ‖b n‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n hn hnT => sq_nonneg _)
  calc (factorialAffineComparisonConstant / 140) *
      (∑ n ∈ T, ‖b n‖ ^ 2 / ((n+1 : ℕ) : ℝ))
      ≤ (factorialAffineComparisonConstant / 140) *
        (∑ n ∈ T, ‖b n‖ ^ 2 / ((m+1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hC (by norm_num))
        apply Finset.sum_le_sum
        intro n hn
        have hmn : m ≤ n := (Finset.mem_filter.mp hn).2
        exact div_le_div_of_nonneg_left (sq_nonneg _) hm (by exact_mod_cast Nat.add_le_add_right hmn 1)
    _ = (factorialAffineComparisonConstant / (140 * ((m+1 : ℕ) : ℝ))) *
        (∑ n ∈ T, ‖b n‖ ^ 2) := by
        rw [← Finset.sum_div]
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (div_nonneg hC (by positivity))

end
end GaloisForLFunctions.ArithmeticPositivityTheory
