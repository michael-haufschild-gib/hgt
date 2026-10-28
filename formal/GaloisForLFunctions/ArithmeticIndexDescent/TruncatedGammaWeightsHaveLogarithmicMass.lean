import GaloisForLFunctions.ArithmeticIndexDescent.TheGammaBoundaryBoundHasNoNonzeroEqualityCase
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Boundary truncations of the exact Gamma weight

Cutting the exact Schur weight to a compact interval away from zero gives
vectors in the original half-line L2 space. Their square masses grow at least
logarithmically as the inner endpoint approaches the boundary.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProduct
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

theorem continuousOn_gammaBoundarySchurWeight :
    ContinuousOn gammaBoundarySchurWeight (Ioi (0 : ℝ)) := by
  unfold gammaBoundarySchurWeight
  refine (by fun_prop : Continuous (fun t : ℝ => Real.exp (t / 2))).continuousOn.div
    (by fun_prop : Continuous (fun t : ℝ => Real.sqrt (Real.exp (2 * t) - 1))).continuousOn ?_
  intro t ht
  apply (Real.sqrt_pos.mpr ?_).ne'
  exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) ht))

/-- The critical weight cut off between a positive inner boundary and unit scale. -/
def truncatedGammaWeightFun (a : ℝ) : ℝ → ℂ :=
  (Ioc a 1).indicator (fun t => (gammaBoundarySchurWeight t : ℂ))

theorem memLp_truncatedGammaWeightFun {a : ℝ} (ha : 0 < a) :
    MemLp (truncatedGammaWeightFun a) 2 μ₊ := by
  have hs : HasCompactSupport (truncatedGammaWeightFun a) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := 1)) fun t ht => ?_
    exact indicator_of_notMem (fun h => ht ⟨h.1.le, h.2⟩) _
  have hc : ContinuousOn (fun t => (gammaBoundarySchurWeight t : ℂ)) (Icc a 1) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_gammaBoundarySchurWeight.mono fun _ ht => ha.trans_le ht.1)
  have hm : Measurable (fun t => (gammaBoundarySchurWeight t : ℂ)) := by
    unfold gammaBoundarySchurWeight
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := 1)).exists_bound_of_continuousOn hc
  have hv : MemLp (truncatedGammaWeightFun a) 2 (volume : Measure ℝ) := by
    apply hs.memLp_of_bound (hm.indicator measurableSet_Ioc).aestronglyMeasurable (max C 0)
    filter_upwards with t
    by_cases ht : t ∈ Ioc a 1
    · rw [truncatedGammaWeightFun, indicator_of_mem ht]
      exact (hC t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)
    · rw [truncatedGammaWeightFun, indicator_of_notMem ht, norm_zero]
      exact le_max_right _ _
  exact hv.mono_measure Measure.restrict_le_self

/-- Actual half-line L2 vectors obtained from boundary truncation. -/
def truncatedGammaWeight (a : ℝ) (ha : 0 < a) : SuzukiPositiveL2 :=
  (memLp_truncatedGammaWeightFun ha).toLp (truncatedGammaWeightFun a)

theorem truncatedGammaWeight_coeFn {a : ℝ} (ha : 0 < a) :
    (truncatedGammaWeight a ha : ℝ → ℂ) =ᵐ[μ₊] truncatedGammaWeightFun a :=
  (memLp_truncatedGammaWeightFun ha).coeFn_toLp

theorem integrableOn_gammaBoundarySchurWeight_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => gammaBoundarySchurWeight t ^ 2) (Ioc a 1) := by
  have hc : ContinuousOn (fun t => gammaBoundarySchurWeight t ^ 2) (Icc a 1) :=
    (continuousOn_gammaBoundarySchurWeight.mono fun _ ht => ha.trans_le ht.1).pow 2
  exact (hc.integrableOn_compact isCompact_Icc).mono_set fun _ ht => ⟨ht.1.le, ht.2⟩

/-- The L2 truncation retains exactly the square mass of its literal weight. -/
theorem norm_truncatedGammaWeight_sq {a : ℝ} (ha : 0 < a) :
    ‖truncatedGammaWeight a ha‖ ^ 2 =
      ∫ t in Ioc a 1, gammaBoundarySchurWeight t ^ 2 := by
  have key := inner_self_eq_norm_sq (𝕜 := ℂ) (truncatedGammaWeight a ha)
  rw [L2.inner_def] at key
  have hint : (∫ t in Ioi (0 : ℝ),
      inner ℂ (truncatedGammaWeight a ha t) (truncatedGammaWeight a ha t)) =
      ((∫ t in Ioi (0 : ℝ), ‖truncatedGammaWeightFun a t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [truncatedGammaWeight_coeFn ha] with t ht
    rw [ht, RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hint] at key
  have hn : ‖truncatedGammaWeight a ha‖ ^ 2 =
      ∫ t in Ioi (0 : ℝ), ‖truncatedGammaWeightFun a t‖ ^ 2 := by
    simpa using key.symm
  rw [hn]
  have he : (fun t => ‖truncatedGammaWeightFun a t‖ ^ 2) =
      (Ioc a 1).indicator (fun t => gammaBoundarySchurWeight t ^ 2) := by
    funext t
    by_cases ht : t ∈ Ioc a 1
    · simp only [truncatedGammaWeightFun, indicator_of_mem ht,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · simp only [truncatedGammaWeightFun, indicator_of_notMem ht,
        norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [he, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    show Ioc a 1 ∩ Ioi (0 : ℝ) = Ioc a 1 from
      inter_eq_left.mpr (fun _ ht => ha.trans ht.1)]

/-- The truncated actual L2 mass grows at least logarithmically at the boundary. -/
theorem norm_truncatedGammaWeight_sq_ge_log {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (Real.exp (-1) / 2) * Real.log (1 / a) ≤ ‖truncatedGammaWeight a ha‖ ^ 2 := by
  have hi := integrableOn_gammaBoundarySchurWeight_sq ha
  have hs : IntegrableOn (fun t : ℝ => (Real.exp (-1) / 2) * t⁻¹) (Ioc a 1) := by
    refine hi.mono' (measurable_const.mul measurable_inv).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ha.trans ht.1
    rw [Real.norm_of_nonneg (by positivity)]
    exact gammaBoundarySchurWeight_sq_ge_inv ht0 ht.2
  have hle := setIntegral_mono_on hs hi measurableSet_Ioc
    (fun t ht => gammaBoundarySchurWeight_sq_ge_inv (ha.trans ht.1) ht.2)
  rwa [integral_const_mul, ← intervalIntegral.integral_of_le ha1,
    integral_inv_of_pos ha (by norm_num : (0 : ℝ) < 1),
    ← norm_truncatedGammaWeight_sq ha] at hle

/-- Exponential cutoffs provide an explicit unbounded sequence of square masses. -/
theorem norm_truncatedGammaWeight_exp_sq_ge (n : ℕ) :
    (Real.exp (-1) / 2) * ((n : ℝ) + 1) ≤
      ‖truncatedGammaWeight (Real.exp (-((n : ℝ) + 1))) (Real.exp_pos _)‖ ^ 2 := by
  have hle : Real.exp (-((n : ℝ) + 1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have h := norm_truncatedGammaWeight_sq_ge_log (Real.exp_pos (-((n : ℝ) + 1))) hle
  simpa only [one_div, Real.log_inv, Real.log_exp, neg_neg] using h

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_truncatedGammaWeight_sq
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_truncatedGammaWeight_sq_ge_log
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_truncatedGammaWeight_exp_sq_ge
