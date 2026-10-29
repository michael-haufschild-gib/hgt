import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZetaPoles
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform bounds for the finite-field zeta ratio

Cancelling the common rational pole gives an entire numerator and denominator.
The Weil circle excludes denominator zeros on a fixed small disk. Compactness
then bounds every root factor in a right half-plane, uniformly in its imaginary part.
-/

open Polynomial Filter Topology Metric Set

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- Numerator after cancelling the common pole at `T=1`. -/
def zetaRatioNumerator (T : ℂ) : ℂ := (1 - T / 3) * numerator.eval T

/-- Denominator after cancelling the common pole at `T=1`. -/
def zetaRatioDenominator (T : ℂ) : ℂ := (1 - 3 * T) * numerator.eval (T / 3)

/-- The reduced rational representative of the shifted zeta quotient. -/
def reducedZetaQuotient (T : ℂ) : ℂ := zetaRatioNumerator T / zetaRatioDenominator T

private lemma numerator_eval_analytic (T : ℂ) : AnalyticAt ℂ (fun z => numerator.eval z) T := by
  simpa using (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) T).aeval_polynomial numerator

lemma zetaRatioNumerator_analytic (T : ℂ) : AnalyticAt ℂ zetaRatioNumerator T := by
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 - z / 3) T).mul
    (numerator_eval_analytic T)

lemma zetaRatioDenominator_analytic (T : ℂ) : AnalyticAt ℂ zetaRatioDenominator T := by
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 1 - 3 * z) T).mul
    ((numerator_eval_analytic (T / 3)).comp (f := fun z : ℂ => z / 3) (by fun_prop))

/-- The only pointwise exception to the cancelled formula is the common pole. -/
theorem shiftedZetaQuotient_eq_reduced (T : ℂ) (hT : T ≠ 1) :
    shiftedZetaQuotient T = reducedZetaQuotient T := by
  have h₁ : 1 - T ≠ 0 := sub_ne_zero.mpr hT.symm
  unfold shiftedZetaQuotient zetaFunction reducedZetaQuotient
    zetaRatioNumerator zetaRatioDenominator
  rw [show (3 : ℂ) * (T / 3) = T by ring]
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div]
  rw [show numerator.eval T * ((1 - T / 3) * (1 - T)) =
      (1 - T) * ((1 - T / 3) * numerator.eval T) by ring,
    show ((1 - T) * (1 - 3 * T)) * numerator.eval (T / 3) =
      (1 - T) * ((1 - 3 * T) * numerator.eval (T / 3)) by ring]
  exact mul_div_mul_left _ _ h₁

lemma numerator_ne_zero_small_norm (T : ℂ) (hT : ‖T‖ ≤ 1 / 3) :
    numerator.eval T ≠ 0 := by
  intro hz
  have hroot := numerator_zero_norm_sq T hz
  nlinarith only [hroot, hT, norm_nonneg T]

lemma zetaRatioDenominator_ne_zero_small_norm (T : ℂ) (hT : ‖T‖ ≤ 1 / 9) :
    zetaRatioDenominator T ≠ 0 := by
  apply mul_ne_zero
  · intro hz
    have he : T = 1 / 3 := by linear_combination -(1 / 3 : ℂ) * hz
    rw [he] at hT
    norm_num [norm_div] at hT
  · apply numerator_ne_zero_small_norm
    rw [norm_div]
    norm_num only [Complex.norm_ofNat]
    linarith only [hT]

lemma reducedZetaQuotient_analytic_small_norm (T : ℂ) (hT : ‖T‖ ≤ 1 / 9) :
    AnalyticAt ℂ reducedZetaQuotient T :=
  (zetaRatioNumerator_analytic T).div (zetaRatioDenominator_analytic T)
    (zetaRatioDenominator_ne_zero_small_norm T hT)

/-- A fixed compact disk controls all sufficiently rightward spectral parameters. -/
theorem exists_reducedZetaQuotient_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ T : ℂ, ‖T‖ ≤ 1 / 9 → ‖reducedZetaQuotient T‖ ≤ B := by
  have hc : ContinuousOn reducedZetaQuotient (closedBall (0 : ℂ) (1 / 9)) := by
    intro T hT
    apply (reducedZetaQuotient_analytic_small_norm T ?_).continuousAt.continuousWithinAt
    simpa only [mem_closedBall, dist_zero_right] using hT
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (1 / 9)).exists_bound_of_continuousOn hc
  refine ⟨max B 1, le_max_right _ _, fun T hT => ?_⟩
  exact (hB T (by simpa only [mem_closedBall, dist_zero_right] using hT)).trans (le_max_left _ _)

lemma zetaCoordinate_norm (s : ℂ) :
    ‖zetaCoordinate s‖ = Real.exp (-Real.log 3 * s.re) := by
  simp only [zetaCoordinate, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

lemma zetaCoordinate_norm_le_ninth (s : ℂ) (hs : 2 ≤ s.re) :
    ‖zetaCoordinate s‖ ≤ 1 / 9 := by
  rw [zetaCoordinate_norm]
  calc
    Real.exp (-Real.log 3 * s.re) ≤ Real.exp (-(Real.log 3 + Real.log 3)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [log_three_pos, hs]
    _ = 1 / 9 := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      norm_num

lemma zetaCoordinate_norm_le_three (s : ℂ) (hs : -1 ≤ s.re) :
    ‖zetaCoordinate s‖ ≤ 3 := by
  rw [zetaCoordinate_norm]
  calc
    Real.exp (-Real.log 3 * s.re) ≤ Real.exp (Real.log 3) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [log_three_pos, hs]
    _ = 3 := Real.exp_log (by norm_num)

lemma zetaCoordinate_ne_one (s : ℂ) (hs : s.re ≠ 0) : zetaCoordinate s ≠ 1 := by
  intro h
  have he : Real.exp (-Real.log 3 * s.re) = Real.exp 0 := by
    rw [← zetaCoordinate_norm, h, norm_one, Real.exp_zero]
  have hz := Real.exp_injective he
  exact hs ((mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr log_three_pos.ne'))

/-- Entire numerator of the arithmetic quotient in its additive coordinate. -/
def arithmeticRatioNumerator (s : ℂ) : ℂ := zetaRatioNumerator (zetaCoordinate s)

/-- Entire denominator of the arithmetic quotient in its additive coordinate. -/
def arithmeticRatioDenominator (s : ℂ) : ℂ := zetaRatioDenominator (zetaCoordinate s)

/-- The reduced meromorphic representative of `ζ_F(s)/ζ_F(s+1)`. -/
def reducedArithmeticRatio (s : ℂ) : ℂ := reducedZetaQuotient (zetaCoordinate s)

lemma reducedArithmeticRatio_eq_div (s : ℂ) :
    reducedArithmeticRatio s = arithmeticRatioNumerator s / arithmeticRatioDenominator s := rfl

lemma reducedArithmeticRatio_eq (s : ℂ) (hs : s.re ≠ 0) :
    reducedArithmeticRatio s = arithmeticZetaRatio s := by
  rw [arithmeticZetaRatio_eq]
  exact (shiftedZetaQuotient_eq_reduced _ (zetaCoordinate_ne_one s hs)).symm

lemma arithmeticRatioNumerator_analytic (s : ℂ) : AnalyticAt ℂ arithmeticRatioNumerator s :=
  (zetaRatioNumerator_analytic (zetaCoordinate s)).comp (zetaCoordinate_analytic s)

lemma arithmeticRatioDenominator_analytic (s : ℂ) : AnalyticAt ℂ arithmeticRatioDenominator s :=
  (zetaRatioDenominator_analytic (zetaCoordinate s)).comp (zetaCoordinate_analytic s)

lemma reducedArithmeticRatio_analytic_right (s : ℂ) (hs : 2 ≤ s.re) :
    AnalyticAt ℂ reducedArithmeticRatio s :=
  (reducedZetaQuotient_analytic_small_norm _ (zetaCoordinate_norm_le_ninth s hs)).comp
    (zetaCoordinate_analytic s)

/-- Uniform right-half-plane control follows from the actual finite-field rational zeta function. -/
theorem exists_reducedArithmeticRatio_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, 2 ≤ s.re → ‖reducedArithmeticRatio s‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_reducedZetaQuotient_bound
  exact ⟨B, hB, fun s hs => hb _ (zetaCoordinate_norm_le_ninth s hs)⟩

/-- A single constant bounds the entire numerator and denominator on the continuation strip. -/
theorem exists_arithmeticRatio_parts_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, -1 ≤ s.re →
      ‖arithmeticRatioNumerator s‖ ≤ B ∧ ‖arithmeticRatioDenominator s‖ ≤ B := by
  have hn : ContinuousOn zetaRatioNumerator (closedBall (0 : ℂ) 3) :=
    fun T _ => (zetaRatioNumerator_analytic T).continuousAt.continuousWithinAt
  have hd : ContinuousOn zetaRatioDenominator (closedBall (0 : ℂ) 3) :=
    fun T _ => (zetaRatioDenominator_analytic T).continuousAt.continuousWithinAt
  obtain ⟨N, hN⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn hn
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : ℂ) 3).exists_bound_of_continuousOn hd
  refine ⟨max 1 (max N D), le_max_left _ _, fun s hs => ?_⟩
  have hmem : zetaCoordinate s ∈ closedBall (0 : ℂ) 3 := by
    simpa only [mem_closedBall, dist_zero_right] using zetaCoordinate_norm_le_three s hs
  exact ⟨(hN _ hmem).trans ((le_max_left N D).trans (le_max_right _ _)),
    (hD _ hmem).trans ((le_max_right N D).trans (le_max_right _ _))⟩

/-- Clearing an arithmetic denominator zero leaves a nonzero numerator. -/
theorem arithmeticRatioNumerator_ne_zero_at_root (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    arithmeticRatioNumerator s ≠ 0 := by
  have he : zetaCoordinate s = 3 * zetaCoordinate (s + 1) := by
    rw [zetaCoordinate_add_one]
    ring
  change (1 - zetaCoordinate s / 3) * numerator.eval (zetaCoordinate s) ≠ 0
  rw [← zetaCoordinate_add_one]
  refine mul_ne_zero ((mul_ne_zero_iff.mp (reciprocal_numerator_nonzero _ hs)).1) ?_
  rw [he]
  exact numerator_at_scaled_root_ne_zero _ hs

lemma arithmeticRatioDenominator_zero_at_root (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    arithmeticRatioDenominator s = 0 := by
  change (1 - 3 * zetaCoordinate s) * numerator.eval (zetaCoordinate s / 3) = 0
  rw [← zetaCoordinate_add_one, hs, mul_zero]

/-- The common denominator has precisely the original Frobenius-root multiplicity. -/
theorem arithmeticRatioDenominator_order_at_root (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    meromorphicOrderAt arithmeticRatioDenominator s =
      ((numerator.rootMultiplicity (zetaCoordinate (s + 1)) : ℤ) : WithTop ℤ) := by
  have he : zetaCoordinate s = 3 * zetaCoordinate (s + 1) := by
    rw [zetaCoordinate_add_one]
    ring
  have hu : AnalyticAt ℂ (fun z : ℂ => 1 - 3 * zetaCoordinate z) s := by
    unfold zetaCoordinate
    fun_prop
  have hu0 : 1 - 3 * zetaCoordinate s ≠ 0 := by
    rw [he]
    exact (mul_ne_zero_iff.mp (denominator_at_scaled_root_ne_zero _ hs)).2
  have huo : meromorphicOrderAt (fun z : ℂ => 1 - 3 * zetaCoordinate z) s = 0 := by
    rw [hu.meromorphicOrderAt_eq, hu.analyticOrderAt_eq_zero.mpr hu0]
    rfl
  have hg : AnalyticAt ℂ (fun z : ℂ => zetaCoordinate z / 3) s := by
    unfold zetaCoordinate
    fun_prop
  have hgd : deriv (fun z : ℂ => zetaCoordinate z / 3) s ≠ 0 := by
    rw [((zetaCoordinate_analytic s).differentiableAt.hasDerivAt.div_const 3).deriv]
    exact div_ne_zero (zetaCoordinate_deriv_ne_zero s) (by norm_num)
  have hp := (numerator_eval_analytic (zetaCoordinate s / 3)).comp
    (f := fun z : ℂ => zetaCoordinate z / 3) hg
  have horder : meromorphicOrderAt (fun z => numerator.eval (zetaCoordinate z / 3)) s =
      meromorphicOrderAt (fun z => numerator.eval z) (zetaCoordinate s / 3) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := fun z => numerator.eval z) (g := fun z : ℂ => zetaCoordinate z / 3) hg hgd
  have hmul : meromorphicOrderAt arithmeticRatioDenominator s =
      meromorphicOrderAt (fun z : ℂ => 1 - 3 * zetaCoordinate z) s +
        meromorphicOrderAt (fun z => numerator.eval (zetaCoordinate z / 3)) s := by
    convert! meromorphicOrderAt_mul hu.meromorphicAt hp.meromorphicAt using 1
  rw [hmul, huo, zero_add, horder, numerator_meromorphicOrder, ← zetaCoordinate_add_one]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
