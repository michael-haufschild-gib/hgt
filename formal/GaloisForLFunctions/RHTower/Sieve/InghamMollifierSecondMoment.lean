import GaloisForLFunctions.RHTower.Sieve.InghamCriticalMoment
import GaloisForLFunctions.RHTower.ZeroDetectionEM
import GaloisForLFunctions.RHTower.Sieve.DirichletPolyAffineMeanSquare

/-!
# Quantitative second moment of Ingham's Möbius mollifier

On the critical line, the finite Möbius mollifier is a finitely supported Dirichlet series with
coefficients `μ(n)n⁻¹ᐟ²`.  Its plain coefficient mass is at most the harmonic sum `1 + log X`, while
its `n`-weighted mass is at most `X`.  The general affine mean-square theorem therefore gives the
unconditional explicit estimate

`∫_{-T}^T |M_X(1/2+it)|² dt ≤ 5πe X + (5π/2)(1+log X)T`.

The final theorem substitutes this bound into the coefficient-three critical moment inequality.
Only the quantitative fourth moment of zeta remains on that edge; no mollifier-moment hypothesis
survives.
-/

open Complex MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace RHTower.Sieve

noncomputable section

/-- Split the critical-line complex power into its `n⁻¹ᐟ²` amplitude and oscillatory phase. -/
theorem natCast_cpow_neg_inghamCriticalPoint (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-inghamCriticalPoint t) =
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (((-t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : -inghamCriticalPoint t =
      (((-(1 : ℝ) / 2 : ℝ) : ℂ)) + (-((t : ℂ) * Complex.I)) := by
    unfold inghamCriticalPoint
    push_cast
    ring
  rw [hsplit, Complex.cpow_add _ _ hn0]
  have hamp : (n : ℂ) ^ (((-(1 : ℝ) / 2 : ℝ) : ℂ)) =
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hnR.le (-(1 : ℝ) / 2)).symm
  rw [hamp]
  rw [Complex.cpow_def_of_ne_zero hn0]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hnR.le).symm
  rw [hlog]
  congr 2
  push_cast
  ring

/-- Critical-line coefficients of the finite Möbius mollifier. -/
noncomputable def inghamCriticalMollifierSeq (X : ℕ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 X then
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
  else 0

theorem inghamCriticalMollifierSeq_support {X n : ℕ}
    (h : inghamCriticalMollifierSeq X n ≠ 0) : n ∈ Finset.Icc 1 X := by
  by_contra hn
  simp [inghamCriticalMollifierSeq, hn] at h

/-- The actual critical-line mollifier is the `LSeries` of its square-root-decayed coefficients. -/
theorem inghamMollifier_critical_eq_LSeries (X : ℕ) (t : ℝ) :
    inghamMollifier X (inghamCriticalPoint t) =
      LSeries (inghamCriticalMollifierSeq X) (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  rw [LSeries_eq_sum_term_of_support
    (fun n h => inghamCriticalMollifierSeq_support h)]
  rw [inghamMollifier]
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [LSeries.term_def, if_neg hn0]
  rw [inghamCriticalMollifierSeq, if_pos hnmem]
  have hpoint : -inghamCriticalPoint t =
      (((-(1 : ℝ) / 2 : ℝ) : ℂ)) + (-((t : ℂ) * Complex.I)) := by
    unfold inghamCriticalPoint
    push_cast
    ring
  rw [hpoint, Complex.cpow_add _ _ hnC]
  have hamp : (n : ℂ) ^ (((-(1 : ℝ) / 2 : ℝ) : ℂ)) =
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hnR.le (-(1 : ℝ) / 2)).symm
  rw [hamp, show (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I by norm_num]
  rw [Complex.cpow_neg]
  ring

/-- A critical mollifier coefficient has squared norm at most `1/n`. -/
theorem inghamCriticalMollifierSeq_norm_sq_le_inv
    (X n : ℕ) (hn : n ∈ Finset.Icc 1 X) :
    ‖inghamCriticalMollifierSeq X n‖ ^ 2 ≤ 1 / (n : ℝ) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [inghamCriticalMollifierSeq, if_pos hn, norm_mul]
  have hmu : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hpow : ‖(((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = 1 / (n : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg _ _)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt hnR)]
    rw [show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 by norm_num]
    rw [Real.rpow_neg_one]
    exact inv_eq_one_div _
    all_goals positivity
  rw [mul_pow, hpow]
  have hmu0 : 0 ≤ ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ := norm_nonneg _
  have hmusq : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (by positivity) hmusq

/-- The `n`-weighted coefficient mass is at most the mollifier length. -/
theorem inghamCriticalMollifierSeq_weighted_mass_le (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, (n : ℝ) * ‖inghamCriticalMollifierSeq X n‖ ^ 2 ≤ X := by
  calc
    ∑ n ∈ Finset.Icc 1 X, (n : ℝ) * ‖inghamCriticalMollifierSeq X n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          calc
            (n : ℝ) * ‖inghamCriticalMollifierSeq X n‖ ^ 2
                ≤ (n : ℝ) * (1 / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (inghamCriticalMollifierSeq_norm_sq_le_inv X n hn) (by positivity)
            _ = 1 := by
              have hn0 : (n : ℝ) ≠ 0 := by
                exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
              field_simp
    _ = X := by simp [Nat.card_Icc]

/-- The plain coefficient mass is at most the harmonic logarithm. -/
theorem inghamCriticalMollifierSeq_plain_mass_le (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, ‖inghamCriticalMollifierSeq X n‖ ^ 2 ≤
      1 + Real.log X := by
  exact (Finset.sum_le_sum fun n hn =>
    inghamCriticalMollifierSeq_norm_sq_le_inv X n hn).trans
      (sum_Icc_one_div_le_one_add_log X)

theorem inghamCriticalMollifierSeq_generalMeanSquareConst_le (X : ℕ) :
    generalMeanSquareConst (inghamCriticalMollifierSeq X) (Finset.Icc 1 X) 0 ≤
      5 * Real.pi * Real.exp 1 * X := by
  rw [generalMeanSquareConst]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  exact mul_le_mul_of_nonneg_left
    (inghamCriticalMollifierSeq_weighted_mass_le X) (by positivity)

theorem inghamCriticalMollifierSeq_generalMeanSquareRate_le (X : ℕ) :
    generalMeanSquareRate (inghamCriticalMollifierSeq X) (Finset.Icc 1 X) 0 ≤
      (5 * Real.pi / 2) * (1 + Real.log X) := by
  rw [generalMeanSquareRate]
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  exact mul_le_mul_of_nonneg_left
    (inghamCriticalMollifierSeq_plain_mass_le X) (by positivity)

/-- The actual Ingham mollifier has the sharp affine mean-square shape on a symmetric interval. -/
theorem integral_Icc_normSq_inghamMollifier_critical_le (X : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T, ‖inghamMollifier X (inghamCriticalPoint t)‖ ^ 2) ≤
      5 * Real.pi * Real.exp 1 * X +
        (5 * Real.pi / 2) * (1 + Real.log X) * T := by
  have hbase := integral_Icc_normSq_LSeries_le_general_affine
    (a := inghamCriticalMollifierSeq X) (s := Finset.Icc 1 X)
    (by simp) (fun _n hn => inghamCriticalMollifierSeq_support hn) 0 hT
  have hconst := inghamCriticalMollifierSeq_generalMeanSquareConst_le X
  have hrate := inghamCriticalMollifierSeq_generalMeanSquareRate_le X
  calc
    (∫ t in Set.Icc (-T) T, ‖inghamMollifier X (inghamCriticalPoint t)‖ ^ 2)
        ≤ generalMeanSquareConst (inghamCriticalMollifierSeq X) (Finset.Icc 1 X) 0 +
          generalMeanSquareRate (inghamCriticalMollifierSeq X) (Finset.Icc 1 X) 0 * T := by
            simpa only [inghamMollifier_critical_eq_LSeries] using hbase
    _ ≤ 5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (1 + Real.log X) * T :=
      add_le_add hconst (mul_le_mul_of_nonneg_right hrate (by linarith))

/-- The actual critical-line mollifier second moment on any positive subinterval has
`O(X + V log X)` with explicit constants. -/
theorem inghamCriticalMollifierSecondMoment_le (X : ℕ) {U V : ℝ}
    (hU : 0 ≤ U) (hV : 1 ≤ V) :
    inghamCriticalMollifierSecondMoment X U V ≤
      5 * Real.pi * Real.exp 1 * X +
        (5 * Real.pi / 2) * (1 + Real.log X) * V := by
  have hcont : Continuous fun t : ℝ =>
      ‖inghamMollifier X (inghamCriticalPoint t)‖ ^ (2 : ℝ) :=
    (continuous_inghamMollifier_critical X).norm.rpow_const (fun _ => Or.inr (by norm_num))
  have hsubset : Set.Icc U V ⊆ Set.Icc (-V) V := by
    exact Set.Icc_subset_Icc (by linarith) le_rfl
  have hmono :
      (∫ t in Set.Icc U V, ‖inghamMollifier X (inghamCriticalPoint t)‖ ^ (2 : ℝ)) ≤
        ∫ t in Set.Icc (-V) V, ‖inghamMollifier X (inghamCriticalPoint t)‖ ^ (2 : ℝ) := by
    refine MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Filter.Eventually.of_forall hsubset)
  unfold inghamCriticalMollifierSecondMoment
  refine hmono.trans ?_
  simpa only [Real.rpow_two] using
    (integral_Icc_normSq_inghamMollifier_critical_le X hV)

/-- Equation (41) after eliminating the mollifier moment: only the zeta fourth moment remains. -/
theorem inghamCriticalErrorFourThirdMoment_le_of_mollifier (X : ℕ) {U V : ℝ}
    (hU : 0 ≤ U) (hUV : U ≤ V) (hV : 1 ≤ V) :
    inghamCriticalErrorFourThirdMoment X U V ≤
      (2 : ℝ) ^ ((1 : ℝ) / 3) * (inghamCriticalZetaFourthMoment U V) ^ ((1 : ℝ) / 3) *
          (5 * Real.pi * Real.exp 1 * X +
            (5 * Real.pi / 2) * (1 + Real.log X) * V) ^ ((2 : ℝ) / 3) +
        (2 : ℝ) ^ ((1 : ℝ) / 3) * (V - U) := by
  have hbase := inghamCriticalErrorFourThirdMoment_le X hUV
  have hM := inghamCriticalMollifierSecondMoment_le X hU hV
  have hM0 : 0 ≤ inghamCriticalMollifierSecondMoment X U V := by
    unfold inghamCriticalMollifierSecondMoment
    positivity
  have hrpow :
      (inghamCriticalMollifierSecondMoment X U V) ^ ((2 : ℝ) / 3) ≤
        (5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (1 + Real.log X) * V) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hM0 hM (by norm_num)
  have hZ0 : 0 ≤ inghamCriticalZetaFourthMoment U V := by
    unfold inghamCriticalZetaFourthMoment
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hfactor : 0 ≤
      (2 : ℝ) ^ ((1 : ℝ) / 3) *
        (inghamCriticalZetaFourthMoment U V) ^ ((1 : ℝ) / 3) := by
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hZ0 _)
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_left hrpow hfactor) le_rfl)

end

end RHTower.Sieve
