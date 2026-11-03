import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import Mathlib.Analysis.Calculus.DSlope

/-!
# The harmonic spectrum of regional logarithmic jumps

The regional kernel `1 / (2 |x-y|)` on `[-1,1]` has Legendre eigenfunctions.
Its eigenvalues are twice the harmonic numbers. The multiplication commutator
reduces the singular integral recurrence to ordinary Legendre primitives.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

/-- The regional logarithmic operator, with the diagonal removed by continuous slopes. -/
def regionalLogOperator (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y in (-1 : ℝ)..x, dslope F x y) - ∫ y in x..1, dslope F x y

/-- The eigenvalue of the Legendre polynomial of degree `n`. -/
def regionalLogEigenvalue (n : ℕ) : ℝ :=
  2 * ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)

@[simp] theorem regionalLogEigenvalue_zero : regionalLogEigenvalue 0 = 0 := by
  simp [regionalLogEigenvalue]

theorem regionalLogEigenvalue_succ (n : ℕ) :
    regionalLogEigenvalue (n + 1) = regionalLogEigenvalue n + 2 / ((n : ℝ) + 1) := by
  simp only [regionalLogEigenvalue, Finset.sum_range_succ]
  ring

private theorem continuous_dslope_of_differentiable {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) (x : ℝ) : Continuous (dslope F x) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases h : y = x
  · subst y
    exact continuousAt_dslope_same.mpr (hF x)
  · exact (continuousAt_dslope_of_ne h).mpr hF.continuous.continuousAt

private theorem dslope_sub_fun {F G : ℝ → ℝ}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x y : ℝ) :
    dslope (fun t => F t - G t) x y = dslope F x y - dslope G x y := by
  by_cases h : y = x
  · subst y
    simp only [dslope_same]
    exact ((hF x).hasDerivAt.sub (hG x).hasDerivAt).deriv
  · rw [dslope_of_ne _ h, dslope_of_ne _ h, dslope_of_ne _ h]
    simp only [slope_def_field]
    ring

private theorem dslope_const_mul_fun {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) (c x y : ℝ) :
    dslope (fun t => c * F t) x y = c * dslope F x y := by
  by_cases h : y = x
  · subst y
    simp only [dslope_same]
    exact ((hF x).hasDerivAt.const_mul c).deriv
  · rw [dslope_of_ne _ h, dslope_of_ne _ h]
    simp only [slope_def_field]
    ring

private theorem dslope_id_mul_fun {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) (x y : ℝ) :
    dslope (fun t => t * F t) x y = x * dslope F x y + F y := by
  by_cases h : y = x
  · subst y
    simp only [dslope_same]
    have hd := ((hasDerivAt_id x).mul (hF x).hasDerivAt).deriv
    change deriv (fun t => t * F t) x = 1 * F x + x * deriv F x at hd
    simpa only [one_mul, add_comm] using hd
  · rw [dslope_of_ne _ h, dslope_of_ne _ h]
    simp only [slope_def_field]
    field_simp [sub_ne_zero.mpr h]
    ring

/-- Linearity of the regional operator on differentiable functions. -/
theorem regionalLogOperator_sub {F G : ℝ → ℝ}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : ℝ) :
    regionalLogOperator (fun t => F t - G t) x =
      regionalLogOperator F x - regionalLogOperator G x := by
  have hFi (a b : ℝ) : IntervalIntegrable (dslope F x) volume a b :=
    (continuous_dslope_of_differentiable hF x).intervalIntegrable a b
  have hGi (a b : ℝ) : IntervalIntegrable (dslope G x) volume a b :=
    (continuous_dslope_of_differentiable hG x).intervalIntegrable a b
  unfold regionalLogOperator
  simp_rw [dslope_sub_fun hF hG]
  rw [intervalIntegral.integral_sub (hFi _ _) (hGi _ _),
    intervalIntegral.integral_sub (hFi _ _) (hGi _ _)]
  ring

theorem regionalLogOperator_const_mul {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) (c x : ℝ) :
    regionalLogOperator (fun t => c * F t) x = c * regionalLogOperator F x := by
  unfold regionalLogOperator
  simp_rw [dslope_const_mul_fun hF, intervalIntegral.integral_const_mul]
  ring

/-- Multiplication by position has an ordinary antiderivative as its commutator. -/
theorem regionalLogOperator_id_mul {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) (x : ℝ) :
    regionalLogOperator (fun t => t * F t) x = x * regionalLogOperator F x +
      ((∫ y in (-1 : ℝ)..x, F y) - ∫ y in x..1, F y) := by
  have hDi (a b : ℝ) : IntervalIntegrable (dslope F x) volume a b :=
    (continuous_dslope_of_differentiable hF x).intervalIntegrable a b
  have hFi (a b : ℝ) : IntervalIntegrable F volume a b := hF.continuous.intervalIntegrable a b
  unfold regionalLogOperator
  simp_rw [dslope_id_mul_fun hF]
  rw [intervalIntegral.integral_add ((hDi _ _).const_mul x) (hFi _ _),
    intervalIntegral.integral_add ((hDi _ _).const_mul x) (hFi _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

private theorem legP_at_one (n : ℕ) : legP n 1 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rfl
    · rfl
    · rw [legP_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring

/-- The ordinary primitive needed by the regional multiplication commutator. -/
theorem integral_legP_succ (n : ℕ) (a b : ℝ) :
    (∫ u in a..b, legP (n + 1) u) =
      ((legP (n + 2) b - legP n b) - (legP (n + 2) a - legP n a)) /
        (2 * (n : ℝ) + 3) := by
  have hd (u : ℝ) : HasDerivAt
      (fun u => (legP (n + 2) u - legP n u) / (2 * (n : ℝ) + 3))
      (legP (n + 1) u) u := by
    have h := ((hasDerivAt_legP (n + 2) u).sub (hasDerivAt_legP n u)).div_const
      (2 * (n : ℝ) + 3)
    refine h.congr_deriv ?_
    change ((2 * (n : ℝ) + 3) * legP (n + 1) u + legP' n u - legP' n u) /
      (2 * (n : ℝ) + 3) = _
    have hn : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_legP (n + 1)).intervalIntegrable _ _)]
  ring

theorem legP_signed_primitive (n : ℕ) (x : ℝ) :
    (∫ u in (-1 : ℝ)..x, legP (n + 1) u) - (∫ u in x..1, legP (n + 1) u) =
      2 * (legP (n + 2) x - legP n x) / (2 * (n : ℝ) + 3) := by
  rw [integral_legP_succ, integral_legP_succ, legP_at_one, legP_at_one]
  have he : legP (n + 2) (-1) = legP n (-1) := by
    rw [legP_neg, legP_neg, legP_at_one, legP_at_one, pow_add]
    norm_num
  rw [he]
  ring

theorem regionalLogOperator_const (c x : ℝ) :
    regionalLogOperator (fun _ => c) x = 0 := by
  have he : dslope (fun _ : ℝ => c) x = fun _ => 0 := by
    funext y
    by_cases h : y = x
    · subst y
      rw [dslope_same]
      exact (hasDerivAt_const x c).deriv
    · rw [dslope_of_ne _ h, slope_def_field]
      simp
  simp only [regionalLogOperator, he, intervalIntegral.integral_zero, sub_self]

theorem regionalLogOperator_id (x : ℝ) : regionalLogOperator (fun t => t) x = 2 * x := by
  have he : dslope (fun t : ℝ => t) x = fun _ => 1 := by
    funext y
    by_cases h : y = x
    · subst y
      rw [dslope_same]
      exact (hasDerivAt_id x).deriv
    · rw [dslope_of_ne _ h, slope_def_field]
      exact div_self (sub_ne_zero.mpr h)
  simp only [regionalLogOperator, he, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Legendre polynomials diagonalize the regional logarithmic operator. -/
theorem regionalLogOperator_legP (n : ℕ) (x : ℝ) :
    regionalLogOperator (legP n) x = regionalLogEigenvalue n * legP n x := by
  have hP (k : ℕ) : Differentiable ℝ (legP k) :=
    fun u => (hasDerivAt_legP k u).differentiableAt
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · change regionalLogOperator (fun _ => 1) x = _
      rw [regionalLogOperator_const, regionalLogEigenvalue_zero, zero_mul]
    · change regionalLogOperator (fun t => t) x = _
      rw [regionalLogOperator_id]
      norm_num [regionalLogEigenvalue, legP]
    · have he : legP (n + 2) = fun t => 1 / ((n : ℝ) + 2) *
          ((2 * (n : ℝ) + 3) * (t * legP (n + 1) t) - ((n : ℝ) + 1) * legP n t) := by
        funext t
        rw [legP_succ_succ]
        ring
      have hXP : Differentiable ℝ (fun t => t * legP (n + 1) t) :=
        fun t => differentiableAt_id.mul (hP (n + 1) t)
      have hA : Differentiable ℝ (fun t => (2 * (n : ℝ) + 3) * (t * legP (n + 1) t)) :=
        hXP.const_mul _
      have hB : Differentiable ℝ (fun t => ((n : ℝ) + 1) * legP n t) := (hP n).const_mul _
      have hAB : Differentiable ℝ (fun t =>
          (2 * (n : ℝ) + 3) * (t * legP (n + 1) t) - ((n : ℝ) + 1) * legP n t) :=
        fun t => (hA t).sub (hB t)
      conv_lhs => rw [he]
      rw [regionalLogOperator_const_mul hAB,
        regionalLogOperator_sub hA hB, regionalLogOperator_const_mul hXP,
        regionalLogOperator_const_mul (hP n), regionalLogOperator_id_mul (hP (n + 1)),
        ih (n + 1) (by omega), ih n (by omega), legP_signed_primitive]
      change 1 / ((n : ℝ) + 2) *
        ((2 * (n : ℝ) + 3) *
          (x * (regionalLogEigenvalue (n + 1) * legP (n + 1) x) +
            2 * (legP (n + 2) x - legP n x) / (2 * (n : ℝ) + 3)) -
          ((n : ℝ) + 1) * (regionalLogEigenvalue n * legP n x)) =
        regionalLogEigenvalue (n + 2) * legP (n + 2) x
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      have hc : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
      have hb : (2 * (n : ℝ) + 3) * x * legP (n + 1) x =
          ((n : ℝ) + 2) * legP (n + 2) x + ((n : ℝ) + 1) * legP n x := by
        linarith only [legP_bonnet n x]
      calc
        _ = (regionalLogEigenvalue (n + 1) *
              ((2 * (n : ℝ) + 3) * x * legP (n + 1) x) +
            2 * (legP (n + 2) x - legP n x) -
            ((n : ℝ) + 1) * regionalLogEigenvalue n * legP n x) / ((n : ℝ) + 2) := by
              field_simp [hc, h2]
        _ = _ := by
          rw [hb, regionalLogEigenvalue_succ (n + 1), regionalLogEigenvalue_succ n]
          push_cast
          field_simp [h1, h2]
          ring

/-- Every polynomial evaluation is a finite Legendre combination. -/
theorem polynomial_eval_mem_legP_span (p : Polynomial ℝ) :
    (fun x => p.eval x) ∈ Submodule.span ℝ (Set.range legP) := by
  let V : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Set.range legP)
  have hP (n : ℕ) : legP n ∈ V := Submodule.subset_span (Set.mem_range_self n)
  have hXP (n : ℕ) : (fun x => x * legP n x) ∈ V := by
    cases n with
    | zero =>
      convert hP 1 using 1
      funext x
      simp only [legP_zero, legP_one, mul_one]
    | succ n =>
      have h := V.add_mem
        (V.smul_mem (((n : ℝ) + 2) / (2 * (n : ℝ) + 3)) (hP (n + 2)))
        (V.smul_mem (((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) (hP n))
      convert h using 1
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hn : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp
      linear_combination -(legP_bonnet n x)
  have hX {F : ℝ → ℝ} (hF : F ∈ V) : (fun x => x * F x) ∈ V := by
    induction hF using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨n, rfl⟩ := hf
      exact hXP n
    | zero =>
      convert V.zero_mem using 1
      funext x
      simp
    | add f g hf hg ihf ihg =>
      convert V.add_mem ihf ihg using 1
      funext x
      simp only [Pi.add_apply, mul_add]
    | smul c f hf ih =>
      convert V.smul_mem c ih using 1
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  change (fun x => p.eval x) ∈ V
  induction p using Polynomial.induction_on with
  | C c =>
    convert V.smul_mem c (hP 0) using 1
    funext x
    simp only [Polynomial.eval_C, Pi.smul_apply, smul_eq_mul, legP_zero, mul_one]
  | add p q hp hq =>
    convert V.add_mem hp hq using 1
    funext x
    simp only [Polynomial.eval_add, Pi.add_apply]
  | monomial n c ih =>
    convert hX ih using 1
    funext x
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, pow_succ]
    ring

theorem polynomial_eval_eq_legP_sum (p : Polynomial ℝ) :
    ∃ c : ℕ →₀ ℝ, ∀ x, p.eval x = ∑ n ∈ c.support, c n * legP n x := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
    (polynomial_eval_mem_legP_span p)
  refine ⟨c, fun x => ?_⟩
  have he := congrFun hc x
  simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he.symm

/-- The continuous-slope definition equals the regional singular integral inside the interval. -/
theorem regionalLogOperator_eq_integral {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    regionalLogOperator F x = ∫ y in (-1 : ℝ)..1, (F x - F y) / |x - y| := by
  have hb (y : ℝ) : |(F x - F y) / (|x - y|)| ≤ |dslope F x y| := by
    by_cases h : y = x
    · subst y
      simp only [sub_self, abs_zero, zero_div, abs_zero]
      exact abs_nonneg _
    · rw [dslope_of_ne _ h, slope_def_field, abs_div, abs_abs, abs_div,
        abs_sub_comm (F y) (F x), abs_sub_comm y x]
  have hi (a b : ℝ) : IntervalIntegrable (fun y => (F x - F y) / |x - y|) volume a b := by
    refine ((continuous_dslope_of_differentiable hF x).intervalIntegrable a b).mono_fun ?_ ?_
    · exact ((continuous_const.sub hF.continuous).measurable.div
        (continuous_const.sub continuous_id).abs.measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-1) x) (hi x 1)]
  have hl : (∫ y in (-1 : ℝ)..x, (F x - F y) / |x - y|) =
      ∫ y in (-1 : ℝ)..x, dslope F x y := by
    apply SelectivePositivityAndThresholdLaws.intervalIntegral_congr_Ioo hx.1
    intro y hy hyx
    rw [abs_of_pos (sub_pos.mpr hyx), dslope_of_ne _ hyx.ne, slope_def_field]
    field_simp [(sub_pos.mpr hyx).ne', (sub_neg.mpr hyx).ne]
    ring
  have hr : (∫ y in x..1, (F x - F y) / |x - y|) =
      -(∫ y in x..1, dslope F x y) := by
    rw [← intervalIntegral.integral_neg]
    apply SelectivePositivityAndThresholdLaws.intervalIntegral_congr_Ioo hx.2
    intro y hxy hy
    rw [abs_of_neg (sub_neg.mpr hxy), dslope_of_ne _ hxy.ne', slope_def_field]
    field_simp [(sub_pos.mpr hxy).ne', (sub_neg.mpr hxy).ne]
    ring
  rw [hl, hr]
  unfold regionalLogOperator
  ring

/-- Legendre functions are smooth; only one derivative is needed for the jump form. -/
theorem contDiff_legP (n : ℕ) : ContDiff ℝ 1 (legP n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · exact contDiff_const
    · exact contDiff_id
    · have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      change ContDiff ℝ 1 (fun x =>
        ((2 * (n : ℝ) + 3) * x * legP (n + 1) x - ((n : ℝ) + 1) * legP n x) /
          ((n : ℝ) + 2))
      simp only [div_eq_mul_inv]
      fun_prop

theorem regionalLogEigenvalue_monotone : Monotone regionalLogEigenvalue := by
  apply monotone_nat_of_le_succ
  intro n
  rw [regionalLogEigenvalue_succ]
  have h : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  linarith only [h]

theorem regionalLogEigenvalue_nonneg (n : ℕ) : 0 ≤ regionalLogEigenvalue n := by
  simpa only [regionalLogEigenvalue_zero] using regionalLogEigenvalue_monotone (Nat.zero_le n)

theorem regionalLogOperator_add {F G : ℝ → ℝ}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : ℝ) :
    regionalLogOperator (fun t => F t + G t) x =
      regionalLogOperator F x + regionalLogOperator G x := by
  have he : (fun t => F t + G t) = fun t => F t - (-1) * G t := by
    funext t
    ring
  rw [he, regionalLogOperator_sub hF (hG.const_mul (-1)),
    regionalLogOperator_const_mul hG]
  ring

/-- A finite Legendre expansion and its differentiated jump expansion. -/
def regionalLegendreSum (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ s, a n * legP n x

theorem contDiff_regionalLegendreSum (s : Finset ℕ) (a : ℕ → ℝ) :
    ContDiff ℝ 1 (regionalLegendreSum s a) := by
  have hP := contDiff_legP
  unfold regionalLegendreSum
  fun_prop

theorem regionalLogOperator_legendreSum (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    regionalLogOperator (regionalLegendreSum s a) x =
      ∑ n ∈ s, a n * regionalLogEigenvalue n * legP n x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have he : regionalLegendreSum ∅ a = fun _ => 0 := by
      funext t
      simp only [regionalLegendreSum, Finset.sum_empty]
    rw [he, regionalLogOperator_const, Finset.sum_empty]
  | @insert n s hn ih =>
    have he : regionalLegendreSum (insert n s) a =
        fun t => a n * legP n t + regionalLegendreSum s a t := by
      funext t
      exact Finset.sum_insert hn
    rw [he, regionalLogOperator_add
      (((contDiff_legP n).differentiable (by norm_num)).const_mul (a n))
      ((contDiff_regionalLegendreSum s a).differentiable (by norm_num)),
      regionalLogOperator_const_mul ((contDiff_legP n).differentiable (by norm_num)),
      regionalLogOperator_legP, ih, Finset.sum_insert hn]
    ring

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogOperator_legP

#print axioms GaloisForLFunctions.LatticeSectionTheory.polynomial_eval_eq_legP_sum
#print axioms GaloisForLFunctions.LatticeSectionTheory.regionalLogOperator_eq_integral
