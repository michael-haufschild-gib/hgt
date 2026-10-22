import GaloisForLFunctions.RHTower.CCM.CCMActualHeadOutgoingQuantileBarycentricDebt
import GaloisForLFunctions.RHTower.CCM.CCMQuantileDisplacementMass
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarRelativeDisplacement
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedSymmetricFirstMomentControl

/-!
# Finite total centroid debit in the literal quantile transport

Replacing a complete polar cell by its left boundary incurs a nonnegative
entropy debit. The debits over all actual prime-power cells are summable.
The signed first displacement retains their exact finite-block sum.
This does not assert a floor for the remaining signed arithmetic current.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RHTower

/-- Exact centroid debit of one outgoing polar cell. -/
def ccmOutgoingQuantileCellEntropyDebit (n : ℕ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..ccmOutgoingPrimeQuantileBoundary (n+1),
    Real.exp (h/2) * (h-ccmOutgoingPrimeQuantileBoundary n)

theorem ccmOutgoingQuantileCellEntropyDebit_nonneg (n : ℕ) :
    0 ≤ ccmOutgoingQuantileCellEntropyDebit n := by
  apply intervalIntegral.integral_nonneg (ccmOutgoingPrimeQuantileBoundary_mono_step n)
  intro h hh
  exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hh.1)

/-- The exact debit is an exponential Bregman increment, with both endpoints retained. -/
theorem ccmOutgoingQuantileCellEntropyDebit_eq (n : ℕ) :
    ccmOutgoingQuantileCellEntropyDebit n =
      (2+ccmOutgoingPrimeCumulative (n+1)) *
        (ccmOutgoingPrimeQuantileBoundary (n+1)-ccmOutgoingPrimeQuantileBoundary n) -
      2*criticalMellinAtomWeight n := by
  let b := ccmOutgoingPrimeQuantileBoundary n
  let c := ccmOutgoingPrimeQuantileBoundary (n+1)
  let P : ℝ → ℝ := fun h => 2*Real.exp (h/2)*(h-b-2)
  have hd (h : ℝ) : HasDerivAt P (Real.exp (h/2)*(h-b)) h := by
    convert! ((((Real.hasDerivAt_exp (h/2)).comp h
      ((hasDerivAt_id h).div_const 2)).const_mul 2).mul
      (((hasDerivAt_id h).sub_const b).sub_const 2)) using 1
    simp only [id_eq, Function.comp_apply]
    ring
  have hi : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*(h-b)) volume b c :=
    (by fun_prop : Continuous (fun h : ℝ => Real.exp (h/2)*(h-b))).intervalIntegrable _ _
  change (∫ h in b..c, Real.exp (h/2)*(h-b)) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun h _ => hd h) hi]
  dsimp only [P, b, c]
  rw [exp_half_ccmOutgoingPrimeQuantileBoundary,
    exp_half_ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative_succ]
  ring

theorem ccmOutgoingQuantileCellEntropyDebit_le_width (n : ℕ) :
    ccmOutgoingQuantileCellEntropyDebit n ≤
      criticalMellinAtomWeight n *
        (ccmOutgoingPrimeQuantileBoundary (n+1)-ccmOutgoingPrimeQuantileBoundary n) := by
  let b := ccmOutgoingPrimeQuantileBoundary n
  let c := ccmOutgoingPrimeQuantileBoundary (n+1)
  have hleft : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*(h-b)) volume b c :=
    (by fun_prop : Continuous (fun h : ℝ => Real.exp (h/2)*(h-b))).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*(c-b)) volume b c :=
    (by fun_prop : Continuous (fun h : ℝ => Real.exp (h/2)*(c-b))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on
    (ccmOutgoingPrimeQuantileBoundary_mono_step n) hleft hright
    (fun h hh => mul_le_mul_of_nonneg_left (sub_le_sub_right hh.2 b) (Real.exp_pos _).le)
  rw [intervalIntegral.integral_mul_const, integral_exp_half_quantileCell_eq_atomWeight] at h
  exact h

theorem ccmOutgoingPrimeQuantileBoundary_increment_le (n : ℕ) :
    ccmOutgoingPrimeQuantileBoundary (n+1)-ccmOutgoingPrimeQuantileBoundary n ≤
      2*criticalMellinAtomWeight n/(2+ccmOutgoingPrimeCumulative n) := by
  let m := ccmOutgoingPrimeCumulative n
  let w := criticalMellinAtomWeight n
  have hm : 0 ≤ m := ccmOutgoingPrimeCumulative_nonneg n
  have hw : 0 ≤ w := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hu : 0 < 1+m/2 := by linarith
  have hv : 0 < 1+(m+w)/2 := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at hl
  have he : (1+(m+w)/2)/(1+m/2)-1 = w/(2+m) := by
    field_simp
    ring
  rw [he] at hl
  unfold ccmOutgoingPrimeQuantileBoundary
  rw [ccmOutgoingPrimeCumulative_succ]
  change 2*Real.log (1+(m+w)/2)-2*Real.log (1+m/2) ≤ 2*w/(2+m)
  have ht := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [mul_sub, mul_div_assoc] using ht

/-- Actual cumulative mass controls the complete local nonlinear debit. -/
theorem ccmOutgoingQuantileCellEntropyDebit_le_mass (n : ℕ) :
    ccmOutgoingQuantileCellEntropyDebit n ≤
      2*criticalMellinAtomWeight n^2/(2+ccmOutgoingPrimeCumulative n) := by
  have h := mul_le_mul_of_nonneg_left (ccmOutgoingPrimeQuantileBoundary_increment_le n)
    (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)
  calc
    _ ≤ criticalMellinAtomWeight n *
        (ccmOutgoingPrimeQuantileBoundary (n+1)-ccmOutgoingPrimeQuantileBoundary n) :=
      ccmOutgoingQuantileCellEntropyDebit_le_width n
    _ ≤ criticalMellinAtomWeight n *
        (2*criticalMellinAtomWeight n/(2+ccmOutgoingPrimeCumulative n)) := h
    _ = _ := by ring

/-- There is only a finite total centroid debit along the complete arithmetic exhaustion. -/
theorem summable_ccmOutgoingQuantileCellEntropyDebit :
    Summable ccmOutgoingQuantileCellEntropyDebit := by
  let k : ℝ := Real.log 2/2
  have hk : 0 < k := by dsimp only [k]; positivity
  have hmajor := summable_criticalMellinAtomWeight_sq_div_exp_half_log.mul_left (2/k)
  apply Summable.of_norm_bounded_eventually_nat hmajor
  filter_upwards [eventually_sqrt_le_ccmOutgoingPrimeCumulative,
    eventually_ge_atTop (1 : ℕ)] with n hmass hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hw := criticalMellinAtomWeight_le_two_of_pos (by omega : 0 < n)
  have hden : k*Real.sqrt n ≤ 2+ccmOutgoingPrimeCumulative n := by
    rw [ccmOutgoingPrimeCumulative_succ] at hmass
    dsimp only [k] at *
    linarith
  have hexp : Real.exp (Real.log (n : ℝ)/2) = Real.sqrt n := by
    rw [← Real.log_sqrt hnpos.le, Real.exp_log hs]
  rw [Real.norm_eq_abs, abs_of_nonneg (ccmOutgoingQuantileCellEntropyDebit_nonneg n), hexp]
  calc
    _ ≤ 2*criticalMellinAtomWeight n^2/(2+ccmOutgoingPrimeCumulative n) :=
      ccmOutgoingQuantileCellEntropyDebit_le_mass n
    _ ≤ 2*criticalMellinAtomWeight n^2/(k*Real.sqrt n) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hk hs) hden
    _ = _ := by ring

/-- Positive arithmetic atoms, and only those atoms, pay a strict centroid debit. -/
theorem ccmOutgoingQuantileCellEntropyDebit_pos_iff (n : ℕ) :
    0 < ccmOutgoingQuantileCellEntropyDebit n ↔ 0 < criticalMellinAtomWeight n := by
  constructor
  · intro hd
    by_contra! hw
    have hw0 := le_antisymm hw
      (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)
    have hb : ccmOutgoingPrimeQuantileBoundary (n+1) =
        ccmOutgoingPrimeQuantileBoundary n := by
      simp only [ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative_succ, hw0, add_zero]
    simp only [ccmOutgoingQuantileCellEntropyDebit, hb, intervalIntegral.integral_same] at hd
    exact lt_irrefl 0 hd
  · intro hw
    have hb : ccmOutgoingPrimeQuantileBoundary n < ccmOutgoingPrimeQuantileBoundary (n+1) := by
      unfold ccmOutgoingPrimeQuantileBoundary
      rw [ccmOutgoingPrimeCumulative_succ]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
      apply Real.log_lt_log
      · linarith [ccmOutgoingPrimeCumulative_nonneg n]
      · linarith
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by fun_prop : Continuous (fun h : ℝ => Real.exp (h/2)*
        (h-ccmOutgoingPrimeQuantileBoundary n))).intervalIntegrable _ _) _ hb
    intro h hh
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr hh.1)

/-- The all-prime debit is finite and strictly positive, without a source-sign premise. -/
theorem tsum_ccmOutgoingQuantileCellEntropyDebit_pos :
    0 < ∑' n, ccmOutgoingQuantileCellEntropyDebit n := by
  have hw : 0 < criticalMellinAtomWeight 2 := by
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have hd := (ccmOutgoingQuantileCellEntropyDebit_pos_iff 2).mpr hw
  exact hd.trans_le (summable_ccmOutgoingQuantileCellEntropyDebit.le_tsum 2
    (fun n _ => ccmOutgoingQuantileCellEntropyDebit_nonneg n))

/-- The signed cell displacement is the boundary-node current minus its exact debit. -/
theorem ccmOutgoingQuantileCellLinearDisplacement_eq_node_sub_entropy (n : ℕ) :
    ccmOutgoingQuantileCellLinearDisplacement n =
      criticalMellinAtomWeight n * (Real.log n-ccmOutgoingPrimeQuantileBoundary n) -
        ccmOutgoingQuantileCellEntropyDebit n := by
  let b := ccmOutgoingPrimeQuantileBoundary n
  let c := ccmOutgoingPrimeQuantileBoundary (n+1)
  have h1 : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*(Real.log n-b)) volume b c :=
    (by fun_prop : Continuous (fun h : ℝ => Real.exp (h/2)*(Real.log n-b))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun h : ℝ => Real.exp (h/2)*(h-b)) volume b c :=
    (by fun_prop : Continuous (fun h : ℝ => Real.exp (h/2)*(h-b))).intervalIntegrable _ _
  unfold ccmOutgoingQuantileCellLinearDisplacement ccmOutgoingQuantileCellEntropyDebit
  calc
    _ = ∫ h in b..c, Real.exp (h/2)*(Real.log n-b)-Real.exp (h/2)*(h-b) := by
      apply intervalIntegral.integral_congr
      intro h _
      dsimp only [b]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_mul_const,
        integral_exp_half_quantileCell_eq_atomWeight]

/-- The source keeps every signed node term; only the positive debit has been summed away. -/
theorem ccmOutgoingQuantileFiniteLinearDisplacement_eq_node_sub_entropy (N : ℕ) :
    (∑ n ∈ Finset.range N, ccmOutgoingQuantileCellLinearDisplacement n) =
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n*(Real.log n-ccmOutgoingPrimeQuantileBoundary n)) -
      ∑ n ∈ Finset.range N, ccmOutgoingQuantileCellEntropyDebit n := by
  simp_rw [ccmOutgoingQuantileCellLinearDisplacement_eq_node_sub_entropy,
    Finset.sum_sub_distrib]

/-- Exact limiting correction between the two literal signed arithmetic currents. -/
theorem tendsto_ccmOutgoingQuantileNodeCurrent_sub_linearDisplacement :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n*(Real.log n-ccmOutgoingPrimeQuantileBoundary n)) -
      ∑ n ∈ Finset.range N, ccmOutgoingQuantileCellLinearDisplacement n)
      atTop (𝓝 (∑' n, ccmOutgoingQuantileCellEntropyDebit n)) := by
  simp_rw [ccmOutgoingQuantileFiniteLinearDisplacement_eq_node_sub_entropy,
    sub_sub_cancel]
  exact summable_ccmOutgoingQuantileCellEntropyDebit.hasSum.tendsto_sum_nat

end RHTower
