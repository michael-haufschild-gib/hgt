import GaloisForLFunctions.RHTower.MobiusPrimeApertureRetainedMass
import GaloisForLFunctions.RHTower.ExponentialIntegralE1
import GaloisForLFunctions.RHTower.MertensSecondRealVariable
import GaloisForLFunctions.RHTower.PrimeRecipBelowWindow

/-!
# The critical prime-aperture profile of the Möbius boundary layer

At the critical scaling `N = exp(c/(2ω))` the prime tail sum `∑_{p > N} p^{-1-2ω}` is exactly a
weighted integral of the prime reciprocal window, by interchanging the sum with the elementary
identity `p^{-2ω} = ∫_{2ω log p}^{∞} e^{-u} du`.  Mertens' second theorem evaluates the window,
and dominated convergence produces the exponential integral `E₁(c)`.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- The prime reciprocal sum up to a real bound. -/
def primeRecipUpTo (x : ℝ) : ℝ := primeRecipSum ⌊x⌋₊

/-- The critical prime cutoff `N_ω = exp(c/(2ω))`. -/
def criticalCutoff (c ω : ℝ) : ℝ := Real.exp (c / (2 * ω))

/-- The prime reciprocal window between the critical cutoff and `exp(u/(2ω))`. -/
def apertureWindow (c ω u : ℝ) : ℝ :=
  primeRecipUpTo (Real.exp (u / (2 * ω))) - primeRecipUpTo (criticalCutoff c ω)

/-- The summand of the critical prime tail: `1/p · p^{-2ω}` above the cutoff. -/
def apertureTerm (c ω : ℝ) (n : ℕ) : ℝ :=
  if ⌊criticalCutoff c ω⌋₊ < n then primeRecipWeight n * (n : ℝ) ^ (-(2 * ω)) else 0

/-- The critical prime tail sum `∑_{p > N_ω} p^{-1-2ω}`. -/
def apertureTailSum (c ω : ℝ) : ℝ := ∑' n : ℕ, apertureTerm c ω n

/-! ## Elementary facts about the cutoff -/

theorem criticalCutoff_pos (c ω : ℝ) : 0 < criticalCutoff c ω := Real.exp_pos _

theorem primeRecipSum_mono {M N : ℕ} (h : M ≤ N) : primeRecipSum M ≤ primeRecipSum N := by
  rw [primeRecipSum, primeRecipSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h) ?_
  exact fun n _ _ => primeRecipWeight_nonneg n

theorem primeRecipSum_eq_sum_range (N : ℕ) :
    primeRecipSum N = ∑ n ∈ Finset.range (N + 1), primeRecipWeight n := by
  rw [primeRecipSum, show Finset.Icc 0 N = Finset.range (N + 1) by ext n; simp]

/-- The finite window sum in terms of the two prime reciprocal sums. -/
theorem sum_range_ite_eq_sub {K M : ℕ} (h : K ≤ M) :
    ∑ n ∈ Finset.range (M + 1), (if K < n then primeRecipWeight n else 0)
      = primeRecipSum M - primeRecipSum K := by
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => if K < n then primeRecipWeight n else 0) (Nat.succ_le_succ h)
  have hlow : ∑ n ∈ Finset.range (K + 1), (if K < n then primeRecipWeight n else 0) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [if_neg (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  have hhigh : ∑ n ∈ Finset.Ico (K + 1) (M + 1), (if K < n then primeRecipWeight n else 0)
      = ∑ n ∈ Finset.Ico (K + 1) (M + 1), primeRecipWeight n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : K + 1 ≤ n := (Finset.mem_Ico.mp hn).1
    rw [if_pos (by omega : K < n)]
  rw [hlow, hhigh, zero_add] at hsplit
  have hsplit2 := Finset.sum_range_add_sum_Ico primeRecipWeight (Nat.succ_le_succ h)
  rw [primeRecipSum_eq_sum_range, primeRecipSum_eq_sum_range, ← hsplit2, ← hsplit]
  ring

/-! ## The prime tail as a weighted window integral -/

/-- The integrand family: the elementary identity `p^{-2ω} = ∫_{2ω log p}^∞ e^{-u} du`. -/
def apertureIntegrand (c ω : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if ⌊criticalCutoff c ω⌋₊ < n then
    primeRecipWeight n * Set.indicator (Ici (2 * ω * Real.log n)) (fun v => Real.exp (-v)) u
  else 0

theorem apertureIntegrand_nonneg (c ω : ℝ) (n : ℕ) (u : ℝ) :
    0 ≤ apertureIntegrand c ω n u := by
  simp only [apertureIntegrand]
  split_ifs with h
  · refine mul_nonneg (primeRecipWeight_nonneg n) ?_
    refine Set.indicator_nonneg (fun v _ => ?_) u
    exact (Real.exp_pos _).le
  · exact le_rfl

theorem measurable_apertureIntegrand (c ω : ℝ) (n : ℕ) :
    Measurable (apertureIntegrand c ω n) := by
  unfold apertureIntegrand
  split_ifs
  · exact (measurable_const.mul
      ((Real.measurable_exp.comp measurable_neg).indicator measurableSet_Ici))
  · exact measurable_const

/-- The cutoff exponent: `2ω log N_ω = c`. -/
theorem two_mul_log_criticalCutoff {c ω : ℝ} (hω : 0 < ω) :
    2 * ω * Real.log (criticalCutoff c ω) = c := by
  rw [criticalCutoff, Real.log_exp]
  field_simp

theorem criticalCutoff_lt_of_floor_lt {c ω : ℝ} {n : ℕ} (h : ⌊criticalCutoff c ω⌋₊ < n) :
    criticalCutoff c ω < n :=
  (Nat.floor_lt (criticalCutoff_pos c ω).le).mp h

/-- Above the cutoff the exponent exceeds `c`. -/
theorem lt_two_mul_log_of_floor_lt {c ω : ℝ} (hω : 0 < ω) {n : ℕ}
    (h : ⌊criticalCutoff c ω⌋₊ < n) : c < 2 * ω * Real.log n := by
  have hlt := criticalCutoff_lt_of_floor_lt h
  have hlog : Real.log (criticalCutoff c ω) < Real.log n :=
    Real.log_lt_log (criticalCutoff_pos c ω) hlt
  have h2 : (0 : ℝ) < 2 * ω := by linarith
  calc c = 2 * ω * Real.log (criticalCutoff c ω) := (two_mul_log_criticalCutoff hω).symm
    _ < 2 * ω * Real.log n := by exact mul_lt_mul_of_pos_left hlog h2

/-- The integral of one term of the family is the corresponding prime tail term. -/
theorem integral_apertureIntegrand {c ω : ℝ} (hω : 0 < ω) (n : ℕ) :
    ∫ u in Ioi c, apertureIntegrand c ω n u = apertureTerm c ω n := by
  simp only [apertureIntegrand, apertureTerm]
  by_cases h : ⌊criticalCutoff c ω⌋₊ < n
  · simp only [if_pos h]
    rw [integral_const_mul]
    have hlt := lt_two_mul_log_of_floor_lt hω h
    have hset : Ioi c ∩ Ici (2 * ω * Real.log n) = Ici (2 * ω * Real.log n) := by
      refine Set.inter_eq_right.mpr fun v hv => ?_
      exact lt_of_lt_of_le hlt hv
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici, hset]
    have hIci : ∫ v in Ici (2 * ω * Real.log n), Real.exp (-v)
        = ∫ v in Ioi (2 * ω * Real.log n), Real.exp (-v) := by
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [hIci, integral_exp_neg_Ioi]
    congr 1
    have hn : 0 < n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Real.rpow_def_of_pos hnpos]
    ring_nf
  · simp only [if_neg h]
    exact integral_zero _ _

end

end RHTower
