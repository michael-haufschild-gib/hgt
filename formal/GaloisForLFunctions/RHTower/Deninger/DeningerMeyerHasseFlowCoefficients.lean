import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseResolvent
import GaloisForLFunctions.RHTower.UniversalBoundedGeneratorCausalHorizonLaw
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Exact full-Jordan coefficients of the original Meyer flow

The bounded Hasse shift exponentiates all repeated-zero slots at once. Each
coordinate sees only its finite predecessor chain, and the resulting formula
agrees with the original dilation action on every literal Meyer source class.
-/

noncomputable section
open Complex Set

namespace RHTower

def deningerHasseLower (q : DeningerArithmeticJetCoordinate) (k : ℕ) :
    DeningerArithmeticJetCoordinate :=
  ⟨q.1, ⟨q.2.val-k, lt_of_le_of_lt (Nat.sub_le _ _) q.2.isLt⟩⟩

theorem deningerHasseHilbertShift_pow_apply (k : ℕ) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    (deningerHasseHilbertShift^k) x q =
      if k ≤ q.2.val then x (deningerHasseLower q k) else 0 := by
  induction k generalizing q with
  | zero => simp [deningerHasseLower]
  | succ k ih =>
    rcases q with ⟨rho, j, hj⟩
    cases j with
    | zero => simp [pow_succ', deningerHasseHilbertShift_zero]
    | succ j =>
      rw [pow_succ', mul_apply_eq_comp, deningerHasseHilbertShift_succ, ih]
      by_cases hk : k ≤ j
      · simp only [hk, Nat.succ_le_succ_iff, ↓reduceIte]
        simp [deningerHasseLower]
      · simp only [hk, Nat.succ_le_succ_iff, ↓reduceIte]

/-- The original nilpotent part, with no cutoff on the multiplicities. -/
def deningerHasseShiftEvolution (t : ℝ) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  NormedSpace.exp ((t : ℂ) • deningerHasseHilbertShift)

theorem continuous_deningerHasseShiftEvolution : Continuous deningerHasseShiftEvolution :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_exp_smul_const deningerHasseHilbertShift (t : ℂ)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt

theorem deningerHasseShiftEvolution_apply (t : ℝ) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerHasseShiftEvolution t x q =
      ∑ k ∈ Finset.range (q.2.val+1),
        (t : ℂ)^k/(k.factorial : ℂ) * x (deningerHasseLower q k) := by
  let e := lp.evalCLM ℂ (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q
  have hs := (ParityForecast.boundedGeneratorOrbit_series_hasSum
    deningerHasseHilbertShift (t : ℂ) x).map e e.continuous
  change HasSum (fun k : ℕ =>
    (t : ℂ)^k/(k.factorial : ℂ) * (deningerHasseHilbertShift^k) x q)
      (deningerHasseShiftEvolution t x q) at hs
  rw [← hs.tsum_eq]
  calc
    _ = ∑ k ∈ Finset.range (q.2.val+1),
        (t : ℂ)^k/(k.factorial : ℂ) * (deningerHasseHilbertShift^k) x q := by
      apply tsum_eq_sum
      intro k hk
      rw [deningerHasseHilbertShift_pow_apply, if_neg (by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk), mul_zero]
    _ = _ := Finset.sum_congr rfl fun k hk => by
      rw [deningerHasseHilbertShift_pow_apply,
        if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

private theorem hasse_binomial_term (j k : ℕ) (hkj : k ≤ j) (a b c : ℂ) :
    (j.choose k : ℂ)*a*b*c/(j.factorial : ℂ) =
      b*(a/(k.factorial : ℂ))*(c/((j-k).factorial : ℂ)) := by
  have h : (j.choose k : ℂ)*(k.factorial : ℂ)*((j-k).factorial : ℂ) =
      (j.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkj
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hd : ((j-k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-k)
  field_simp
  linear_combination a*b*c*h

/-- Entire original-source flow covariance in factorial normalization. -/
theorem deningerMeyerHasseJet_flow (t : ℝ) (u : DeningerMeyerStrongLogCohomology)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHasseJet (deningerMeyerStrongLogCohomologyFlow t u) q =
      Complex.exp ((t : ℂ)*(q.1 : ℂ)) *
        ∑ k ∈ Finset.range (q.2.val+1),
          (t : ℂ)^k/(k.factorial : ℂ) * deningerMeyerHasseJet u (deningerHasseLower q k) := by
  rw [deningerMeyerHasseJet, deningerMeyerXiSupportJetEvaluationLM_flow,
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [deningerMeyerHasseJet, deningerHasseLower, mul_assoc] using
    hasse_binomial_term q.2.val k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      ((t : ℂ)^k) (Complex.exp ((t : ℂ)*(q.1 : ℂ)))
        (deningerMeyerXiSupportJetEvaluationLM q.1
          ⟨q.2.val-k, lt_of_le_of_lt (Nat.sub_le _ _) q.2.isLt⟩ u)

end RHTower
