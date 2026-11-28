import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Survival
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock.LinearClock

/-! # One residue at unit time determines all elementary survival probabilities -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock

open scoped NNReal
open ModeCapacities

abbrev Curve := ℝ≥0 → Set.Icc (0:ℝ) 1

/-- Counting one surviving residue at unit time calibrates a memoryless curve. -/
def calibrated (p : Nat.Primes) (q : Curve) :=
  (∀ a b, (q (a+b)).val=(q a).val*(q b).val) ∧ (q 1).val=1/(p.val:ℝ)

private theorem attenuation {p : Nat.Primes} {q : Curve} (law : calibrated p q) (t : ℝ≥0) :
    (q t).val=survive (t:ℝ) p.val := by
  obtain ⟨add,anchor⟩ := law
  have atOne : 0<(q 1).val := by rw [anchor]; exact one_div_pos.mpr (Nat.cast_pos.mpr p.property.pos)
  have atZero : (q 0).val=1 := by
    have h := add 0 1
    rw [zero_add] at h
    exact mul_right_cancel₀ atOne.ne' (h.symm.trans (one_mul _).symm)
  have integers (n : ℕ) : (q (n:ℝ≥0)).val=(q 1).val^n := by
    induction n with
    | zero => simpa only [Nat.cast_zero,pow_zero] using atZero
    | succ n ih => rw [Nat.cast_succ,add,ih,pow_succ]
  have anti : Antitone fun x => (q x).val := by
    intro a b hab
    obtain ⟨r,rfl⟩ := exists_add_of_le hab
    change (q (a+r)).val≤(q a).val
    rw [add]
    exact mul_le_of_le_one_right (q a).property.1 (q r).property.2
  have positive (r : ℝ≥0) : 0<(q r).val := by
    obtain ⟨N,hN⟩ := exists_nat_gt r
    have h : 0<(q (N:ℝ≥0)).val := by rw [integers]; exact pow_pos atOne N
    exact h.trans_le (anti hN.le)
  let A : ℝ≥0 →+ ℝ := {
    toFun := fun x => -Real.log (q x).val
    map_zero' := by rw [atZero,Real.log_one,neg_zero]
    map_add' := fun a b => by rw [add,Real.log_mul (positive a).ne' (positive b).ne',neg_add] }
  have Apos (x : ℝ≥0) : 0≤A x := neg_nonneg.mpr (Real.log_nonpos (q x).property.1 (q x).property.2)
  have main := linear_attenuation A Apos t
  change -Real.log (q t).val=(t:ℝ)*(-Real.log (q 1).val) at main
  rw [anchor,one_div,Real.log_inv,neg_neg] at main
  rw [←Real.exp_log (positive t),survive]
  congr 1
  linarith only [main]

/-- The finite counting calibration fixes the full clock, including its
regularity, among all probability-valued functions on real time. -/
theorem calibrated_iff (p : Nat.Primes) (q : Curve) :
    calibrated p q ↔ ∀ t, (q t).val=survive (t:ℝ) p.val := by
  constructor
  · exact fun h t => attenuation h t
  · intro canon
    constructor
    · intro a b
      rw [canon,canon,canon,NNReal.coe_add,←survive_mul,Pi.mul_apply]
    · simpa only [canon,NNReal.coe_one] using one_time p

#print axioms calibrated_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock
