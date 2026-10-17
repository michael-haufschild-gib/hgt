import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Explicit hyperbolic weight jets and finite cell producers -/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistWeight (β : ℝ) (x : ℝ) : ℝ := Real.cosh (β * x)

def nyquistWeightJet (β : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  β ^ j / 2 * (Real.exp (β * x) + (-1 : ℝ) ^ j * Real.exp (-β * x))

theorem nyquistWeightJet_zero (β x : ℝ) : nyquistWeightJet β 0 x = nyquistWeight β x := by
  simp only [nyquistWeightJet, pow_zero, one_mul, nyquistWeight, Real.cosh_eq, neg_mul]
  ring

theorem contDiff_nyquistWeight (β : ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (nyquistWeight β) :=
  Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)

theorem contDiff_nyquistWeightJet (β : ℝ) (j : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (nyquistWeightJet β j) := by
  unfold nyquistWeightJet
  fun_prop

theorem hasDerivAt_nyquistWeightJet (β : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (nyquistWeightJet β j) (nyquistWeightJet β (j + 1) x) x := by
  have hp : HasDerivAt (fun y : ℝ => Real.exp (β * y)) (Real.exp (β * x) * β) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp (β * x)).comp x ((hasDerivAt_id x).const_mul β)
  have hn : HasDerivAt (fun y : ℝ => Real.exp (-β * y)) (Real.exp (-β * x) * -β) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp (-β * x)).comp x ((hasDerivAt_id x).const_mul (-β))
  have hh : HasDerivAt (nyquistWeightJet β j)
      (β ^ j / 2 * (Real.exp (β * x) * β + (-1 : ℝ) ^ j * (Real.exp (-β * x) * -β))) x :=
    (hp.add (hn.const_mul ((-1 : ℝ) ^ j))).const_mul (β ^ j / 2)
  have heq : β ^ j / 2 *
      (Real.exp (β * x) * β + (-1 : ℝ) ^ j * (Real.exp (-β * x) * -β)) =
      nyquistWeightJet β (j + 1) x := by
    simp only [nyquistWeightJet, pow_succ]
    ring
  rwa [heq] at hh

theorem iteratedDeriv_nyquistWeight (β : ℝ) (j : ℕ) :
    iteratedDeriv j (nyquistWeight β) = nyquistWeightJet β j := by
  induction j with
  | zero =>
      rw [iteratedDeriv_zero]
      funext x
      exact (nyquistWeightJet_zero β x).symm
  | succ j hj =>
      rw [iteratedDeriv_succ, hj]
      funext x
      exact (hasDerivAt_nyquistWeightJet β j x).deriv

theorem nyquistWeightJet_nonneg {β x : ℝ} (hβ : 0 ≤ β) (hx : 0 ≤ x) (j : ℕ) :
    0 ≤ nyquistWeightJet β j x := by
  have hs : |(-1 : ℝ) ^ j| ≤ 1 := by simp
  have hl := (abs_le.mp hs).1
  have he : Real.exp (-β * x) ≤ Real.exp (β * x) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hβ hx])
  have hh := mul_le_mul_of_nonneg_right hl (Real.exp_pos (-β * x)).le
  have hc : 0 ≤ Real.exp (β * x) + (-1 : ℝ) ^ j * Real.exp (-β * x) := by
    nlinarith only [he, hh]
  exact mul_nonneg (div_nonneg (pow_nonneg hβ j) (by norm_num)) hc

theorem nyquistWeightJet_le_exp {β x : ℝ} (hβ : 0 ≤ β) (hx : 0 ≤ x) (j : ℕ) :
    nyquistWeightJet β j x ≤ β ^ j * Real.exp (β * x) := by
  have hs : |(-1 : ℝ) ^ j| ≤ 1 := by simp
  have hu := (abs_le.mp hs).2
  have he : Real.exp (-β * x) ≤ Real.exp (β * x) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hβ hx])
  have hh := mul_le_mul_of_nonneg_right hu (Real.exp_pos (-β * x)).le
  have hc : Real.exp (β * x) + (-1 : ℝ) ^ j * Real.exp (-β * x) ≤
      2 * Real.exp (β * x) := by nlinarith only [he, hh]
  calc
    _ ≤ (β ^ j / 2) * (2 * Real.exp (β * x)) :=
      mul_le_mul_of_nonneg_left hc (div_nonneg (pow_nonneg hβ j) (by norm_num))
    _ = _ := by ring

def nyquistWeightTaylor (β : ℝ) (m : ℕ) (a x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), nyquistWeightJet β j a * (x - a) ^ j / (j.factorial : ℝ)

theorem nyquistWeightTaylor_zero (β a x : ℝ) :
    nyquistWeightTaylor β 0 a x = nyquistWeight β a := by
  simp [nyquistWeightTaylor, nyquistWeightJet_zero]

theorem nyquistWeightTaylor_succ (β : ℝ) (m : ℕ) (a x : ℝ) :
    nyquistWeightTaylor β (m + 1) a x = nyquistWeightTaylor β m a x +
      nyquistWeightJet β (m + 1) a * (x - a) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  exact Finset.sum_range_succ _ _

theorem nyquistWeightTaylor_self (β : ℝ) (m : ℕ) (a : ℝ) :
    nyquistWeightTaylor β m a a = nyquistWeight β a := by
  induction m with
  | zero => exact nyquistWeightTaylor_zero β a a
  | succ m hm => rw [nyquistWeightTaylor_succ, hm]; simp

theorem contDiff_nyquistWeightTaylor (β : ℝ) (m : ℕ) (a : ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (nyquistWeightTaylor β m a) := by
  unfold nyquistWeightTaylor
  fun_prop

theorem nyquistWeightTaylor_eq_taylorWithin (β : ℝ) (m : ℕ) (s : Set ℝ) (a x : ℝ)
    (hs : UniqueDiffOn ℝ s) (ha : a ∈ s) :
    nyquistWeightTaylor β m a x = taylorWithinEval (nyquistWeight β) m s a x := by
  rw [taylor_within_apply]
  unfold nyquistWeightTaylor
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (contDiff_nyquistWeight β j).contDiffAt ha,
    iteratedDeriv_nyquistWeight, smul_eq_mul]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty
