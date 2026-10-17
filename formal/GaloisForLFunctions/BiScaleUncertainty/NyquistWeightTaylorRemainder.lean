import GaloisForLFunctions.BiScaleUncertainty.NyquistWeightJets
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Positive Taylor residuals and sharp endpoint bounds on one cell -/

open Set MeasureTheory

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem monotoneOn_nyquistWeightJet {β : ℝ} (hβ : 0 ≤ β) (j : ℕ) :
    MonotoneOn (nyquistWeightJet β j) (Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (contDiff_nyquistWeightJet β j 1).continuous.continuousOn
    (fun x _ => (hasDerivAt_nyquistWeightJet β j x).hasDerivWithinAt)
  intro x hx
  exact nyquistWeightJet_nonneg hβ (interior_subset hx) (j + 1)

def nyquistWeightTaylorResidual (β : ℝ) (m : ℕ) (a x : ℝ) : ℝ :=
  nyquistWeight β x - nyquistWeightTaylor β m a x

theorem continuous_nyquistWeightTaylorResidual (β : ℝ) (m : ℕ) (a : ℝ) :
    Continuous (nyquistWeightTaylorResidual β m a) :=
  (contDiff_nyquistWeight β 1).continuous.sub
    (contDiff_nyquistWeightTaylor β m a 1).continuous

theorem nyquistWeightTaylorResidual_bounds {β a b x : ℝ} (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (m : ℕ) (hx : x ∈ Icc a b) :
    nyquistWeightJet β (m + 1) a * (x - a) ^ (m + 1) / ((m + 1).factorial : ℝ) ≤
        nyquistWeightTaylorResidual β m a x ∧
      nyquistWeightTaylorResidual β m a x ≤
        nyquistWeightJet β (m + 1) b * (x - a) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · subst x
    simp [nyquistWeightTaylorResidual, nyquistWeightTaylor_self]
  obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax.ne
    (contDiff_nyquistWeight β ((m : WithTop ℕ∞) + 1)).contDiffOn
  rw [uIoo_of_lt hax] at hy
  rw [← nyquistWeightTaylor_eq_taylorWithin β m (uIcc a x) a x
    (uniqueDiffOn_uIcc hax.ne) left_mem_uIcc, iteratedDeriv_nyquistWeight] at heq
  change nyquistWeightTaylorResidual β m a x = _ at heq
  rw [heq]
  have hm := monotoneOn_nyquistWeightJet hβ (m + 1)
  have hp : 0 ≤ (x - a) ^ (m + 1) := pow_nonneg (sub_nonneg.mpr hx.1) _
  have hd : 0 ≤ ((m + 1).factorial : ℝ) := Nat.cast_nonneg _
  exact ⟨div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hm ha (ha.trans hy.1.le) hy.1.le) hp) hd,
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hm (ha.trans hy.1.le)
        (ha.trans (hx.1.trans hx.2)) (hy.2.le.trans hx.2)) hp) hd⟩

theorem nyquistWeightTaylorResidual_nonneg {β a x : ℝ} (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (m : ℕ) (hax : a ≤ x) :
    0 ≤ nyquistWeightTaylorResidual β m a x := by
  apply le_trans _ (nyquistWeightTaylorResidual_bounds hβ ha m ⟨hax, le_rfl⟩).1
  exact div_nonneg (mul_nonneg (nyquistWeightJet_nonneg hβ ha (m + 1))
    (pow_nonneg (sub_nonneg.mpr hax) _)) (Nat.cast_nonneg _)

def nyquistWeightTaylorMass (β : ℝ) (m : ℕ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, nyquistWeightTaylorResidual β m a x

theorem integral_nyquistWeightTaylor_monomial (c a b : ℝ) (m : ℕ) :
    (∫ x in a..b, c * (x - a) ^ (m + 1) / ((m + 1).factorial : ℝ)) =
      c * (b - a) ^ (m + 2) / ((m + 2).factorial : ℝ) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (m + 1)), integral_pow]
  have hf : ((m + 2).factorial : ℝ) =
      ((m : ℝ) + 2) * ((m + 1).factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  simp only [sub_self, zero_pow (by omega : m + 1 + 1 ≠ 0), sub_zero,
    Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem nyquistWeightTaylorMass_bounds {β a b : ℝ} (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) :
    nyquistWeightJet β (m + 1) a * (b - a) ^ (m + 2) / ((m + 2).factorial : ℝ) ≤
        nyquistWeightTaylorMass β m a b ∧
      nyquistWeightTaylorMass β m a b ≤
        nyquistWeightJet β (m + 1) b * (b - a) ^ (m + 2) / ((m + 2).factorial : ℝ) := by
  have hi := (continuous_nyquistWeightTaylorResidual β m a).intervalIntegrable
    (μ := volume) a b
  have hp (c : ℝ) : IntervalIntegrable
      (fun x : ℝ => c * (x - a) ^ (m + 1) / ((m + 1).factorial : ℝ)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  constructor
  · rw [← integral_nyquistWeightTaylor_monomial]
    exact intervalIntegral.integral_mono_on hab (hp _) hi
      (fun x hx => (nyquistWeightTaylorResidual_bounds hβ ha m hx).1)
  · rw [← integral_nyquistWeightTaylor_monomial]
    exact intervalIntegral.integral_mono_on hab hi (hp _)
      (fun x hx => (nyquistWeightTaylorResidual_bounds hβ ha m hx).2)

theorem nyquistWeightTaylorMass_nonneg {β a b : ℝ} (hβ : 0 ≤ β)
    (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) : 0 ≤ nyquistWeightTaylorMass β m a b :=
  intervalIntegral.integral_nonneg hab
    (fun _ hx => nyquistWeightTaylorResidual_nonneg hβ ha m hx.1)

end
end GaloisForLFunctions.BiScaleUncertainty
