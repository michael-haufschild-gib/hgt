import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.HorizonAveragesAndSparseHorizons

/-!
# The averaged criterion on sparse horizons

The averaged budget is a statement for each horizon separately — the integral identity
`∫_a^c r_T = log((1+E_T(a))/(1+E_T(c)))` holds horizon by horizon — and the critical energy is
monotone in the horizon.  So the budget only has to be checked along a cofinal set of horizons:
dyadic ones suffice.

`admits_of_averaged_dyadic` transports admission from half damping using only the dyadic integrals,
and `riemannHypothesis_of_averaged_dyadic` is the resulting criterion for the Riemann hypothesis.

Combined with the fact that the averaged budget is *exactly* admission, this is the weakest shape the
continuation demand can take: one number per dyadic horizon, bounding the damping average of the
relative loss, and nothing else.
-/

open Set Filter MeasureTheory RHTower

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- **Per-horizon transport.**  One horizon's averaged bound transports that horizon's energy. -/
theorem energy_le_of_averaged_horizon {a c C : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ)
    (hC : (∫ ε in a..c, relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv T ε) ≤ C)
    {B : ℝ} (hB : dampedMobiusEnergy c T ≤ B) :
    dampedMobiusEnergy a T ≤ (1 + max B 0) * Real.exp C - 1 := by
  have hid := integral_relativeLoss_eq (E := dampedMobiusEnergy) (E' := dampedMobiusEnergyDeriv)
    (T := T) hac (fun ε _ => dampedMobiusEnergy_nonneg ε T)
    (fun ε hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le ha hε.1) T)
    (intervalIntegrable_relativeLoss_dampedMobiusEnergy ha hac T)
  have hca : (0 : ℝ) < 1 + dampedMobiusEnergy a T := by
    linarith [dampedMobiusEnergy_nonneg a T]
  have hcc : (0 : ℝ) < 1 + dampedMobiusEnergy c T := by
    linarith [dampedMobiusEnergy_nonneg c T]
  have hlog : Real.log (1 + dampedMobiusEnergy a T) ≤
      Real.log (1 + dampedMobiusEnergy c T) + C := by
    rw [hid] at hC
    linarith
  have hstep : 1 + dampedMobiusEnergy a T ≤ (1 + dampedMobiusEnergy c T) * Real.exp C := by
    calc 1 + dampedMobiusEnergy a T = Real.exp (Real.log (1 + dampedMobiusEnergy a T)) :=
          (Real.exp_log hca).symm
      _ ≤ Real.exp (Real.log (1 + dampedMobiusEnergy c T) + C) := Real.exp_le_exp.mpr hlog
      _ = (1 + dampedMobiusEnergy c T) * Real.exp C := by
          rw [Real.exp_add, Real.exp_log hcc]
  have h2 : (1 + dampedMobiusEnergy c T) * Real.exp C ≤ (1 + max B 0) * Real.exp C :=
    mul_le_mul_of_nonneg_right (by linarith [hB.trans (le_max_left B 0)]) (Real.exp_pos _).le
  linarith

/-- **Dyadic averaged budgets give admission.** -/
theorem admits_of_averaged_dyadic {a C : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hC : ∀ k : ℕ, (∫ ε in a..(1 / 2 : ℝ),
      relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv (2 ^ k) ε) ≤ C) :
    Admits dampedMobiusEnergy a := by
  obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_half_le (le_refl (1 / 2 : ℝ))
  refine Admits.of_dyadic_horizons (C := (1 + max B 0) * Real.exp C - 1)
    (dampedMobiusEnergy_mono a) fun k => ?_
  exact energy_le_of_averaged_horizon ha ha2 (2 ^ k) (hC k) (hB (2 ^ k))

/-- **The sparse averaged criterion for the Riemann hypothesis.** -/
theorem riemannHypothesis_of_averaged_dyadic
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 / 2 → ∃ C : ℝ, ∀ k : ℕ,
      (∫ ε in a..(1 / 2 : ℝ),
        relativeLoss dampedMobiusEnergy dampedMobiusEnergyDeriv (2 ^ k) ε) ≤ C) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_cofinallyAdmits.mpr fun δ hδ => ?_
  have hmin : 0 < min δ (1 / 2 : ℝ) := lt_min hδ (by norm_num)
  have hx0 : 0 < min δ (1 / 2 : ℝ) / 2 := by positivity
  have hx2 : min δ (1 / 2 : ℝ) / 2 ≤ 1 / 2 := by linarith [min_le_right δ (1 / 2 : ℝ)]
  obtain ⟨C, hC⟩ := h _ hx0 hx2
  exact ⟨min δ (1 / 2) / 2, hx0, by linarith [min_le_left δ (1 / 2 : ℝ)],
    admits_of_averaged_dyadic hx0 hx2 hC⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
