import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureVerticalSourceIncrement

/-!
# Safe source family for positive HCF height traces

The HCF obstruction is not a fixed vertical increment: equal-multiplicity
transverse poles can cancel at one prescribed height.  This module constructs
the literal completed Euler--Gamma current on the whole short interval
`0 ≤ h ≤ 1` and proves a uniform safe-side bound.  Its squared norm is the
source-native nonnegative datum required by any later continuation argument.

Nothing here claims that this square reaches the divisor or retains a residue.
Those are the remaining HCF hard steps.
-/

open Complex LSeries

namespace RHTower

noncomputable section

/-- Literal short-height increment of the completed HCF Euler--Gamma current. -/
def criticalFeatureVerticalUnitSourceIncrement (t h : ℝ) : ℂ :=
  xiWardCubicCompletedArithmeticCurrent (criticalFeatureEulerVMArchPoint (t + h)) -
    xiWardCubicCompletedArithmeticCurrent (criticalFeatureEulerVMArchPoint t)

/-- Exact channel separation for every short-height source increment. -/
theorem criticalFeatureVerticalUnitSourceIncrement_eq_channels (t h : ℝ) :
    criticalFeatureVerticalUnitSourceIncrement t h =
      (criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹ +
        ((criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹) +
        (logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + h)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t)) := by
  unfold criticalFeatureVerticalUnitSourceIncrement xiWardCubicCompletedArithmeticCurrent
  ring

/-- The literal completed source is uniformly bounded on the safe line for
every positive height shift in the unit interval. -/
theorem exists_norm_criticalFeatureVerticalUnitSourceIncrement_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t h : ℝ, 2 ≤ t → 0 ≤ h → h ≤ 1 →
      ‖criticalFeatureVerticalUnitSourceIncrement t h‖ ≤ C := by
  obtain ⟨K, hK, hgamma⟩ :=
    exists_norm_logDeriv_GammaR_vertical_unit_interval_le
  let A : ℝ := ∑' n : ℕ, ‖LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((3 / 2 : ℝ) : ℂ) n‖
  have hA : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨16 / 3 + K + 2 * A, by positivity, ?_⟩
  intro t h ht hh0 hh1
  have hgamma' :
      ‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ ≤ K := by
    simpa [criticalFeatureEulerVMArchPoint] using hgamma t h ht hh0 hh1
  have hA_t := norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le t
  have hA_th := norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le (t + h)
  change ‖criticalFeatureVerticalUnitSourceIncrement t h‖ ≤ _
  rw [criticalFeatureVerticalUnitSourceIncrement_eq_channels]
  have hfirst : ‖(criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
      (criticalFeatureEulerVMArchPoint t)⁻¹‖ ≤ 4 / 3 := by
    calc
      _ ≤ ‖(criticalFeatureEulerVMArchPoint (t + h))⁻¹‖ +
          ‖(criticalFeatureEulerVMArchPoint t)⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 / 3 + 2 / 3 := by
        gcongr
        · exact norm_inv_criticalFeatureEulerVMArchPoint_le _
        · exact norm_inv_criticalFeatureEulerVMArchPoint_le _
      _ = 4 / 3 := by norm_num
  have hsecond : ‖(criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
      (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ ≤ 4 := by
    calc
      _ ≤ ‖(criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹‖ +
          ‖(criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ := norm_sub_le _ _
      _ ≤ 2 + 2 := by
        gcongr
        · exact norm_inv_criticalFeatureEulerVMArchPoint_sub_one_le _
        · exact norm_inv_criticalFeatureEulerVMArchPoint_sub_one_le _
      _ = 4 := by norm_num
  have hprime : ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint (t + h)) -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint t)‖ ≤ 2 * A := by
    calc
      _ ≤ ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + h))‖ +
          ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t)‖ := norm_sub_le _ _
      _ ≤ A + A := by simpa only [A] using add_le_add hA_th hA_t
      _ = 2 * A := by ring
  calc
    ‖(criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹ +
        ((criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹) +
        (logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + h)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t))‖ ≤
        ‖(criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
          (criticalFeatureEulerVMArchPoint t)⁻¹‖ +
        ‖(criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
          (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖ +
        ‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
          logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ +
        ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint (t + h)) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t)‖ := by
      calc
        _ = ‖((criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
            (criticalFeatureEulerVMArchPoint t)⁻¹ +
          ((criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
            (criticalFeatureEulerVMArchPoint t - 1)⁻¹)) +
          ((logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
            logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (t + h)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t)))‖ := by
          congr 1
          ring
        _ ≤ ‖(criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
            (criticalFeatureEulerVMArchPoint t)⁻¹ +
          ((criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
            (criticalFeatureEulerVMArchPoint t - 1)⁻¹)‖ +
          ‖(logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
            logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)) -
          (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (t + h)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t))‖ := norm_add_le _ _
        _ ≤ (‖(criticalFeatureEulerVMArchPoint (t + h))⁻¹ -
            (criticalFeatureEulerVMArchPoint t)⁻¹‖ +
          ‖(criticalFeatureEulerVMArchPoint (t + h) - 1)⁻¹ -
            (criticalFeatureEulerVMArchPoint t - 1)⁻¹‖) +
          (‖logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint (t + h)) -
            logDeriv Gammaℝ (criticalFeatureEulerVMArchPoint t)‖ +
          ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint (t + h)) -
            LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
              (criticalFeatureEulerVMArchPoint t)‖) := by
          gcongr
          · exact norm_add_le _ _
          · exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ 16 / 3 + K + 2 * A := by linarith

/-- Every finite safe-height window has a nonnegative source-square budget
linear in its cardinality.  This is the finite quadratic datum that a
continuation theorem must transport to the divisor. -/
theorem exists_sum_normSq_criticalFeatureVerticalUnitSourceIncrement_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℝ) (h : ℝ), 0 ≤ h → h ≤ 1 →
      (∀ t ∈ S, 2 ≤ t) →
        ∑ t ∈ S, ‖criticalFeatureVerticalUnitSourceIncrement t h‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * S.card := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_criticalFeatureVerticalUnitSourceIncrement_le
  refine ⟨C, hC, ?_⟩
  intro S h hh0 hh1 hS
  calc
    ∑ t ∈ S, ‖criticalFeatureVerticalUnitSourceIncrement t h‖ ^ (2 : ℕ) ≤
        ∑ _t ∈ S, C ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      have htbound := hbound t h (hS t ht) hh0 hh1
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) htbound
    _ = C ^ (2 : ℕ) * S.card := by simp [mul_comm]

end

end RHTower
