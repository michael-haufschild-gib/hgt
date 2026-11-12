import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateHasNoPositiveLaplaceZero
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateSatisfiesTheWeakEquation

/-!
# Uniqueness of the actual critical half-line state

The weak equation makes linear combinations of critical states have zero
energy. Cancelling one positive real Laplace value therefore produces a
zero profile. Unit normalization leaves only the two signs.
-/

noncomputable section
open MeasureTheory Filter Set Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

/-- Positive real Laplace weights are bounded on the actual half-line support. -/
theorem integrable_halfLineLaplace_of_domain {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun u => F u * Real.exp (s * u)) := by
  apply hF.integrable.norm.mono'
    (hF.meas.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  refine Eventually.of_forall fun u => ?_
  by_cases hu : 0 ≤ u
  · rw [hF.support u hu, zero_mul, norm_zero]
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_ge hu))))
      (norm_nonneg _)).trans_eq (mul_one _)

/-- One positive Laplace value fixes the scalar between any two actual critical states. -/
theorem criticalHalfLineGroundState_eq_laplace_ratio_ae
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F G : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hG : IsCriticalHalfLineGroundState W₀ G) {s : ℝ} (hs : 0 < s) :
    F =ᵐ[volume] fun u =>
      ((∫ v, F v * Real.exp (s * v)) / (∫ v, G v * Real.exp (s * v))) * G u := by
  have hdF := criticalHalfLineEnergyDomain_of_groundState hF
  have hdG := criticalHalfLineEnergyDomain_of_groundState hG
  let c := -((∫ v, F v * Real.exp (s * v)) / (∫ v, G v * Real.exp (s * v)))
  have hd := hdF.add_const_mul hdG c
  have he : criticalHalfLineFullEnergy W₀ (fun u => F u + c * G u) = 0 := by
    rw [criticalHalfLineFullEnergy_add_const_mul W₀ hdF hdG,
      criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hF,
      criticalHalfLineFullEnergy_groundState_eq_zero hW hthreshold hG,
      criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hdG]
    ring
  have hLG := criticalHalfLineGroundState_laplace_ne_zero hW hthreshold hG hs
  have hz : (∫ u, (F u + c * G u) * Real.exp (s * u)) = 0 := by
    simp_rw [add_mul, mul_assoc]
    rw [integral_add (integrable_halfLineLaplace_of_domain hdF hs.le)
      ((integrable_halfLineLaplace_of_domain hdG hs.le).const_mul c), integral_const_mul]
    dsimp only [c]
    field_simp
    ring
  have hh := ae_eq_zero_of_criticalHalfLineFullEnergy_eq_zero_of_laplace_zero
    hW hthreshold hd he hs hz
  filter_upwards [hh] with u hu
  change F u + c * G u = 0 at hu
  dsimp only [c] at hu
  linarith only [hu]

/-- The actual normalized critical state is unique up to sign, almost everywhere. -/
theorem criticalHalfLineGroundState_unique_up_to_sign
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F G : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hG : IsCriticalHalfLineGroundState W₀ G) :
    (F =ᵐ[volume] G) ∨ (F =ᵐ[volume] fun u => -G u) := by
  let c := (∫ v, F v * Real.exp v) / (∫ v, G v * Real.exp v)
  have hp : F =ᵐ[volume] fun u => c * G u := by
    simpa only [one_mul] using
      criticalHalfLineGroundState_eq_laplace_ratio_ae hW hthreshold hF hG (s := 1) zero_lt_one
  have hn : (∫ u, F u ^ 2) = c ^ 2 * (∫ u, G u ^ 2) := by
    calc
      _ = ∫ u, c ^ 2 * G u ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [hp] with u hu
        dsimp only
        rw [hu, mul_pow]
      _ = _ := integral_const_mul _ _
  rw [hF.2.2.2.1, hG.2.2.2.1, mul_one] at hn
  have hc : (c - 1) * (c + 1) = 0 := by nlinarith only [hn]
  rcases mul_eq_zero.mp hc with hc | hc
  · left
    have hc1 : c = 1 := by linarith only [hc]
    simpa only [hc1, one_mul] using hp
  · right
    have hc1 : c = -1 := by linarith only [hc]
    simpa only [hc1, neg_one_mul] using hp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
