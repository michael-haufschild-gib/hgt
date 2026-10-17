import GaloisForLFunctions.BiScaleUncertainty.AnnularGaugeEnergy
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarRoughGauge
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicJumpEnergyTransfer

/-!
# Correlation-only gauge budgets for signed prime–polar transport

The actual collar gauge source occupies an interval of length twice the original
source radius plus the collar width. Its exact correlation energy controls its
L¹ cost, eliminating the gauge norm from the rough-source packet upper bound.
-/

open MeasureTheory Set
open scoped CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open ChebyshevGauge
noncomputable section
set_option autoImplicit false

private theorem collar_zero_off_interval (f : C_c(ℝ, ℝ)) (a b u : ℝ)
    (hu : u ∉ Icc (Real.exp a - multiplierSourceRadius f)
      (Real.exp a + Real.exp b + multiplierSourceRadius f)) : collarSource f a b u = 0 := by
  change (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b), f (u-y)) / Real.exp b = 0
  have he : (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b), f (u-y)) = 0 := by
    calc
      _ = ∫ _y in Icc (Real.exp a) (Real.exp a + Real.exp b), (0:ℝ) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro y hy
        by_contra hn
        have hb := abs_le.mp (abs_le_multiplierSourceRadius f (u-y) hn)
        exact hu ⟨by linarith [hy.1], by linarith [hy.2]⟩
      _ = 0 := integral_zero _ _
  rw [he, zero_div]

/-- Gauge support lies in the translated source interval enlarged only by the width. -/
theorem collarGaugeSource_zero_off_interval (f : C_c(ℝ, ℝ)) (a b u : ℝ)
    (hu : u ∉ Icc (Real.exp a - multiplierSourceRadius f)
      (Real.exp a + Real.exp b + multiplierSourceRadius f)) : collarGaugeSource f a b u = 0 := by
  have h₁ : f (u-Real.exp a) = 0 := by
    by_contra hn
    have hb := abs_le.mp (abs_le_multiplierSourceRadius f _ hn)
    exact hu ⟨by linarith, by linarith [Real.exp_pos b]⟩
  have h₂ : f (u-Real.exp a-Real.exp b) = 0 := by
    by_contra hn
    have hb := abs_le.mp (abs_le_multiplierSourceRadius f _ hn)
    exact hu ⟨by linarith [Real.exp_pos b], by linarith⟩
  change (f (u-Real.exp a)-f (u-Real.exp a-Real.exp b))/Real.exp b -
    collarSource f a b u / 2 = 0
  rw [h₁, h₂, collar_zero_off_interval f a b u hu]
  ring

/-- Explicit L¹ budget from the exact correlation energy and actual support length. -/
def collarGaugeBudget (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  (2 * multiplierSourceRadius f + Real.exp b) * collarGaugeEnergy f a b

theorem collarGaugeL1_sq_le_budget (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarGaugeL1 f a b ^ 2 ≤ collarGaugeBudget f a b := by
  let lo := Real.exp a - multiplierSourceRadius f
  let hi := Real.exp a + Real.exp b + multiplierSourceRadius f
  have hab : lo ≤ hi := by
    dsimp [lo, hi]
    linarith [multiplierSourceRadius_pos f, Real.exp_pos b]
  have hsq : Integrable (fun u => collarGaugeSource f a b u ^ 2) :=
    integrable_sq (collarGaugeSource f a b).continuous (collarGaugeSource f a b).hasCompactSupport
  have ha : IntegrableOn (fun u => |collarGaugeSource f a b u| ^ 2) (Icc lo hi) := by
    simpa only [sq_abs] using hsq.integrableOn (s := Icc lo hi)
  have hc : IntegrableOn (fun _u : ℝ => (1:ℝ)^2) (Icc lo hi) :=
    continuous_const.integrableOn_Icc
  have hs := HTGeometry.sq_integral_mul_le (μ := volume.restrict (Icc lo hi))
    (f := fun u => |collarGaugeSource f a b u|) (g := fun _u => (1:ℝ))
    (collarGaugeSource f a b).continuous.abs.aestronglyMeasurable
    continuous_const.aestronglyMeasurable ha hc
  have h₁ : (∫ u in Icc lo hi, |collarGaugeSource f a b u|) = collarGaugeL1 f a b := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [collarGaugeSource_zero_off_interval f a b u hu, abs_zero]
  have h₂ : (∫ u in Icc lo hi, collarGaugeSource f a b u ^ 2) = collarGaugeEnergy f a b := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [collarGaugeSource_zero_off_interval f a b u hu, zero_pow (by omega : 2 ≠ 0)]),
      integral_collarGaugeSource_sq]
  have hlen : (∫ _u in Icc lo hi, (1:ℝ)) = 2 * multiplierSourceRadius f + Real.exp b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_const]
    dsimp [lo, hi]
    ring
  simp only [mul_one, one_pow, sq_abs] at hs
  rw [h₁, h₂, hlen] at hs
  simpa only [collarGaugeBudget, mul_comm] using hs

theorem collarGaugeBudget_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    0 ≤ collarGaugeBudget f a b :=
  (sq_nonneg _).trans (collarGaugeL1_sq_le_budget f a b)

/-- The gauge budget is independent of collar position. -/
theorem collarGaugeBudget_position_invariant (f : C_c(ℝ, ℝ)) (a a' b : ℝ) :
    collarGaugeBudget f a b = collarGaugeBudget f a' b := by
  unfold collarGaugeBudget
  rw [collarGaugeEnergy_position_invariant f a a' b]

/-- Explicit packet budget in source correlations, source radius, and Chebyshev error. -/
def correlationGaugeBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) : ℝ :=
  6 * (10+normalizedLogError (cutoff N)^2) * collarEnergy f a b +
    6 * collarGaugeBudget f a b * (∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2) +
    2 * mass N ^ 2 * collarChordEnergy f a b

theorem roughGaugeBound_le_correlationGaugeBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    roughGaugeBound f a b N ≤ correlationGaugeBound f a b N := by
  have hi : 0 ≤ ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (collarGaugeL1_sq_le_budget f a b) (by norm_num : (0:ℝ)≤6)) hi
  unfold roughGaugeBound correlationGaugeBound
  linarith only [hs]

/-- Source-only packet upper control with no constructed gauge norm remaining. -/
theorem packetEnergy_le_correlationGaugeBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    packetEnergy f N ≤ correlationGaugeBound f a b N :=
  (packetEnergy_le_roughGaugeBound f a b N).trans (roughGaugeBound_le_correlationGaugeBound f a b N)

/-- Global signed transport with correlation-only smoothing control. -/
theorem abs_fullPairing_sub_work_le_correlationGauge_levy (f : C_c(ℝ, ℝ))
    (a b u v c : ℝ) (K : ℕ) :
    |fullPairing (autocorr f) - fullChebyshevWork f u v| ≤
      Real.exp c * (∫ y in Real.exp u..Real.exp u + Real.exp v,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      correlationGaugeBound f a b (sourceCutoff f + K) / (2 * Real.exp c * Real.exp v ^ 2) *
        ∫ y in Real.exp u..Real.exp u + Real.exp v, Real.exp (-y / 2) * Real.sinh y := by
  have hi : 0 ≤ ∫ y in Real.exp u..Real.exp u + Real.exp v,
      Real.exp (-y / 2) * Real.sinh y := by
    apply intervalIntegral.integral_nonneg (le_add_of_nonneg_right (Real.exp_pos v).le)
    intro y hy
    rw [← inv_archLevySinhWeight_eq]
    exact inv_nonneg.mpr (archLevySinhWeight_pos ((Real.exp_pos u).trans_le hy.1)).le
  apply (abs_fullPairing_sub_work_le_roughGauge_levy f a b u v c K).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hi
  exact div_le_div_of_nonneg_right (roughGaugeBound_le_correlationGaugeBound f a b _) (by positivity)

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
