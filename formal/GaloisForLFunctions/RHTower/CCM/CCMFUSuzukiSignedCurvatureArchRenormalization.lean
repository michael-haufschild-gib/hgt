import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSignedCurvatureUnitRieszBridge
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszProfileLimit
import GaloisForLFunctions.RHTower.BlaschkeLocalizedClockAsymptotic

/-!
# Sublinear archimedean renormalization for Suzuki signed curvature

Suzuki's signed checkpoint curvature lands exactly in the central unit-Riesz source after an
explicit source-free archimedean renormalization. This file proves that renormalization is only
`O(√N)`, hence disappears after the natural first-moment normalization by `N + 2`.

Consequently, normalized signed Suzuki curvature and the literal central CCM-UR/HG coherent
source differ by `o(1)` and have exactly the same cofinal limits. This is a pre-damping bridge: it
preserves the arithmetic first moment that the summable matched Route-O lift necessarily erases.
No prime asymptotic, zero-location statement, or RH hypothesis is used.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower
open scoped Interval

/-- Positive decaying tail subtracted from `exp (t / 2)` in Suzuki's regular kernel. -/
def suzukiCheckpointArchTail (t : ℝ) : ℝ :=
  Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t)))

theorem suzukiCheckpointArchTail_nonneg_le_exp_neg_half_div_three
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    0 ≤ suzukiCheckpointArchTail t ∧
      suzukiCheckpointArchTail t ≤ Real.exp (-(t / 2)) / 3 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have htpos : 0 < t := hlog2.trans_le ht
  have hxpos : 0 < Real.exp (-(2 * t)) := Real.exp_pos _
  have hxle : Real.exp (-(2 * t)) ≤ 1 / 4 := by
    have hneg : -(2 * t) ≤ -(2 * Real.log 2) := by linarith
    calc
      Real.exp (-(2 * t)) ≤ Real.exp (-(2 * Real.log 2)) := Real.exp_le_exp.mpr hneg
      _ = 1 / 4 := by
        rw [show -(2 * Real.log 2) = -(Real.log 2 + Real.log 2) by ring,
          Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hden : 0 < 1 - Real.exp (-(2 * t)) := by linarith
  have hratio : Real.exp (-(2 * t)) / (1 - Real.exp (-(2 * t))) ≤ 1 / 3 := by
    rw [div_le_iff₀ hden]
    linarith
  have hfactor : Real.exp (-(5 * t / 2)) =
      Real.exp (-(t / 2)) * Real.exp (-(2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [suzukiCheckpointArchTail, hfactor, mul_div_assoc]
  constructor
  · positivity
  · calc
      Real.exp (-(t / 2)) *
          (Real.exp (-(2 * t)) / (1 - Real.exp (-(2 * t)))) ≤
        Real.exp (-(t / 2)) * (1 / 3) :=
          mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
      _ = Real.exp (-(t / 2)) / 3 := by ring

theorem integral_exp_half_log_cell {k : ℕ} (hk : 1 ≤ k) :
    (∫ t in Real.log (k : ℝ)..Real.log ((k + 1 : ℕ) : ℝ), Real.exp (t / 2)) =
      2 * (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkp1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => 2 * Real.exp (u / 2)) (Real.exp (t / 2)) t := by
    intro t
    apply (((Real.hasDerivAt_exp (t / 2)).comp t
      ((hasDerivAt_id t).div_const 2)).const_mul 2).congr_deriv
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (t / 2)) volume
      (Real.log (k : ℝ)) (Real.log ((k + 1 : ℕ) : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (t / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  have hsqrt2 : Real.exp (Real.log ((k + 1 : ℕ) : ℝ) / 2) =
      Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    rw [← Real.log_sqrt hkp1pos.le, Real.exp_log (Real.sqrt_pos.mpr hkp1pos)]
  have hsqrt1 : Real.exp (Real.log (k : ℝ) / 2) = Real.sqrt (k : ℝ) := by
    rw [← Real.log_sqrt hkpos.le, Real.exp_log (Real.sqrt_pos.mpr hkpos)]
  rw [hsqrt2, hsqrt1]
  ring

theorem integral_exp_neg_half_log_cell {k : ℕ} (hk : 1 ≤ k) :
    (∫ t in Real.log (k : ℝ)..Real.log ((k + 1 : ℕ) : ℝ), Real.exp (-(t / 2))) =
      2 * ((Real.sqrt k)⁻¹ - (Real.sqrt (k + 1 : ℕ))⁻¹) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkp1pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => -2 * Real.exp (-(u / 2))) (Real.exp (-(t / 2))) t := by
    intro t
    have hinner : HasDerivAt (fun u : ℝ => -(u / 2)) (-(1 / 2 : ℝ)) t := by
      simpa using! ((hasDerivAt_id t).div_const 2).neg
    apply ((hinner.exp).const_mul (-2 : ℝ)).congr_deriv
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(t / 2))) volume
      (Real.log (k : ℝ)) (Real.log ((k + 1 : ℕ) : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t / 2))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  have hsqrt1 : Real.exp (-(Real.log (k : ℝ) / 2)) = (Real.sqrt k)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [← Real.log_sqrt hkpos.le, Real.exp_log (Real.sqrt_pos.mpr hkpos)]
  have hsqrt2 : Real.exp (-(Real.log ((k + 1 : ℕ) : ℝ) / 2)) =
      (Real.sqrt (k + 1 : ℕ))⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [← Real.log_sqrt hkp1pos.le, Real.exp_log (Real.sqrt_pos.mpr hkp1pos)]
  rw [hsqrt2, hsqrt1]
  ring

theorem natCast_mul_invSqrt_sub_invSqrt_le_invSqrt_pred
    {k : ℕ} (hk : 2 ≤ k) :
    (k : ℝ) * ((Real.sqrt (k - 1 : ℕ))⁻¹ - (Real.sqrt k)⁻¹) ≤
      (Real.sqrt (k - 1 : ℕ))⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpredR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  have ha : 0 < a := Real.sqrt_pos.mpr hpredR
  have hb : 0 < b := Real.sqrt_pos.mpr hkR
  have ha2 : a ^ 2 = ((k - 1 : ℕ) : ℝ) := Real.sq_sqrt hpredR.le
  have hb2 : b ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le k 1))
  have hba0 : 0 ≤ b - a := sub_nonneg.mpr hab
  have hgap : (b - a) * (b + a) = 1 := by
    nlinarith [ha2, hb2, hcast]
  have haux : b * (b - a) ≤ 1 := by
    calc
      b * (b - a) ≤ (b + a) * (b - a) := by nlinarith
      _ = 1 := by nlinarith [hgap]
  have hmain : (k : ℝ) * (b - a) ≤ b := by
    rw [← hb2]
    calc
      b ^ 2 * (b - a) = b * (b * (b - a)) := by ring
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left haux hb.le
      _ = b := by ring
  change (k : ℝ) * (a⁻¹ - b⁻¹) ≤ a⁻¹
  rw [inv_sub_inv ha.ne' hb.ne']
  calc
    (k : ℝ) * ((b - a) / (a * b)) =
        ((k : ℝ) * (b - a)) / (a * b) := by ring
    _ ≤ b / (a * b) := div_le_div_of_nonneg_right hmain (mul_pos ha hb).le
    _ = a⁻¹ := by field_simp [ha.ne', hb.ne']

def suzukiCheckpointWeightedArchTailPrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      suzukiCheckpointArchTail t)

theorem suzukiCheckpointWeightedArchTailCell_nonneg_le
    {k : ℕ} (hk : 3 ≤ k) :
    0 ≤ (k : ℝ) *
        (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          suzukiCheckpointArchTail t) ∧
      (k : ℝ) *
        (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          suzukiCheckpointArchTail t) ≤
        (2 / 3 : ℝ) * (Real.sqrt (k - 1 : ℕ))⁻¹ := by
  have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hlogle : Real.log ((k - 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
    (Real.log_le_log_iff hpredpos hkpos).mpr (by exact_mod_cast (Nat.sub_le k 1))
  have hlog2 : Real.log 2 ≤ Real.log ((k - 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hpredpos
    · exact_mod_cast (by omega : 2 ≤ k - 1)
  have htailCont : ContinuousOn suzukiCheckpointArchTail
      (Icc (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog2.trans ht.1)
      exact ne_of_gt (one_sub_exp_neg_two_mul_pos htpos)
  have htailInt : IntervalIntegrable suzukiCheckpointArchTail volume
      (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ)) := by
    have htailCont' : ContinuousOn suzukiCheckpointArchTail
        (uIcc (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ))) := by
      simpa only [uIcc_of_le hlogle] using htailCont
    exact htailCont'.intervalIntegrable
  have hmajorInt : IntervalIntegrable (fun t : ℝ => Real.exp (-(t / 2)) / 3) volume
      (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t / 2)) / 3).intervalIntegrable _ _
  have hmono :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          suzukiCheckpointArchTail t) ≤
        ∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
          Real.exp (-(t / 2)) / 3 := by
    refine intervalIntegral.integral_mono_on hlogle htailInt hmajorInt ?_
    intro t ht
    exact (suzukiCheckpointArchTail_nonneg_le_exp_neg_half_div_three
      (hlog2.trans ht.1)).2
  have htail0 : 0 ≤
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        suzukiCheckpointArchTail t) := by
    apply intervalIntegral.integral_nonneg hlogle
    intro t ht
    exact (suzukiCheckpointArchTail_nonneg_le_exp_neg_half_div_three
      (hlog2.trans ht.1)).1
  constructor
  · positivity
  · calc
      (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            suzukiCheckpointArchTail t) ≤
        (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            Real.exp (-(t / 2)) / 3) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (2 / 3 : ℝ) * (k : ℝ) *
          ((Real.sqrt (k - 1 : ℕ))⁻¹ - (Real.sqrt k)⁻¹) := by
        have hneg :
            (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
              Real.exp (-(t / 2))) =
              2 * ((Real.sqrt (k - 1 : ℕ))⁻¹ - (Real.sqrt k)⁻¹) := by
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
            (integral_exp_neg_half_log_cell (k := k - 1) (by omega : 1 ≤ k - 1))
        rw [intervalIntegral.integral_div, hneg]
        ring
      _ ≤ (2 / 3 : ℝ) * (Real.sqrt (k - 1 : ℕ))⁻¹ := by
        have hbase := natCast_mul_invSqrt_sub_invSqrt_le_invSqrt_pred
          (by omega : 2 ≤ k)
        have hmul := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 2 / 3)
        nlinarith

theorem suzukiCheckpointWeightedArchTailPrefix_nonneg_le (N : ℕ) :
    0 ≤ suzukiCheckpointWeightedArchTailPrefix N ∧
      suzukiCheckpointWeightedArchTailPrefix N ≤
        (8 / 3 : ℝ) * Real.sqrt (N + 2 : ℕ) := by
  rw [suzukiCheckpointWeightedArchTailPrefix]
  have hterm : ∀ k ∈ Finset.Ico 3 (N + 2),
      0 ≤ (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            suzukiCheckpointArchTail t) ∧
        (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            suzukiCheckpointArchTail t) ≤
          (4 / 3 : ℝ) * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro k hk
    have hk3 := (Finset.mem_Ico.mp hk).1
    have hcell := suzukiCheckpointWeightedArchTailCell_nonneg_le hk3
    refine ⟨hcell.1, hcell.2.trans ?_⟩
    have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have hsqrtPred : 0 < Real.sqrt ((k - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hpredpos
    have hsqrtK : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
    have hsqrtLe : Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
      have hnat : k ≤ 4 * (k - 1) := by omega
      have hcast : (k : ℝ) ≤ 4 * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      calc
        Real.sqrt (k : ℝ) ≤ Real.sqrt (4 * ((k - 1 : ℕ) : ℝ)) :=
          Real.sqrt_le_sqrt hcast
        _ = 2 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    rw [Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
    have hinv : (Real.sqrt (k - 1 : ℕ))⁻¹ ≤ 2 * (Real.sqrt k)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div,
        show 2 * (1 / Real.sqrt k) = 2 / Real.sqrt k by ring]
      rw [div_le_div_iff₀ hsqrtPred hsqrtK]
      nlinarith
    calc
      (2 / 3 : ℝ) * (Real.sqrt (k - 1 : ℕ))⁻¹ ≤
          (2 / 3 : ℝ) * (2 * (Real.sqrt k)⁻¹) := by gcongr
      _ = (4 / 3 : ℝ) * (Real.sqrt k)⁻¹ := by ring
  constructor
  · exact Finset.sum_nonneg fun k hk => (hterm k hk).1
  · calc
      (∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            suzukiCheckpointArchTail t)) ≤
        ∑ k ∈ Finset.Ico 3 (N + 2),
          (4 / 3 : ℝ) * ((k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        Finset.sum_le_sum fun k hk => (hterm k hk).2
      _ ≤ ∑ k ∈ Finset.Icc 1 (N + 2),
          (4 / 3 : ℝ) * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
          omega
        · intro k hk _
          positivity
      _ = (4 / 3 : ℝ) *
          (∑ k ∈ Finset.Icc 1 (N + 2), ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by
        rw [Finset.mul_sum]
      _ ≤ (4 / 3 : ℝ) * (2 * Real.sqrt (N + 2 : ℕ)) := by
        gcongr
        exact sum_rpow_neg_half_le (N + 2)
      _ = (8 / 3 : ℝ) * Real.sqrt (N + 2 : ℕ) := by ring

def suzukiCheckpointWeightedExpHalfPrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
      Real.exp (t / 2))

theorem sqrt_le_weightedExpHalfCell_le_sqrt_add_invSqrtPred
    {k : ℕ} (hk : 2 ≤ k) :
    Real.sqrt k ≤ 2 * (k : ℝ) * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) ∧
      2 * (k : ℝ) * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) ≤
        Real.sqrt k + (Real.sqrt (k - 1 : ℕ))⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hpredR : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  let a := Real.sqrt ((k - 1 : ℕ) : ℝ)
  let b := Real.sqrt (k : ℝ)
  have ha : 0 < a := Real.sqrt_pos.mpr hpredR
  have hb : 0 < b := Real.sqrt_pos.mpr hkR
  have ha2 : a ^ 2 = ((k - 1 : ℕ) : ℝ) := Real.sq_sqrt hpredR.le
  have hb2 : b ^ 2 = (k : ℝ) := Real.sq_sqrt hkR.le
  have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hab : a ≤ b := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le k 1))
  have hsumpos : 0 < a + b := add_pos ha hb
  have hsumpos' : 0 < b + a := add_pos hb ha
  have hgap : (b - a) * (b + a) = 1 := by
    nlinarith [ha2, hb2, hcast]
  have hdelta : b - a = 1 / (b + a) := by
    exact (eq_div_iff hsumpos'.ne').2 hgap
  change b ≤ 2 * (k : ℝ) * (b - a) ∧
    2 * (k : ℝ) * (b - a) ≤ b + a⁻¹
  rw [hdelta, ← hb2]
  have hform : 2 * b ^ 2 * (1 / (b + a)) = 2 * b ^ 2 / (b + a) := by ring
  rw [hform]
  constructor
  · apply (le_div_iff₀ hsumpos').2
    nlinarith
  · have herr : 2 * b ^ 2 / (b + a) - b = b / (b + a) ^ 2 := by
      field_simp [hsumpos.ne']
      nlinarith [hgap]
    have herrorle : b / (b + a) ^ 2 ≤ a⁻¹ := by
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ (sq_pos_of_pos hsumpos') ha).2
      nlinarith [ha.le, hb.le]
    linarith

theorem unitRieszSqrtPrefixMass_eq_sum_Ico_one (m : ℕ) :
    unitRieszSqrtPrefixMass m =
      ∑ k ∈ Finset.Ico 1 (m + 1), Real.sqrt k := by
  rw [unitRieszSqrtPrefixMass, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  congr 1
  ring

theorem suzukiCheckpointWeightedExpHalfPrefix_eq_cellFormula (N : ℕ) :
    suzukiCheckpointWeightedExpHalfPrefix N =
      ∑ k ∈ Finset.Ico 3 (N + 2),
        2 * (k : ℝ) * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) := by
  rw [suzukiCheckpointWeightedExpHalfPrefix]
  apply Finset.sum_congr rfl
  intro k hk
  have hk3 := (Finset.mem_Ico.mp hk).1
  have hcell :
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ), Real.exp (t / 2)) =
        2 * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (integral_exp_half_log_cell (k := k - 1) (by omega : 1 ≤ k - 1))
  rw [hcell]
  ring

theorem abs_polar_sub_weightedExpHalfPrefix_le
    {N : ℕ} (hN : 1 ≤ N) :
    |(2 / 3 : ℝ) * (N + 2 : ℕ) * Real.sqrt (N + 2 : ℕ) -
        suzukiCheckpointWeightedExpHalfPrefix N| ≤
      5 * Real.sqrt (N + 2 : ℕ) + 3 := by
  let X : ℕ := N + 2
  let S : ℝ := ∑ k ∈ Finset.Ico 3 X, Real.sqrt k
  let E : ℝ := ∑ k ∈ Finset.Ico 3 X,
    (2 * (k : ℝ) * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - Real.sqrt k)
  have hX3 : 3 ≤ X := by dsimp [X]; omega
  have hprefix : unitRieszSqrtPrefixMass (X - 1) = 1 + Real.sqrt 2 + S := by
    rw [unitRieszSqrtPrefixMass_eq_sum_Ico_one]
    have hsum := Finset.sum_Ico_consecutive (fun k : ℕ => Real.sqrt k)
      (show 1 ≤ 3 by omega) hX3
    have hXsub : X - 1 + 1 = X := Nat.sub_add_cancel (by omega : 1 ≤ X)
    rw [hXsub]
    rw [← hsum]
    norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, S]
  have hSupper : S ≤ (2 / 3 : ℝ) * X * Real.sqrt X - 1 - Real.sqrt 2 := by
    have h := unitRieszSqrtPrefixMass_upper (X - 1)
    rw [hprefix] at h
    have hXsub : (((X - 1 : ℕ) : ℝ) + 1) = X := by
      rw [Nat.cast_sub (by omega : 1 ≤ X)]
      norm_num
    rw [hXsub] at h
    nlinarith
  have hSlower : (2 / 3 : ℝ) * (X - 1 : ℕ) * Real.sqrt X - 1 - Real.sqrt 2 ≤ S := by
    have h := unitRieszSqrtPrefixMass_lower (X - 1)
    rw [hprefix] at h
    have hXsub : (((X - 1 : ℕ) : ℝ) + 1) = X := by
      rw [Nat.cast_sub (by omega : 1 ≤ X)]
      norm_num
    rw [hXsub] at h
    nlinarith
  have hE0 : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro k hk
    have hk3 := (Finset.mem_Ico.mp hk).1
    exact sub_nonneg.mpr
      (sqrt_le_weightedExpHalfCell_le_sqrt_add_invSqrtPred
        (by omega : 2 ≤ k)).1
  have hEle : E ≤ 4 * Real.sqrt X := by
    have hterm : ∀ k ∈ Finset.Ico 3 X,
        2 * (k : ℝ) * (Real.sqrt k - Real.sqrt (k - 1 : ℕ)) - Real.sqrt k ≤
          2 * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      intro k hk
      have hk3 := (Finset.mem_Ico.mp hk).1
      have hcell := (sqrt_le_weightedExpHalfCell_le_sqrt_add_invSqrtPred
        (by omega : 2 ≤ k)).2
      have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < k - 1)
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      have hsqrtPred : 0 < Real.sqrt ((k - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hpredpos
      have hsqrtK : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
      have hsqrtLe : Real.sqrt k ≤ 2 * Real.sqrt (k - 1 : ℕ) := by
        have hnat : k ≤ 4 * (k - 1) := by omega
        have hcast : (k : ℝ) ≤ 4 * ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
        calc
          Real.sqrt (k : ℝ) ≤ Real.sqrt (4 * ((k - 1 : ℕ) : ℝ)) :=
            Real.sqrt_le_sqrt hcast
          _ = 2 * Real.sqrt ((k - 1 : ℕ) : ℝ) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
      have hinv : (Real.sqrt (k - 1 : ℕ))⁻¹ ≤ 2 * (Real.sqrt k)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div,
          show 2 * (1 / Real.sqrt k) = 2 / Real.sqrt k by ring]
        rw [div_le_div_iff₀ hsqrtPred hsqrtK]
        nlinarith
      rw [Real.rpow_neg hkpos.le, ← Real.sqrt_eq_rpow]
      linarith
    calc
      E ≤ ∑ k ∈ Finset.Ico 3 X, 2 * ((k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        Finset.sum_le_sum fun k hk => hterm k hk
      _ ≤ ∑ k ∈ Finset.Icc 1 X, 2 * ((k : ℝ) ^ (-(1 / 2 : ℝ))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
          omega
        · intro k hk _
          positivity
      _ = 2 * (∑ k ∈ Finset.Icc 1 X, ((k : ℝ) ^ (-(1 / 2 : ℝ)))) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (2 * Real.sqrt X) := by
        gcongr
        exact sum_rpow_neg_half_le X
      _ = 4 * Real.sqrt X := by ring
  have hlead : suzukiCheckpointWeightedExpHalfPrefix N = S + E := by
    rw [suzukiCheckpointWeightedExpHalfPrefix_eq_cellFormula]
    dsimp [S, E, X]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hD0 : 0 ≤ (2 / 3 : ℝ) * X * Real.sqrt X - S := by
    linarith [Real.sqrt_nonneg (2 : ℝ)]
  have hDle : (2 / 3 : ℝ) * X * Real.sqrt X - S ≤
      (2 / 3 : ℝ) * Real.sqrt X + 3 := by
    have hXcast : (((X - 1 : ℕ) : ℝ)) = (X : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ X)]
      norm_num
    rw [hXcast] at hSlower
    have hsqrt2le : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    linarith
  rw [show N + 2 = X by rfl, hlead]
  calc
    |(2 / 3 : ℝ) * X * Real.sqrt X - (S + E)| =
        |((2 / 3 : ℝ) * X * Real.sqrt X - S) - E| := by ring_nf
    _ ≤ |(2 / 3 : ℝ) * X * Real.sqrt X - S| + |E| := abs_sub _ _
    _ = ((2 / 3 : ℝ) * X * Real.sqrt X - S) + E := by
      rw [abs_of_nonneg hD0, abs_of_nonneg hE0]
    _ ≤ ((2 / 3 : ℝ) * Real.sqrt X + 3) + 4 * Real.sqrt X := by linarith
    _ ≤ 5 * Real.sqrt X + 3 := by nlinarith [Real.sqrt_nonneg (X : ℝ)]

theorem integral_screwRegularKernel_eq_expHalf_sub_archTail
    {k : ℕ} (hk : 3 ≤ k) :
    (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        screwRegularKernel t) =
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        Real.exp (t / 2)) -
      (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
        suzukiCheckpointArchTail t) := by
  have hpredpos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hlogle : Real.log ((k - 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) :=
    (Real.log_le_log_iff hpredpos hkpos).mpr (by exact_mod_cast (Nat.sub_le k 1))
  have hlog2 : Real.log 2 ≤ Real.log ((k - 1 : ℕ) : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact hpredpos
    · exact_mod_cast (by omega : 2 ≤ k - 1)
  have htailCont : ContinuousOn suzukiCheckpointArchTail
      (Icc (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t ht
      have htpos : 0 < t := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
        (hlog2.trans ht.1)
      exact ne_of_gt (one_sub_exp_neg_two_mul_pos htpos)
  have htailInt : IntervalIntegrable suzukiCheckpointArchTail volume
      (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ)) := by
    have htailCont' : ContinuousOn suzukiCheckpointArchTail
        (uIcc (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ))) := by
      simpa only [uIcc_of_le hlogle] using htailCont
    exact htailCont'.intervalIntegrable
  have hexpInt : IntervalIntegrable (fun t : ℝ => Real.exp (t / 2)) volume
      (Real.log ((k - 1 : ℕ) : ℝ)) (Real.log (k : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (t / 2)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hexpInt htailInt]
  apply intervalIntegral.integral_congr
  intro t ht
  rfl

theorem suzukiCheckpointWeightedArchRenormalization_eq_lead_add_tail (N : ℕ) :
    suzukiCheckpointWeightedArchRenormalization N =
      ((2 / 3 : ℝ) * (N + 2 : ℕ) * Real.sqrt (N + 2 : ℕ) -
        suzukiCheckpointWeightedExpHalfPrefix N) -
      ArithmeticFunction.vonMangoldt 2 * Real.sqrt 2 +
      suzukiCheckpointWeightedArchTailPrefix N := by
  have hsum :
      (∑ k ∈ Finset.Ico 3 (N + 2), (k : ℝ) *
          (∫ t in Real.log ((k - 1 : ℕ) : ℝ)..Real.log (k : ℝ),
            screwRegularKernel t)) =
        suzukiCheckpointWeightedExpHalfPrefix N -
          suzukiCheckpointWeightedArchTailPrefix N := by
    rw [suzukiCheckpointWeightedExpHalfPrefix,
      suzukiCheckpointWeightedArchTailPrefix, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_screwRegularKernel_eq_expHalf_sub_archTail
      (Finset.mem_Ico.mp hk).1]
    ring
  rw [suzukiCheckpointWeightedArchRenormalization, hsum]
  ring

theorem abs_suzukiCheckpointWeightedArchRenormalization_le
    {N : ℕ} (hN : 1 ≤ N) :
    |suzukiCheckpointWeightedArchRenormalization N| ≤
      8 * Real.sqrt (N + 2 : ℕ) + 5 := by
  let lead : ℝ :=
    (2 / 3 : ℝ) * (N + 2 : ℕ) * Real.sqrt (N + 2 : ℕ) -
      suzukiCheckpointWeightedExpHalfPrefix N
  let atom : ℝ := ArithmeticFunction.vonMangoldt 2 * Real.sqrt 2
  let tail : ℝ := suzukiCheckpointWeightedArchTailPrefix N
  have hlead : |lead| ≤ 5 * Real.sqrt (N + 2 : ℕ) + 3 := by
    exact abs_polar_sub_weightedExpHalfPrefix_le hN
  have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt 2 :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hvmle : ArithmeticFunction.vonMangoldt 2 ≤ 1 := by
    calc
      ArithmeticFunction.vonMangoldt 2 ≤ Real.log 2 :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        norm_num at this
        exact this
  have hsqrt2le : Real.sqrt 2 ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hatom0 : 0 ≤ atom := by
    dsimp [atom]
    positivity
  have hatomle : atom ≤ 2 := by
    dsimp [atom]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have htail := suzukiCheckpointWeightedArchTailPrefix_nonneg_le N
  have htail0 : 0 ≤ tail := by exact htail.1
  have htaille : tail ≤ (8 / 3 : ℝ) * Real.sqrt (N + 2 : ℕ) := by
    exact htail.2
  rw [suzukiCheckpointWeightedArchRenormalization_eq_lead_add_tail]
  change |lead + -atom + tail| ≤ _
  calc
    |lead + -atom + tail| ≤ |lead| + |-atom| + |tail| := abs_add_three _ _ _
    _ = |lead| + atom + tail := by rw [abs_neg, abs_of_nonneg hatom0, abs_of_nonneg htail0]
    _ ≤ (5 * Real.sqrt (N + 2 : ℕ) + 3) + 2 +
        (8 / 3 : ℝ) * Real.sqrt (N + 2 : ℕ) := by linarith
    _ ≤ 8 * Real.sqrt (N + 2 : ℕ) + 5 := by
      nlinarith [Real.sqrt_nonneg ((N + 2 : ℕ) : ℝ)]

theorem tendsto_suzukiCheckpointWeightedArchRenormalization_div_zero :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointWeightedArchRenormalization N / (N + 2 : ℕ))
      atTop (nhds 0) := by
  have hsqrt :
      Tendsto (fun N : ℕ =>
        Real.sqrt ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ))
        atTop (nhds 0) :=
    tendsto_sqrt_natCast_div_natCast_atTop_zero.comp
      (Filter.tendsto_add_atTop_nat 2)
  have hinv :
      Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 2 : ℕ) : ℝ))
        atTop (nhds 0) :=
    tendsto_inv_natCast_atTop_zero.comp (Filter.tendsto_add_atTop_nat 2)
  have hmajor :
      Tendsto (fun N : ℕ =>
        8 * (Real.sqrt ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) +
          5 * ((1 : ℝ) / ((N + 2 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    simpa using (hsqrt.const_mul 8).add (hinv.const_mul 5)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hXpos : (0 : ℝ) < ((N + 2 : ℕ) : ℝ) := by positivity
      rw [abs_div, abs_of_pos hXpos]
      calc
        |suzukiCheckpointWeightedArchRenormalization N| / ((N + 2 : ℕ) : ℝ) ≤
            (8 * Real.sqrt (N + 2 : ℕ) + 5) / ((N + 2 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right
            (abs_suzukiCheckpointWeightedArchRenormalization_le hN) hXpos.le
        _ = 8 * (Real.sqrt ((N + 2 : ℕ) : ℝ) / ((N + 2 : ℕ) : ℝ)) +
            5 * ((1 : ℝ) / ((N + 2 : ℕ) : ℝ)) := by ring) hmajor

theorem tendsto_normalizedSignedCurvatureFirstMoment_sub_unitRieszCenter_zero :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointNormalizedSignedCurvatureFirstMoment N -
        unitRieszCompletedCoherentBarycenter (N + 2) 0)
      atTop (nhds 0) := by
  have hneg := tendsto_suzukiCheckpointWeightedArchRenormalization_div_zero.neg
  simpa only [neg_zero] using hneg.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [normalizedSignedCurvatureFirstMoment_eq_unitRieszCenter_sub_arch hN]
    ring)

theorem tendsto_normalizedSignedCurvatureFirstMoment_iff_unitRieszCenter
    (L : ℝ) :
    Tendsto suzukiCheckpointNormalizedSignedCurvatureFirstMoment atTop (nhds L) ↔
      Tendsto (fun N : ℕ =>
        unitRieszCompletedCoherentBarycenter (N + 2) 0) atTop (nhds L) := by
  have hdiff :=
    tendsto_normalizedSignedCurvatureFirstMoment_sub_unitRieszCenter_zero
  constructor
  · intro hcurv
    have h := hcurv.sub hdiff
    simpa only [sub_zero] using h.congr'
      (Eventually.of_forall fun N => by ring)
  · intro hcenter
    have h := hdiff.add hcenter
    simpa only [zero_add] using h.congr'
      (Eventually.of_forall fun N => by ring)

end RHTower
