import GaloisForLFunctions.RHTower.CCMFUSuzukiSignedCurvatureMeasure
import GaloisForLFunctions.RHTower.LogFloorExpBridge

/-!
# Exact triangular-curvature reduction of the CCM--FU affine mixture

The canonical floor-selected affine current is converted exactly into three finite marked
responses: a fixed affine memory, the signed Suzuki curvature cells paired with the literal
third-grade triangular reporter, and positive endpoint-reset packets paired with the associated
error kernel. The affine and reset channels are then proved uniformly bounded without any RH
input.

Consequently the canonical CCM--FU affine-tail premise is equivalent to uniform boundedness of
one explicit finite signed triangular curvature transform. Combined with the existing CCM--FU
endpoint, that transform bound is sufficient for RH. No Jordan decomposition or absolute-value
majorization is applied to the signed curvature channel.
-/

noncomputable section

namespace RHTower

open Set MeasureTheory
open GaloisForLFunctions.RHTower

def suzukiCheckpointBaseAffineCurrent (t : ℝ) : ℝ :=
  suzukiPsi (Real.log 2) +
    suzukiCheckpointAffineSlope 2 * (t - Real.log 2)

def suzukiCheckpointSignedCurvatureHingeCurrent (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
    suzukiCheckpointSignedCurvatureCell j *
      (t - Real.log ((j + 1 : ℕ) : ℝ))

def suzukiCheckpointResetPrefixCurrent (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
    suzukiCheckpointEventCurvatureJump j

theorem suzukiCheckpointGlobalAffineCurrent_eq_base_add_hinge_add_reset
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiCheckpointGlobalAffineCurrent t =
      suzukiCheckpointBaseAffineCurrent t +
        suzukiCheckpointSignedCurvatureHingeCurrent t +
          suzukiCheckpointResetPrefixCurrent t := by
  obtain ⟨hN, _htcell⟩ := suzukiCheckpointEventIndex_two_le_and_mem_cell ht
  have hleft := (globalAffineCurrent_eq_leftJet_and_curvature_mem_unitInterval ht).1
  have hpsi := suzukiPsi_log_nat_eq_affine_add_signedCurvatureGreen_add_resets hN
  have hslope := suzukiCheckpointAffineSlope_eq_base_add_sum_signedCurvatureCell hN
  have hslopeDef :
      suzukiCheckpointReservoirDeriv
          (Real.log (suzukiCheckpointEventIndex t : ℝ)) -
        suzukiCheckpointMass (suzukiCheckpointEventIndex t) =
          suzukiCheckpointAffineSlope (suzukiCheckpointEventIndex t) := rfl
  have hsum :
      (∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
          suzukiCheckpointSignedCurvatureCell j *
            (Real.log (suzukiCheckpointEventIndex t : ℝ) -
              Real.log ((j + 1 : ℕ) : ℝ))) +
        (∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
          suzukiCheckpointSignedCurvatureCell j) *
            (t - Real.log (suzukiCheckpointEventIndex t : ℝ)) =
      ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
        suzukiCheckpointSignedCurvatureCell j *
          (t - Real.log ((j + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hleft]
  unfold suzukiCheckpointLeftAffineJet suzukiCheckpointBaseAffineCurrent
    suzukiCheckpointSignedCurvatureHingeCurrent suzukiCheckpointResetPrefixCurrent
  rw [hpsi]
  rw [hslopeDef, hslope]
  unfold suzukiCheckpointSignedCurvatureGreenPotential
  linear_combination hsum

theorem suzukiCheckpointSignedCurvatureHingeCurrent_eq_fixed_sum_max
    {H t : ℝ} (_ht1 : 1 ≤ t) (htH : t ≤ H) :
    suzukiCheckpointSignedCurvatureHingeCurrent t =
      ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        suzukiCheckpointSignedCurvatureCell j *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)) := by
  have hsub : Finset.Ico 2 (suzukiCheckpointEventIndex t) ⊆
      Finset.Ico 2 (suzukiCheckpointEventIndex H) := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    apply Finset.mem_Ico.mpr
    refine ⟨hj'.1, ?_⟩
    have hjlog : Real.log ((j + 1 : ℕ) : ℝ) ≤ t := by
      apply (log_le_iff_le_floor (by omega : 1 ≤ j + 1) t).2
      simpa [suzukiCheckpointEventIndex] using (show j + 1 ≤ suzukiCheckpointEventIndex t by omega)
    have hjH : Real.log ((j + 1 : ℕ) : ℝ) ≤ H := hjlog.trans htH
    have := (log_le_iff_le_floor (by omega : 1 ≤ j + 1) H).1 hjH
    have hlt : j < ⌊Real.exp H⌋₊ := Nat.lt_of_succ_le this
    simpa [suzukiCheckpointEventIndex] using hlt
  unfold suzukiCheckpointSignedCurvatureHingeCurrent
  calc
    (∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
        suzukiCheckpointSignedCurvatureCell j *
          (t - Real.log ((j + 1 : ℕ) : ℝ))) =
      ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
        suzukiCheckpointSignedCurvatureCell j *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have hjlog : Real.log ((j + 1 : ℕ) : ℝ) ≤ t := by
          apply (log_le_iff_le_floor (by omega : 1 ≤ j + 1) t).2
          simpa [suzukiCheckpointEventIndex] using
            (show j + 1 ≤ suzukiCheckpointEventIndex t by omega)
        rw [max_eq_right (sub_nonneg.mpr hjlog)]
    _ = ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        suzukiCheckpointSignedCurvatureCell j *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_subset hsub
      intro j hjH hjnot
      have hjH' := Finset.mem_Ico.mp hjH
      have hjnotlt : ¬ j < suzukiCheckpointEventIndex t := by
        intro hjlt
        exact hjnot (Finset.mem_Ico.mpr ⟨hjH'.1, hjlt⟩)
      have hjfloor : ¬ j + 1 ≤ suzukiCheckpointEventIndex t := by omega
      have hjlog : ¬ Real.log ((j + 1 : ℕ) : ℝ) ≤ t := by
        intro h
        exact hjfloor ((log_le_iff_le_floor (by omega : 1 ≤ j + 1) t).1 h)
      rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge hjlog)), mul_zero]

theorem suzukiCheckpointResetPrefixCurrent_eq_fixed_sum_indicator
    {H t : ℝ} (_ht1 : 1 ≤ t) (htH : t ≤ H) :
    suzukiCheckpointResetPrefixCurrent t =
      ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then
          suzukiCheckpointEventCurvatureJump j else 0 := by
  have hsub : Finset.Ico 2 (suzukiCheckpointEventIndex t) ⊆
      Finset.Ico 2 (suzukiCheckpointEventIndex H) := by
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    apply Finset.mem_Ico.mpr
    refine ⟨hj'.1, ?_⟩
    have hjlog : Real.log ((j + 1 : ℕ) : ℝ) ≤ t := by
      apply (log_le_iff_le_floor (by omega : 1 ≤ j + 1) t).2
      simpa [suzukiCheckpointEventIndex] using
        (show j + 1 ≤ suzukiCheckpointEventIndex t by omega)
    have hjH : Real.log ((j + 1 : ℕ) : ℝ) ≤ H := hjlog.trans htH
    have hjfloor := (log_le_iff_le_floor (by omega : 1 ≤ j + 1) H).1 hjH
    have hlt : j < ⌊Real.exp H⌋₊ := Nat.lt_of_succ_le hjfloor
    simpa [suzukiCheckpointEventIndex] using hlt
  unfold suzukiCheckpointResetPrefixCurrent
  calc
    (∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
        suzukiCheckpointEventCurvatureJump j) =
      ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex t),
        if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then
          suzukiCheckpointEventCurvatureJump j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_Ico.mp hj
        have hjlog : Real.log ((j + 1 : ℕ) : ℝ) ≤ t := by
          apply (log_le_iff_le_floor (by omega : 1 ≤ j + 1) t).2
          simpa [suzukiCheckpointEventIndex] using
            (show j + 1 ≤ suzukiCheckpointEventIndex t by omega)
        rw [if_pos hjlog]
    _ = ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then
          suzukiCheckpointEventCurvatureJump j else 0 := by
      apply Finset.sum_subset hsub
      intro j hjH hjnot
      have hjH' := Finset.mem_Ico.mp hjH
      have hjnotlt : ¬ j < suzukiCheckpointEventIndex t := by
        intro hjlt
        exact hjnot (Finset.mem_Ico.mpr ⟨hjH'.1, hjlt⟩)
      have hjfloor : ¬ j + 1 ≤ suzukiCheckpointEventIndex t := by omega
      have hjlog : ¬ Real.log ((j + 1 : ℕ) : ℝ) ≤ t := by
        intro h
        exact hjfloor ((log_le_iff_le_floor (by omega : 1 ≤ j + 1) t).1 h)
      rw [if_neg hjlog]

theorem ccmThirdGradeCesaroRectangularMix_hinge_eq_triangularWeight
    {b h H : ℝ} (hb : 0 < b) (hbh : b ≤ h) (hhH : h ≤ H) :
    (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        max 0 (t - h)) +
      (32 / H ^ 4) * max 0 (H - h) =
        ccmGuinandWeilThirdGradeCesaroTriangularWeight H h := by
  have hh : 0 < h := hb.trans_le hbh
  have hH : 0 < H := hh.trans_le hhH
  let f : ℝ → ℝ := fun t =>
    ccmThirdGradeCesaroRectangularMixDensity H t * max 0 (t - h)
  have hfCont : ContinuousOn f (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    have hdensity : ContinuousAt (ccmThirdGradeCesaroRectangularMixDensity H) t := by
      unfold ccmThirdGradeCesaroRectangularMixDensity
      exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
        (continuousAt_const.mul (continuousAt_id.pow 5))
        (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0)))
    exact (hdensity.mul
      ((continuous_const.max (continuous_id.sub continuous_const)).continuousAt)).continuousWithinAt
  have hfbh : IntervalIntegrable f volume b h := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbh]
    exact hfCont.mono (Set.Icc_subset_Icc_right hhH)
  have hfhH : IntervalIntegrable f volume h H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hhH]
    exact hfCont.mono (Set.Icc_subset_Icc_left hbh)
  have hzero : (∫ t in b..h, f t) = 0 := by
    calc
      (∫ t in b..h, f t) = ∫ _t in b..h, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hbh] at ht
        dsimp only [f]
        rw [max_eq_left (sub_nonpos.mpr ht.2), mul_zero]
      _ = 0 := by simp
  have hright : (∫ t in h..H, f t) =
      ∫ t in h..H,
        ccmThirdGradeCesaroRectangularMixDensity H t * (t - h) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hhH] at ht
    dsimp only [f]
    rw [max_eq_right (sub_nonneg.mpr ht.1)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfbh hfhH
  have hend : max 0 (H - h) = H - h := max_eq_right (sub_nonneg.mpr hhH)
  rw [← hsplit, hzero, zero_add, hright, hend]
  exact (ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_rectangularMixture hh hhH).symm

theorem ccmThirdGradeCesaroRectangularMix_step_eq_errorKernel
    {b h H : ℝ} (hb : 0 < b) (hbh : b ≤ h) (hhH : h ≤ H) :
    (∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        (if h ≤ t then (1 : ℝ) else 0)) +
      (32 / H ^ 4) * (if h ≤ H then (1 : ℝ) else 0) =
        ccmGuinandWeilThirdGradeCesaroErrorKernel H h := by
  have hh : 0 < h := hb.trans_le hbh
  have hH : 0 < H := hh.trans_le hhH
  let f : ℝ → ℝ := fun t =>
    ccmThirdGradeCesaroRectangularMixDensity H t *
      (if h ≤ t then (1 : ℝ) else 0)
  let density : ℝ → ℝ := ccmThirdGradeCesaroRectangularMixDensity H
  have hdensityCont : ContinuousOn density (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold density ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hdensityInt : IntervalIntegrable density volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hbh.trans hhH)]
    exact hdensityCont
  have hfInt : IntervalIntegrable f volume b H := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hbh.trans hhH)]
    have hdensOn : IntegrableOn density (Set.Icc b H) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (hbh.trans hhH)).1 hdensityInt
    have hind := hdensOn.indicator (t := Set.Ici h) measurableSet_Ici
    apply hind.congr_fun
    · intro t ht
      dsimp only [f, density]
      by_cases hht : h ≤ t
      · simp [hht]
      · simp [hht]
    · exact measurableSet_Icc
  have hfbh : IntervalIntegrable f volume b h := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbh]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (hbh.trans hhH)).1 hfInt).mono_set
      (Set.Icc_subset_Icc_right hhH)
  have hfhH : IntervalIntegrable f volume h H := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hhH]
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (hbh.trans hhH)).1 hfInt).mono_set
      (Set.Icc_subset_Icc_left hbh)
  have hzero : (∫ t in b..h, f t) = 0 := by
    have haene : ∀ᵐ t : ℝ ∂volume, t ≠ h := by
      rw [MeasureTheory.ae_iff]
      simpa using
        (MeasureTheory.NullSingletonClass.measure_singleton (μ := volume) h)
    calc
      (∫ t in b..h, f t) = ∫ _t in b..h, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [haene] with t hth ht
        rw [Set.uIoc_of_le hbh] at ht
        have hnot : ¬ h ≤ t := by
          intro hle
          exact hth (le_antisymm ht.2 hle)
        simp only [f, hnot, ↓reduceIte, mul_zero]
      _ = 0 := by simp
  have hright : (∫ t in h..H, f t) =
      ∫ t in h..H, density t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hhH] at ht
    dsimp only [f]
    rw [if_pos ht.1, mul_one]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfbh hfhH
  rw [← hsplit, hzero, zero_add, hright, if_pos hhH]
  dsimp only [density]
  simpa using integral_rectangularMixDensity_add_endpoint_eq_errorKernel hh hhH

/-- Marked response of the fixed affine memory at the first physical wall. -/
def suzukiCheckpointBaseAffineMixture (H : ℝ) : ℝ :=
  (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
      suzukiCheckpointBaseAffineCurrent t) +
    (32 / H ^ 4) * suzukiCheckpointBaseAffineCurrent H

/-- The finite signed-curvature transform seen by the third-grade reporter. -/
def suzukiCheckpointTriangularCurvatureTransform (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
    suzukiCheckpointSignedCurvatureCell j *
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H
        (Real.log ((j + 1 : ℕ) : ℝ))

/-- The absolutely summable reset channel seen by the third-grade error kernel. -/
def suzukiCheckpointResetErrorTransform (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
    suzukiCheckpointEventCurvatureJump j *
      ccmGuinandWeilThirdGradeCesaroErrorKernel H
        (Real.log ((j + 1 : ℕ) : ℝ))

theorem suzukiCheckpointBaseAffineCurrent_eq_at_one_add
    (t : ℝ) :
    suzukiCheckpointBaseAffineCurrent t =
      suzukiCheckpointBaseAffineCurrent 1 +
        suzukiCheckpointAffineSlope 2 * (t - 1) := by
  unfold suzukiCheckpointBaseAffineCurrent
  ring

/-- The fixed affine memory has a closed response formula. -/
theorem suzukiCheckpointBaseAffineMixture_eq
    {H : ℝ} (hH : 1 ≤ H) :
    suzukiCheckpointBaseAffineMixture H =
      suzukiCheckpointBaseAffineCurrent 1 *
          ccmGuinandWeilThirdGradeCesaroErrorKernel H 1 +
        suzukiCheckpointAffineSlope 2 * (32 - 32 / H) := by
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  let density : ℝ → ℝ := ccmThirdGradeCesaroRectangularMixDensity H
  have hdensityCont : ContinuousOn density (Set.Icc 1 H) := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    unfold density ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH0.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hρ : IntervalIntegrable density volume 1 H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hH]
    exact hdensityCont
  have hρlin : IntervalIntegrable (fun t => density t * (t - 1)) volume 1 H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hH]
    exact hdensityCont.mul (continuousOn_id.sub continuousOn_const)
  have hbulk :
      (∫ t in (1 : ℝ)..H, density t * suzukiCheckpointBaseAffineCurrent t) =
        suzukiCheckpointBaseAffineCurrent 1 * (∫ t in (1 : ℝ)..H, density t) +
          suzukiCheckpointAffineSlope 2 *
            (∫ t in (1 : ℝ)..H, density t * (t - 1)) := by
    calc
      _ = ∫ t in (1 : ℝ)..H,
          suzukiCheckpointBaseAffineCurrent 1 * density t +
            suzukiCheckpointAffineSlope 2 * (density t * (t - 1)) := by
              apply intervalIntegral.integral_congr
              intro t _ht
              calc
                density t * suzukiCheckpointBaseAffineCurrent t =
                    density t * (suzukiCheckpointBaseAffineCurrent 1 +
                      suzukiCheckpointAffineSlope 2 * (t - 1)) := by
                        rw [suzukiCheckpointBaseAffineCurrent_eq_at_one_add t]
                _ = _ := by ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hρ.const_mul (suzukiCheckpointBaseAffineCurrent 1))
          (hρlin.const_mul (suzukiCheckpointAffineSlope 2)),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hmass := integral_rectangularMixDensity_add_endpoint_eq_errorKernel
    (H := H) (h := (1 : ℝ)) zero_lt_one hH
  have hfirst := integral_rectangularMixDensity_mul_sub_add_endpoint_eq
    (b := (1 : ℝ)) (H := H) zero_lt_one hH
  unfold suzukiCheckpointBaseAffineMixture
  dsimp only [density] at hbulk
  have hend := suzukiCheckpointBaseAffineCurrent_eq_at_one_add H
  rw [hbulk, hend]
  linear_combination
    suzukiCheckpointBaseAffineCurrent 1 * hmass +
      suzukiCheckpointAffineSlope 2 * hfirst

theorem one_lt_log_event_succ_and_log_event_succ_le
    {H : ℝ} {j : ℕ} (hj : j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H)) :
    1 < Real.log ((j + 1 : ℕ) : ℝ) ∧
      Real.log ((j + 1 : ℕ) : ℝ) ≤ H := by
  have hjIco := Finset.mem_Ico.mp hj
  have hthree : (3 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ j + 1 by omega)
  have hlogOne : 1 < Real.log ((j + 1 : ℕ) : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).2
    exact Real.exp_one_lt_three.trans_le hthree
  have hfloor : j + 1 ≤ suzukiCheckpointEventIndex H := by omega
  have hlogH : Real.log ((j + 1 : ℕ) : ℝ) ≤ H := by
    apply (log_le_iff_le_floor (by omega : 1 ≤ j + 1) H).2
    simpa [suzukiCheckpointEventIndex] using hfloor
  exact ⟨hlogOne, hlogH⟩

/-- The hinge channel is exactly the finite triangular transform. -/
theorem suzukiCheckpointSignedCurvatureHingeMixture_eq_triangularTransform
    {H : ℝ} (hH : 2 ≤ H) :
    (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        suzukiCheckpointSignedCurvatureHingeCurrent t) +
      (32 / H ^ 4) * suzukiCheckpointSignedCurvatureHingeCurrent H =
        suzukiCheckpointTriangularCurvatureTransform H := by
  have h1H : (1 : ℝ) ≤ H := one_le_two.trans hH
  have hH0 : 0 < H := zero_lt_one.trans_le h1H
  let s := Finset.Ico 2 (suzukiCheckpointEventIndex H)
  have htermInt : ∀ j ∈ s, IntervalIntegrable
      (fun t : ℝ => suzukiCheckpointSignedCurvatureCell j *
        (ccmThirdGradeCesaroRectangularMixDensity H t *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)))) volume 1 H := by
    intro j _hj
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le h1H] at ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    have hdensity : ContinuousAt (ccmThirdGradeCesaroRectangularMixDensity H) t := by
      unfold ccmThirdGradeCesaroRectangularMixDensity
      exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
        (continuousAt_const.mul (continuousAt_id.pow 5))
        (mul_ne_zero hH0.ne' (pow_ne_zero 5 ht0)))
    exact (continuousAt_const.mul (hdensity.mul
      (continuous_const.max (continuous_id.sub continuous_const)).continuousAt)).continuousWithinAt
  have hbulk :
      (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          suzukiCheckpointSignedCurvatureHingeCurrent t) =
        ∑ j ∈ s, suzukiCheckpointSignedCurvatureCell j *
          (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
            max 0 (t - Real.log ((j + 1 : ℕ) : ℝ))) := by
    calc
      _ = ∫ t in (1 : ℝ)..H,
          ∑ j ∈ s, suzukiCheckpointSignedCurvatureCell j *
            (ccmThirdGradeCesaroRectangularMixDensity H t *
              max 0 (t - Real.log ((j + 1 : ℕ) : ℝ))) := by
                apply intervalIntegral.integral_congr
                intro t ht
                rw [Set.uIcc_of_le h1H] at ht
                change ccmThirdGradeCesaroRectangularMixDensity H t *
                    suzukiCheckpointSignedCurvatureHingeCurrent t = _
                rw [suzukiCheckpointSignedCurvatureHingeCurrent_eq_fixed_sum_max
                  ht.1 ht.2]
                dsimp only [s]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                ring
      _ = ∑ j ∈ s, ∫ t in (1 : ℝ)..H,
          suzukiCheckpointSignedCurvatureCell j *
            (ccmThirdGradeCesaroRectangularMixDensity H t *
              max 0 (t - Real.log ((j + 1 : ℕ) : ℝ))) := by
                exact intervalIntegral.integral_finsetSum htermInt
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [intervalIntegral.integral_const_mul]
  have hend := suzukiCheckpointSignedCurvatureHingeCurrent_eq_fixed_sum_max
    (H := H) (t := H) h1H le_rfl
  unfold suzukiCheckpointTriangularCurvatureTransform
  rw [hbulk, hend]
  dsimp only [s]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjbounds := one_lt_log_event_succ_and_log_event_succ_le hj
  have hresponse := ccmThirdGradeCesaroRectangularMix_hinge_eq_triangularWeight
    (b := (1 : ℝ)) (h := Real.log ((j + 1 : ℕ) : ℝ)) (H := H)
    zero_lt_one hjbounds.1.le hjbounds.2
  linear_combination suzukiCheckpointSignedCurvatureCell j * hresponse

/-- The reset-prefix channel is exactly the finite error-kernel transform. -/
theorem suzukiCheckpointResetPrefixMixture_eq_errorTransform
    {H : ℝ} (hH : 2 ≤ H) :
    (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
        suzukiCheckpointResetPrefixCurrent t) +
      (32 / H ^ 4) * suzukiCheckpointResetPrefixCurrent H =
        suzukiCheckpointResetErrorTransform H := by
  have h1H : (1 : ℝ) ≤ H := one_le_two.trans hH
  have hH0 : 0 < H := zero_lt_one.trans_le h1H
  let density : ℝ → ℝ := ccmThirdGradeCesaroRectangularMixDensity H
  let s := Finset.Ico 2 (suzukiCheckpointEventIndex H)
  have hdensityCont : ContinuousOn density (Set.Icc 1 H) := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    unfold density ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH0.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hdensityInt : IntervalIntegrable density volume 1 H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1H]
    exact hdensityCont
  have htermInt : ∀ j ∈ s, IntervalIntegrable
      (fun t : ℝ => suzukiCheckpointEventCurvatureJump j *
        (density t *
          (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then (1 : ℝ) else 0)))
      volume 1 H := by
    intro j _hj
    let h := Real.log ((j + 1 : ℕ) : ℝ)
    let f : ℝ → ℝ := fun t => density t * (if h ≤ t then (1 : ℝ) else 0)
    have hfInt : IntervalIntegrable f volume 1 H := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le h1H]
      have hdensOn : IntegrableOn density (Set.Icc 1 H) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le h1H).1 hdensityInt
      have hind := hdensOn.indicator (t := Set.Ici h) measurableSet_Ici
      apply hind.congr_fun
      · intro t ht
        dsimp only [f]
        rw [Set.indicator_apply]
        by_cases hht : h ≤ t
        · simp [hht]
        · simp [hht]
      · exact measurableSet_Icc
    simpa only [f, h] using hfInt.const_mul (suzukiCheckpointEventCurvatureJump j)
  have hbulk :
      (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
          suzukiCheckpointResetPrefixCurrent t) =
        ∑ j ∈ s, suzukiCheckpointEventCurvatureJump j *
          (∫ t in (1 : ℝ)..H, ccmThirdGradeCesaroRectangularMixDensity H t *
            (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then (1 : ℝ) else 0)) := by
    calc
      _ = ∫ t in (1 : ℝ)..H,
          ∑ j ∈ s, suzukiCheckpointEventCurvatureJump j *
            (ccmThirdGradeCesaroRectangularMixDensity H t *
              (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then (1 : ℝ) else 0)) := by
                apply intervalIntegral.integral_congr
                intro t ht
                rw [Set.uIcc_of_le h1H] at ht
                change ccmThirdGradeCesaroRectangularMixDensity H t *
                    suzukiCheckpointResetPrefixCurrent t = _
                rw [suzukiCheckpointResetPrefixCurrent_eq_fixed_sum_indicator
                  ht.1 ht.2]
                dsimp only [s]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                by_cases hjt : Real.log ((j + 1 : ℕ) : ℝ) ≤ t
                · rw [if_pos hjt, if_pos hjt]
                  ring
                · rw [if_neg hjt, if_neg hjt]
                  ring
      _ = ∑ j ∈ s, ∫ t in (1 : ℝ)..H,
          suzukiCheckpointEventCurvatureJump j *
            (ccmThirdGradeCesaroRectangularMixDensity H t *
              (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then (1 : ℝ) else 0)) := by
                exact intervalIntegral.integral_finsetSum htermInt
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [intervalIntegral.integral_const_mul]
  have hend := suzukiCheckpointResetPrefixCurrent_eq_fixed_sum_indicator
    (H := H) (t := H) h1H le_rfl
  unfold suzukiCheckpointResetErrorTransform
  rw [hbulk, hend]
  dsimp only [density, s]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjbounds := one_lt_log_event_succ_and_log_event_succ_le hj
  rw [if_pos hjbounds.2]
  have hresponse := ccmThirdGradeCesaroRectangularMix_step_eq_errorKernel
    (b := (1 : ℝ)) (h := Real.log ((j + 1 : ℕ) : ℝ)) (H := H)
    zero_lt_one hjbounds.1.le hjbounds.2
  rw [if_pos hjbounds.2] at hresponse
  linear_combination suzukiCheckpointEventCurvatureJump j * hresponse

/-- Exact finite transform of the canonical CCM--FU affine mixture. No floor-selected integral
remains: the arithmetic channel is one signed triangular sum plus an absolutely summable reset
sum and a fixed affine response. -/
theorem ccmFUSuzukiCheckpointAffineMixture_eq_base_add_triangular_add_reset
    {H : ℝ} (hH : 2 ≤ H) :
    ccmFUSuzukiCheckpointAffineMixture 1 H =
      suzukiCheckpointBaseAffineMixture H +
        suzukiCheckpointTriangularCurvatureTransform H +
          suzukiCheckpointResetErrorTransform H := by
  have h1H : (1 : ℝ) ≤ H := one_le_two.trans hH
  have hH0 : 0 < H := zero_lt_one.trans_le h1H
  have hlog2one : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  let density : ℝ → ℝ := ccmThirdGradeCesaroRectangularMixDensity H
  let s := Finset.Ico 2 (suzukiCheckpointEventIndex H)
  have hdensityCont : ContinuousOn density (Set.Icc 1 H) := by
    intro t ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
    unfold density ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH0.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hdensityInt : IntervalIntegrable density volume 1 H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1H]
    exact hdensityCont
  have hbaseInt : IntervalIntegrable
      (fun t => density t * suzukiCheckpointBaseAffineCurrent t) volume 1 H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1H]
    have hbaseCont : Continuous suzukiCheckpointBaseAffineCurrent := by
      unfold suzukiCheckpointBaseAffineCurrent
      fun_prop
    exact hdensityCont.mul hbaseCont.continuousOn
  have hhingeTermInt : ∀ j ∈ s, IntervalIntegrable
      (fun t : ℝ => density t *
        (suzukiCheckpointSignedCurvatureCell j *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)))) volume 1 H := by
    intro j _hj
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1H]
    exact hdensityCont.mul
      (continuous_const.mul
        (continuous_const.max (continuous_id.sub continuous_const))).continuousOn
  have hhingeSumInt : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ s, density t *
        (suzukiCheckpointSignedCurvatureCell j *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)))) volume 1 H :=
    by
      have hraw := IntervalIntegrable.sum s hhingeTermInt
      apply hraw.congr
      intro t _ht
      simp only [Finset.sum_apply]
  have hhingeInt : IntervalIntegrable
      (fun t => density t * suzukiCheckpointSignedCurvatureHingeCurrent t)
      volume 1 H := by
    apply hhingeSumInt.congr
    intro t ht
    rw [Set.uIoc_of_le h1H] at ht
    change (∑ j ∈ s, density t *
        (suzukiCheckpointSignedCurvatureCell j *
          max 0 (t - Real.log ((j + 1 : ℕ) : ℝ)))) =
      density t * suzukiCheckpointSignedCurvatureHingeCurrent t
    rw [suzukiCheckpointSignedCurvatureHingeCurrent_eq_fixed_sum_max ht.1.le ht.2]
    dsimp only [s]
    rw [Finset.mul_sum]
  have hresetTermInt : ∀ j ∈ s, IntervalIntegrable
      (fun t : ℝ => density t *
        (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then
          suzukiCheckpointEventCurvatureJump j else 0)) volume 1 H := by
    intro j _hj
    let h := Real.log ((j + 1 : ℕ) : ℝ)
    let g : ℝ → ℝ := fun t => density t * suzukiCheckpointEventCurvatureJump j
    let f : ℝ → ℝ := fun t => density t *
      (if h ≤ t then suzukiCheckpointEventCurvatureJump j else 0)
    have hgInt : IntervalIntegrable g volume 1 H := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le h1H]
      exact hdensityCont.mul continuousOn_const
    have hfInt : IntervalIntegrable f volume 1 H := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le h1H]
      have hgOn : IntegrableOn g (Set.Icc 1 H) :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le h1H).1 hgInt
      have hind := hgOn.indicator (t := Set.Ici h) measurableSet_Ici
      apply hind.congr_fun
      · intro t ht
        dsimp only [f]
        rw [Set.indicator_apply]
        by_cases hht : h ≤ t
        · simp [g, hht]
        · simp [g, hht]
      · exact measurableSet_Icc
    simpa only [f, h] using hfInt
  have hresetSumInt : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ s, density t *
        (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then
          suzukiCheckpointEventCurvatureJump j else 0)) volume 1 H :=
    by
      have hraw := IntervalIntegrable.sum s hresetTermInt
      apply hraw.congr
      intro t _ht
      simp only [Finset.sum_apply]
  have hresetInt : IntervalIntegrable
      (fun t => density t * suzukiCheckpointResetPrefixCurrent t)
      volume 1 H := by
    apply hresetSumInt.congr
    intro t ht
    rw [Set.uIoc_of_le h1H] at ht
    change (∑ j ∈ s, density t *
        (if Real.log ((j + 1 : ℕ) : ℝ) ≤ t then
          suzukiCheckpointEventCurvatureJump j else 0)) =
      density t * suzukiCheckpointResetPrefixCurrent t
    rw [suzukiCheckpointResetPrefixCurrent_eq_fixed_sum_indicator ht.1.le ht.2]
    dsimp only [s]
    rw [Finset.mul_sum]
  have hbulk :
      (∫ t in (1 : ℝ)..H, density t * suzukiCheckpointGlobalAffineCurrent t) =
        (∫ t in (1 : ℝ)..H, density t * suzukiCheckpointBaseAffineCurrent t) +
          (∫ t in (1 : ℝ)..H,
            density t * suzukiCheckpointSignedCurvatureHingeCurrent t) +
            (∫ t in (1 : ℝ)..H,
              density t * suzukiCheckpointResetPrefixCurrent t) := by
    calc
      _ = ∫ t in (1 : ℝ)..H,
          (density t * suzukiCheckpointBaseAffineCurrent t +
            density t * suzukiCheckpointSignedCurvatureHingeCurrent t) +
              density t * suzukiCheckpointResetPrefixCurrent t := by
                apply intervalIntegral.integral_congr
                intro t ht
                rw [Set.uIcc_of_le h1H] at ht
                change density t * suzukiCheckpointGlobalAffineCurrent t =
                  (density t * suzukiCheckpointBaseAffineCurrent t +
                    density t * suzukiCheckpointSignedCurvatureHingeCurrent t) +
                      density t * suzukiCheckpointResetPrefixCurrent t
                rw [suzukiCheckpointGlobalAffineCurrent_eq_base_add_hinge_add_reset
                  (hlog2one.trans ht.1)]
                ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hbaseInt.add hhingeInt) hresetInt,
          intervalIntegral.integral_add hbaseInt hhingeInt]
  have hend := suzukiCheckpointGlobalAffineCurrent_eq_base_add_hinge_add_reset
    (t := H) (hlog2one.trans h1H)
  have hhingeResponse :=
    suzukiCheckpointSignedCurvatureHingeMixture_eq_triangularTransform hH
  have hresetResponse := suzukiCheckpointResetPrefixMixture_eq_errorTransform hH
  unfold ccmFUSuzukiCheckpointAffineMixture suzukiCheckpointBaseAffineMixture
  dsimp only [density] at hbulk
  rw [hbulk, hend]
  linear_combination hhingeResponse + hresetResponse

/-- The fixed affine response is uniformly bounded; it carries no RH information. -/
theorem exists_nonnegative_uniform_bound_suzukiCheckpointBaseAffineMixture :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointBaseAffineMixture H| ≤ C := by
  let C : ℝ :=
    |suzukiCheckpointBaseAffineCurrent 1| * 96 +
      |suzukiCheckpointAffineSlope 2| * 32
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    positivity
  · intro H hH
    have h1H : (1 : ℝ) ≤ H := one_le_two.trans hH
    have hH0 : 0 < H := zero_lt_one.trans_le h1H
    have hk := ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds
      zero_lt_one h1H (show (1 : ℝ) ∈ Set.Icc 1 H from ⟨le_rfl, h1H⟩)
    have hk0 : 0 ≤ ccmGuinandWeilThirdGradeCesaroErrorKernel H 1 := by
      exact (ccmGuinandWeilThirdGradeCesaroErrorKernel_pos
        zero_lt_one h1H (show (1 : ℝ) ∈ Set.Icc 1 H from ⟨le_rfl, h1H⟩)).le
    have hkle : ccmGuinandWeilThirdGradeCesaroErrorKernel H 1 ≤ 96 := by
      simpa using hk.2
    let m : ℝ := 32 - 32 / H
    have hm0 : 0 ≤ m := by
      dsimp only [m]
      have hdiv : 32 / H ≤ (32 : ℝ) := by
        apply (div_le_iff₀ hH0).2
        nlinarith
      linarith
    have hmle : m ≤ 32 := by
      dsimp only [m]
      have hdiv0 : 0 ≤ 32 / H := by positivity
      linarith
    rw [suzukiCheckpointBaseAffineMixture_eq h1H]
    change |suzukiCheckpointBaseAffineCurrent 1 *
        ccmGuinandWeilThirdGradeCesaroErrorKernel H 1 +
      suzukiCheckpointAffineSlope 2 * m| ≤ C
    calc
      _ ≤ |suzukiCheckpointBaseAffineCurrent 1 *
            ccmGuinandWeilThirdGradeCesaroErrorKernel H 1| +
          |suzukiCheckpointAffineSlope 2 * m| := abs_add_le _ _
      _ = |suzukiCheckpointBaseAffineCurrent 1| *
            ccmGuinandWeilThirdGradeCesaroErrorKernel H 1 +
          |suzukiCheckpointAffineSlope 2| * m := by
            rw [abs_mul, abs_mul, abs_of_nonneg hk0, abs_of_nonneg hm0]
      _ ≤ |suzukiCheckpointBaseAffineCurrent 1| * 96 +
          |suzukiCheckpointAffineSlope 2| * 32 :=
            add_le_add
              (mul_le_mul_of_nonneg_left hkle (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hmle (abs_nonneg _))
      _ = C := rfl

/-- The reset error transform has a uniform budget because reset packets have finite total
variation and every active error-kernel weight is uniformly bounded. -/
theorem exists_nonnegative_uniform_bound_suzukiCheckpointResetErrorTransform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointResetErrorTransform H| ≤ C := by
  obtain ⟨R, hR0, hR⟩ :=
    exists_uniform_bound_suzukiCheckpointEventCurvatureJump_prefix
  refine ⟨96 * R, mul_nonneg (by norm_num) hR0, ?_⟩
  intro H hH
  let s := Finset.Ico 2 (suzukiCheckpointEventIndex H)
  have hjump0 : ∀ j ∈ s, 0 ≤ suzukiCheckpointEventCurvatureJump j := by
    intro j hj
    exact (suzukiCheckpointEventCurvatureJump_mem_unitInterval
      (Finset.mem_Ico.mp hj).1).1
  have hkernel : ∀ j ∈ s,
      0 ≤ ccmGuinandWeilThirdGradeCesaroErrorKernel H
          (Real.log ((j + 1 : ℕ) : ℝ)) ∧
        ccmGuinandWeilThirdGradeCesaroErrorKernel H
          (Real.log ((j + 1 : ℕ) : ℝ)) ≤ 96 := by
    intro j hj
    have hjbounds := one_lt_log_event_succ_and_log_event_succ_le hj
    let h := Real.log ((j + 1 : ℕ) : ℝ)
    have hkpos : 0 < ccmGuinandWeilThirdGradeCesaroErrorKernel H h :=
      ccmGuinandWeilThirdGradeCesaroErrorKernel_pos (zero_lt_one.trans hjbounds.1) hjbounds.2
        (show h ∈ Set.Icc h H from ⟨le_rfl, hjbounds.2⟩)
    have hk := ccmGuinandWeilThirdGradeCesaroErrorKernel_bounds
      (zero_lt_one.trans hjbounds.1) hjbounds.2
        (show h ∈ Set.Icc h H from ⟨le_rfl, hjbounds.2⟩)
    have hhpow : 1 ≤ h ^ 4 := by
      have hh1 : 1 ≤ h := hjbounds.1.le
      nlinarith [sq_nonneg (h ^ 2 - 1)]
    have hhpow0 : 0 < h ^ 4 := by positivity
    have hfrac : 96 / h ^ 4 ≤ (96 : ℝ) := by
      apply (div_le_iff₀ hhpow0).2
      nlinarith
    exact ⟨hkpos.le, hk.2.trans hfrac⟩
  have hsum0 : 0 ≤ ∑ j ∈ s,
      suzukiCheckpointEventCurvatureJump j *
        ccmGuinandWeilThirdGradeCesaroErrorKernel H
          (Real.log ((j + 1 : ℕ) : ℝ)) := by
    exact Finset.sum_nonneg fun j hj => mul_nonneg (hjump0 j hj) (hkernel j hj).1
  have hprefix0 : 0 ≤ ∑ j ∈ s, suzukiCheckpointEventCurvatureJump j :=
    Finset.sum_nonneg fun j hj => hjump0 j hj
  have hprefixLe : (∑ j ∈ s, suzukiCheckpointEventCurvatureJump j) ≤ R := by
    have hbound := hR (suzukiCheckpointEventIndex H)
    dsimp only [s]
    rw [abs_of_nonneg hprefix0] at hbound
    exact hbound
  unfold suzukiCheckpointResetErrorTransform
  rw [abs_of_nonneg hsum0]
  calc
    (∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        suzukiCheckpointEventCurvatureJump j *
          ccmGuinandWeilThirdGradeCesaroErrorKernel H
            (Real.log ((j + 1 : ℕ) : ℝ))) ≤
      ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        suzukiCheckpointEventCurvatureJump j * 96 := by
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul_of_nonneg_left (hkernel j hj).2 (hjump0 j hj)
    _ = 96 * ∑ j ∈ Finset.Ico 2 (suzukiCheckpointEventIndex H),
        suzukiCheckpointEventCurvatureJump j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ ≤ 96 * R := mul_le_mul_of_nonneg_left hprefixLe (by norm_num)

/-- Combined affine and reset channels have a uniform budget. -/
theorem exists_nonnegative_uniform_bound_suzukiCheckpointAffineNuisance :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
      |suzukiCheckpointBaseAffineMixture H +
        suzukiCheckpointResetErrorTransform H| ≤ C := by
  obtain ⟨A, hA0, hA⟩ :=
    exists_nonnegative_uniform_bound_suzukiCheckpointBaseAffineMixture
  obtain ⟨R, hR0, hR⟩ :=
    exists_nonnegative_uniform_bound_suzukiCheckpointResetErrorTransform
  refine ⟨A + R, add_nonneg hA0 hR0, ?_⟩
  intro H hH
  exact (abs_add_le _ _).trans (add_le_add (hA H hH) (hR H hH))

/-- Remaining CCM--FU burden after the exact affine-floor transform: uniform cancellation of the
single signed triangular curvature sum. -/
def CCMFUSuzukiTriangularCurvatureTransformBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 2 ≤ H →
    |suzukiCheckpointTriangularCurvatureTransform H| ≤ C

/-- Canonical affine-tail boundedness is equivalent to boundedness of the signed triangular
curvature transform. Both discarded channels are unconditionally and uniformly bounded. -/
theorem ccmFUSuzukiCanonicalCheckpointAffineTailBound_iff_triangularCurvatureTransformBound :
    CCMFUSuzukiCanonicalCheckpointAffineTailBound ↔
      CCMFUSuzukiTriangularCurvatureTransformBound := by
  obtain ⟨D, hD0, hD⟩ :=
    exists_nonnegative_uniform_bound_suzukiCheckpointAffineNuisance
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + D, add_nonneg hC0 hD0, ?_⟩
    intro H hH
    have hdecomp :=
      ccmFUSuzukiCheckpointAffineMixture_eq_base_add_triangular_add_reset hH
    have hrearrange : suzukiCheckpointTriangularCurvatureTransform H =
        ccmFUSuzukiCheckpointAffineMixture 1 H -
          (suzukiCheckpointBaseAffineMixture H +
            suzukiCheckpointResetErrorTransform H) := by
      linarith
    rw [hrearrange]
    exact (abs_sub _ _).trans (add_le_add (hC H hH) (hD H hH))
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + D, add_nonneg hC0 hD0, ?_⟩
    intro H hH
    have hdecomp :=
      ccmFUSuzukiCheckpointAffineMixture_eq_base_add_triangular_add_reset hH
    have hrearrange : ccmFUSuzukiCheckpointAffineMixture 1 H =
        suzukiCheckpointTriangularCurvatureTransform H +
          (suzukiCheckpointBaseAffineMixture H +
            suzukiCheckpointResetErrorTransform H) := by
      linarith
    rw [hrearrange]
    exact (abs_add_le _ _).trans (add_le_add (hC H hH) (hD H hH))

/-- RH chain after the reduction: it now suffices to bound one finite signed triangular transform
of the exact Suzuki curvature cells. -/
theorem riemannHypothesis_of_suzukiCheckpointTriangularCurvatureTransformBound
    (hbound : CCMFUSuzukiTriangularCurvatureTransformBound) :
    RiemannHypothesis := by
  have htail : CCMFUSuzukiCanonicalCheckpointAffineTailBound :=
    ccmFUSuzukiCanonicalCheckpointAffineTailBound_iff_triangularCurvatureTransformBound.mpr
      hbound
  exact
    ccmFUSuzukiCanonicalCheckpointAffineTailBound_iff_and_riemannHypothesis.mp htail |>.2

end RHTower
