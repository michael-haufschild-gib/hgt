import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCutoffPowerHeight

/-! Exact boundary and eigenvalue-mismatch value of the full differential cutoff moment. -/
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

def cutoffPowerMoment (delta k : ℂ) : ℂ :=
  ∫ y in (1:ℝ)..4, (y:ℂ)^(delta-2)*cutoffCommutator k ![0,y]

def cutoffBulkMoment (delta k : ℂ) : ℂ :=
  ∫ y in (1:ℝ)..4, (y:ℂ)^(delta-2)*powerCutoffHeight k y

def cutoffPowerFlux (delta k : ℂ) (y : ℝ) : ℂ :=
  (y:ℂ)^delta*deriv (powerCutoffHeight k) y-
    delta*(y:ℂ)^(delta-1)*powerCutoffHeight k y

private theorem power_step (delta : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^delta = (y:ℂ)^(delta-2)*(y:ℂ)^(2 : ℕ) := by
  have he : (y:ℂ)^(2:ℂ) = (y:ℂ)^(2 : ℕ) := by norm_cast
  rw [← he,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  congr 1
  ring

/-- The actual cutoff Wronskian retains the full eigenvalue-mismatch source. -/
theorem cutoffPowerFlux_hasDerivAt (delta k : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cutoffPowerFlux delta k)
      ((y:ℂ)^(delta-2)*cutoffCommutator k ![0,y]+
        (k*(k-1)-delta*(delta-1))*((y:ℂ)^(delta-2)*powerCutoffHeight k y)) y := by
  have h0 := ((powerCutoffHeight_smooth k).differentiable (by simp) y).hasDerivAt
  have h1 := (((contDiff_infty_iff_deriv.mp (powerCutoffHeight_smooth k)).2).differentiable
    (by simp) y).hasDerivAt
  have hp := GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := delta) hy
  have hp1 := GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := delta-1) hy
  have h := (hp.mul h1).sub ((hp1.const_mul delta).mul h0)
  change HasDerivAt (cutoffPowerFlux delta k) _ y at h
  convert h using 1
  rw [cutoffCommutator_height]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [show delta-1-1=delta-2 by ring,power_step delta hy]
  ring

/-- Both boundary values are forced by the original cutoff's literal germs. -/
theorem cutoffPowerFlux_boundaries (delta k : ℂ) :
    cutoffPowerFlux delta k 1 = 0 ∧
      cutoffPowerFlux delta k 4 = (k-delta)*(4:ℂ)^(delta+k-1) := by
  have hl0 := (powerCutoffHeight_low_germ k).eq_of_nhds
  have hl1 := (powerCutoffHeight_low_germ k).deriv_eq
  simp only [deriv_const] at hl1
  have hh0 := (powerCutoffHeight_high_germ k).eq_of_nhds
  have hh1 : deriv (powerCutoffHeight k) 4 = k*(4:ℂ)^(k-1) := by
    rw [(powerCutoffHeight_high_germ k).deriv_eq]
    exact (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := k)
      (by norm_num : (0:ℝ)<4)).deriv
  constructor
  · rw [cutoffPowerFlux,hl0,hl1]
    simp
  · rw [cutoffPowerFlux,hh0,hh1]
    norm_num only [Complex.ofReal_ofNat]
    have ha : (4:ℂ)^delta*(4:ℂ)^(k-1) = (4:ℂ)^(delta+k-1) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (4:ℂ) ≠ 0)]
      congr 1
      ring
    have hb : (4:ℂ)^(delta-1)*(4:ℂ)^k = (4:ℂ)^(delta+k-1) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (4:ℂ) ≠ 0)]
      congr 1
      ring
    calc
      (4:ℂ)^delta*(k*(4:ℂ)^(k-1))-delta*(4:ℂ)^(delta-1)*(4:ℂ)^k =
        k*((4:ℂ)^delta*(4:ℂ)^(k-1))-delta*((4:ℂ)^(delta-1)*(4:ℂ)^k) := by ring
      _ = (k-delta)*(4:ℂ)^(delta+k-1) := by rw [ha,hb]; ring

theorem cutoffPowerSource_intervalIntegrable (delta k : ℂ) :
    IntervalIntegrable (fun y : ℝ => (y:ℂ)^(delta-2)*cutoffCommutator k ![0,y]) volume 1 4 := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hp : 0 < y := by norm_num only [uIcc_of_le (show (1:ℝ)≤4 by norm_num),mem_Icc] at hy; linarith [hy.1]
  exact ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := delta-2) hp).continuousAt.mul
    (cutoffCommutator_height_continuous k).continuousAt).continuousWithinAt

/-- Exact moment value: the original boundary flux plus the retained mismatch integral. -/
theorem cutoffPowerMoment_eq (delta k : ℂ) :
    cutoffPowerMoment delta k = (k-delta)*(4:ℂ)^(delta+k-1)+
      (delta*(delta-1)-k*(k-1))*cutoffBulkMoment delta k := by
  have hp (y : ℝ) (hy : y ∈ uIcc (1:ℝ) 4) : 0 < y := by
    norm_num only [uIcc_of_le (show (1:ℝ)≤4 by norm_num),mem_Icc] at hy
    linarith [hy.1]
  have hs := cutoffPowerSource_intervalIntegrable delta k
  have hb : IntervalIntegrable (fun y : ℝ => (y:ℂ)^(delta-2)*powerCutoffHeight k y) volume 1 4 := by
    apply ContinuousOn.intervalIntegrable
    intro y hy
    exact ((GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := delta-2) (hp y hy)).continuousAt.mul
      (powerCutoffHeight_smooth k).continuous.continuousAt).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => cutoffPowerFlux_hasDerivAt delta k (hp y hy))
    (hs.add (hb.const_mul (k*(k-1)-delta*(delta-1))))
  rw [intervalIntegral.integral_add hs (hb.const_mul _),intervalIntegral.integral_const_mul,
    (cutoffPowerFlux_boundaries delta k).1,(cutoffPowerFlux_boundaries delta k).2,sub_zero] at h
  change cutoffPowerMoment delta k+(k*(k-1)-delta*(delta-1))*cutoffBulkMoment delta k = _ at h
  calc
    cutoffPowerMoment delta k = (k-delta)*(4:ℂ)^(delta+k-1)-
        (k*(k-1)-delta*(delta-1))*cutoffBulkMoment delta k := eq_sub_of_add_eq h
    _ = _ := by ring

end
end RHTower.D4BMJointSource
