import GaloisForLFunctions.RHTower.RouteETerminalContinuousOddResonance
import GaloisForLFunctions.RHTower.RouteETerminalPrimeStieltjesTransport
import GaloisForLFunctions.RHTower.CCM.CCMSawtoothDilationIncidence

namespace RHTower
open Filter Topology MeasureTheory Set intervalIntegral
noncomputable section

noncomputable def routeETerminalDenominatedEnergy (a L t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..1,
    routeETerminalWeight a v *
      routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v)

theorem routeETerminalDenominatedEnergy_compare
    {a L t : ℝ} (hL : 1 < L) :
    routeETerminalContinuousEnergy a L t / L ≤
        routeETerminalDenominatedEnergy a L t ∧
      routeETerminalDenominatedEnergy a L t ≤
        routeETerminalContinuousEnergy a L t / (L - 1) := by
  have hL0 : 0 < L := lt_trans zero_lt_one hL
  have hLm1 : 0 < L - 1 := sub_pos.mpr hL
  have hcontNum : Continuous (fun v : ℝ =>
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v))) :=
    continuous_routeETerminalContinuousIntegrand a L t
  have hcontDen : ContinuousOn (fun v : ℝ =>
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v)) (Icc 0 1) := by
    intro v hv
    have hden : L - v ≠ 0 := by
      have hv1 := hv.2
      linarith
    exact hcontNum.continuousAt.div
      (continuousAt_const.sub continuousAt_id) hden |>.continuousWithinAt
  have hnumInt : IntervalIntegrable (fun v : ℝ =>
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v))) volume 0 1 :=
    hcontNum.intervalIntegrable 0 1
  have hdenInt : IntervalIntegrable (fun v : ℝ =>
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v)) volume 0 1 :=
    hcontDen.intervalIntegrable_of_Icc zero_le_one
  have hlowerPoint : ∀ v ∈ Icc (0 : ℝ) 1,
      (routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v))) / L ≤
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v) := by
    intro v hv
    have hnum0 : 0 ≤ routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) :=
      mul_nonneg (routeETerminalWeight_pos a v).le
        (routeETerminalPhaseEnergy_nonneg _ _)
    have hv0 := hv.1
    have hv1 := hv.2
    have hden : 0 < L - v := by linarith
    exact div_le_div_of_nonneg_left hnum0 hden (by linarith)
  have hupperPoint : ∀ v ∈ Icc (0 : ℝ) 1,
      routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v) ≤
      (routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v))) / (L - 1) := by
    intro v hv
    have hnum0 : 0 ≤ routeETerminalWeight a v *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) :=
      mul_nonneg (routeETerminalWeight_pos a v).le
        (routeETerminalPhaseEnergy_nonneg _ _)
    have hv0 := hv.1
    have hv1 := hv.2
    have hden : 0 < L - v := by linarith
    exact div_le_div_of_nonneg_left hnum0 hLm1 (by linarith)
  constructor
  · rw [routeETerminalContinuousEnergy,
      routeETerminalDenominatedEnergy, ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_mono_on zero_le_one
      (hnumInt.div_const L) hdenInt hlowerPoint
  · rw [routeETerminalDenominatedEnergy,
      routeETerminalContinuousEnergy, ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_mono_on zero_le_one
      hdenInt (hnumInt.div_const (L - 1)) hupperPoint

theorem routeETerminalPrimeMain_exp_eq_denominated
    (r L t : ℝ) :
    routeETerminalPrimeMain r (Real.exp L) t =
      Real.exp ((1 - r) * L) *
        routeETerminalDenominatedEnergy (1 - r) L t := by
  have hX : 0 < Real.exp L := Real.exp_pos L
  have hscale : 0 < Real.exp L := Real.exp_pos L
  have hle : Real.exp L / Real.exp 1 ≤ Real.exp L :=
    div_le_self hX.le (Real.one_le_exp_iff.mpr (by norm_num))
  rw [routeETerminalPrimeMain, ← intervalIntegral.integral_of_le hle]
  have hlower : Real.exp L / Real.exp 1 = Real.exp L * Real.exp (-1) := by
    rw [Real.exp_neg]
    field_simp
  rw [hlower]
  have hcov := GaloisForLFunctions.RHTower.integral_comp_exp_scale
    hscale (by norm_num : (-1 : ℝ) ≤ 0)
      (fun x : ℝ => x ^ (-r) * routeETerminalPhaseEnergy t x / Real.log x)
  have hcov' :
      (∫ x in (Real.exp L * Real.exp (-1))..Real.exp L,
        x ^ (-r) * routeETerminalPhaseEnergy t x / Real.log x) =
      ∫ s in (-1 : ℝ)..0, (Real.exp L * Real.exp s) *
        ((Real.exp L * Real.exp s) ^ (-r) *
          routeETerminalPhaseEnergy t (Real.exp L * Real.exp s) /
            Real.log (Real.exp L * Real.exp s)) := by
    simpa using hcov
  rw [hcov']
  let G : ℝ → ℝ := fun s => (Real.exp L * Real.exp s) *
    ((Real.exp L * Real.exp s) ^ (-r) *
      routeETerminalPhaseEnergy t (Real.exp L * Real.exp s) /
        Real.log (Real.exp L * Real.exp s))
  have hneg : (∫ s in (-1 : ℝ)..0, G s) =
      ∫ v in (0 : ℝ)..1, G (-v) := by
    symm
    simpa using (intervalIntegral.integral_comp_neg
      (f := G) (a := (0 : ℝ)) (b := 1))
  change (∫ s in (-1 : ℝ)..0, G s) = _
  rw [hneg]
  rw [routeETerminalDenominatedEnergy, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp [G]
  rw [← Real.exp_add]
  rw [show L + -v = L - v by ring]
  rw [Real.log_exp, ← Real.exp_mul, routeETerminalWeight]
  have hexpEq :
      Real.exp (L - v) * Real.exp ((L - v) * -r) =
        Real.exp ((1 - r) * L) * Real.exp (-(1 - r) * v) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (L - v) *
      (Real.exp ((L - v) * -r) *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v)) =
      (Real.exp (L - v) * Real.exp ((L - v) * -r)) *
        routeETerminalPhaseEnergy t (Real.exp (L - v)) / (L - v) by ring]
  rw [hexpEq]
  ring

/-- The logarithmic denominator does not change any finite normalized continuous-energy limit. -/
theorem tendsto_routeETerminalDenominatedEnergy_of_continuousEnergy
    (a Q : ℝ) (t : ℝ → ℝ)
    (henergy : Tendsto (fun L : ℝ =>
      L ^ 2 * routeETerminalContinuousEnergy a L (t L)) atTop (nhds Q)) :
    Tendsto (fun L : ℝ =>
      L ^ 3 * routeETerminalDenominatedEnergy a L (t L)) atTop (nhds Q) := by
  have hshift : Tendsto (fun L : ℝ => L - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) tendsto_id
  have hinv : Tendsto (fun L : ℝ => (L - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have hfactor : Tendsto (fun L : ℝ => L / (L - 1)) atTop (nhds 1) := by
    have hraw : Tendsto (fun L : ℝ => 1 + (L - 1)⁻¹) atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add hinv
    have heq : (fun L : ℝ => 1 + (L - 1)⁻¹) =ᶠ[atTop]
        (fun L : ℝ => L / (L - 1)) := by
      filter_upwards [eventually_ne_atTop (1 : ℝ)] with L hL
      field_simp [sub_ne_zero.mpr hL]
      ring
    simpa using hraw.congr' heq
  have hupperLimit : Tendsto (fun L : ℝ =>
      (L / (L - 1)) *
        (L ^ 2 * routeETerminalContinuousEnergy a L (t L))) atTop (nhds Q) := by
    simpa using hfactor.mul henergy
  have hbounds : ∀ᶠ L : ℝ in atTop,
      L ^ 2 * routeETerminalContinuousEnergy a L (t L) ≤
          L ^ 3 * routeETerminalDenominatedEnergy a L (t L) ∧
        L ^ 3 * routeETerminalDenominatedEnergy a L (t L) ≤
          (L / (L - 1)) *
            (L ^ 2 * routeETerminalContinuousEnergy a L (t L)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    have hcomp := routeETerminalDenominatedEnergy_compare
      (a := a) (t := t L) hL
    have hL0 : 0 < L := lt_trans zero_lt_one hL
    have hcube : 0 ≤ L ^ 3 := (pow_pos hL0 _).le
    constructor
    · have hm := mul_le_mul_of_nonneg_left hcomp.1 hcube
      have heq : L ^ 3 *
          (routeETerminalContinuousEnergy a L (t L) / L) =
          L ^ 2 * routeETerminalContinuousEnergy a L (t L) := by
        field_simp [hL0.ne']
      rwa [heq] at hm
    · have hm := mul_le_mul_of_nonneg_left hcomp.2 hcube
      have hLne : L - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hL)
      have heq : L ^ 3 *
          (routeETerminalContinuousEnergy a L (t L) / (L - 1)) =
          (L / (L - 1)) *
            (L ^ 2 * routeETerminalContinuousEnergy a L (t L)) := by
        field_simp [hLne]
      rwa [heq] at hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' henergy hupperLimit
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- Exact prime-main version of the denominator transfer. -/
theorem tendsto_routeETerminalPrimeMain_exp_normalized_of_continuousEnergy
    (r Q : ℝ) (t : ℝ → ℝ)
    (henergy : Tendsto (fun L : ℝ =>
      L ^ 2 * routeETerminalContinuousEnergy (1 - r) L (t L)) atTop (nhds Q)) :
    Tendsto (fun L : ℝ =>
      L ^ 3 / Real.exp ((1 - r) * L) *
        routeETerminalPrimeMain r (Real.exp L) (t L)) atTop (nhds Q) := by
  have hden := tendsto_routeETerminalDenominatedEnergy_of_continuousEnergy
    (1 - r) Q t henergy
  apply hden.congr'
  filter_upwards with L
  rw [routeETerminalPrimeMain_exp_eq_denominated]
  have hexp : Real.exp ((1 - r) * L) ≠ 0 := Real.exp_ne_zero _
  field_simp

end
end RHTower
