import GaloisForLFunctions.RHTower.CCMFUCauchyVolterraReconstruction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Literal CCM-FU coefficient as a positive Cauchy--Volterra mixture

This is the moving third-grade FU profile in its square-root coordinate.  Its simple terminal
zero forces a nonzero endpoint jet; the interior curvature is positive on the complete active
clock range.  No prime, polar, or Gamma term is estimated here.
-/

open MeasureTheory

namespace RHTower

noncomputable section

/-- Literal third-grade FU coefficient in square-root coordinate. -/
def cauchyVolterraFUProfile (H y : ℝ) : ℝ :=
  4 / (y * Real.log y ^ 3) * (1 - 2 * Real.log y / H)

def cauchyVolterraFUProfileDeriv (H y : ℝ) : ℝ :=
  4 / y ^ 2 *
    (-3 / Real.log y ^ 4 + (4 / H - 1) / Real.log y ^ 3 + 2 / (H * Real.log y ^ 2))

def cauchyVolterraFUProfileDerivTwo (H y : ℝ) : ℝ :=
  4 / y ^ 3 *
    (12 / Real.log y ^ 5 + (9 - 12 / H) / Real.log y ^ 4 +
      (2 - 12 / H) / Real.log y ^ 3 - 4 / (H * Real.log y ^ 2))

def cauchyVolterraFUDensityNumerator (H t : ℝ) : ℝ :=
  H * (12 + 9 * t + 2 * t ^ 2) - 12 * t - 12 * t ^ 2 - 4 * t ^ 3

/-- Square-root-coordinate curvature of the literal FU profile. -/
def cauchyVolterraFUCurvature (H y : ℝ) : ℝ :=
  4 * cauchyVolterraFUDensityNumerator H (Real.log y) /
    (y * H * Real.log y ^ 5)

theorem hasDerivAt_cauchyVolterraFUProfile
    {H y : ℝ} (hH : H ≠ 0) (hy : y ≠ 0) (hlog : Real.log y ≠ 0) :
    HasDerivAt (cauchyVolterraFUProfile H) (cauchyVolterraFUProfileDeriv H y) y := by
  have hlog' := Real.hasDerivAt_log hy
  have hlog3 := hlog'.pow 3
  have hden := (hasDerivAt_id (x := y)).mul hlog3
  have hden0 : y * Real.log y ^ 3 ≠ 0 := mul_ne_zero hy (pow_ne_zero _ hlog)
  have hquot := (hasDerivAt_const (x := y) (c := (4 : ℝ))).div hden hden0
  have hfactor := (hasDerivAt_const (x := y) (c := (1 : ℝ))).sub
    (((hasDerivAt_const (x := y) (c := (2 : ℝ))).mul hlog').div_const H)
  apply (hquot.mul hfactor).congr_deriv
  simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  unfold cauchyVolterraFUProfileDeriv
  field_simp [hH, hy, hlog]
  ring

theorem hasDerivAt_cauchyVolterraFUProfileDeriv
    {H y : ℝ} (hH : H ≠ 0) (hy : y ≠ 0) (hlog : Real.log y ≠ 0) :
    HasDerivAt (cauchyVolterraFUProfileDeriv H) (cauchyVolterraFUProfileDerivTwo H y) y := by
  have hlog' := Real.hasDerivAt_log hy
  have hlog2 := hlog'.pow 2
  have hlog3 := hlog'.pow 3
  have hlog4 := hlog'.pow 4
  have hterm1 := (hasDerivAt_const (x := y) (c := (-3 : ℝ))).div hlog4
    (pow_ne_zero _ hlog)
  have hterm2 := (hasDerivAt_const (x := y) (c := 4 / H - 1)).div hlog3
    (pow_ne_zero _ hlog)
  have hden3 := (hasDerivAt_const (x := y) (c := H)).mul hlog2
  have hden3ne : H * Real.log y ^ 2 ≠ 0 := mul_ne_zero hH (pow_ne_zero _ hlog)
  have hterm3 := (hasDerivAt_const (x := y) (c := (2 : ℝ))).div hden3 hden3ne
  have hbracket := (hterm1.add hterm2).add hterm3
  have hy2 := (hasDerivAt_id (x := y)).pow 2
  have houter := (hasDerivAt_const (x := y) (c := (4 : ℝ))).div hy2
    (pow_ne_zero _ hy)
  unfold cauchyVolterraFUProfileDeriv
  apply (houter.mul hbracket).congr_deriv
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  unfold cauchyVolterraFUProfileDerivTwo
  field_simp [hH, hy, hlog]
  ring

theorem cauchyVolterraFUProfile_terminal
    {H : ℝ} (hH : H ≠ 0) :
    cauchyVolterraFUProfile H (Real.exp (H / 2)) = 0 := by
  unfold cauchyVolterraFUProfile
  rw [Real.log_exp]
  have hzero : 1 - 2 * (H / 2) / H = 0 := by
    field_simp [hH]
    ring
  rw [hzero]
  ring

/-- The forced first-order terminal charge of the literal FU profile. -/
theorem cauchyVolterraFUProfile_endpointJet
    {H : ℝ} (hH : H ≠ 0) :
    -Real.exp (H / 2) * cauchyVolterraFUProfileDeriv H (Real.exp (H / 2)) =
      64 / (Real.exp (H / 2) * H ^ 4) := by
  unfold cauchyVolterraFUProfileDeriv
  rw [Real.log_exp]
  field_simp [hH, (Real.exp_pos (H / 2)).ne']
  ring

theorem cauchyVolterraFUCurvature_eq_profileDerivTwo
    {H y : ℝ} (hH : H ≠ 0) (hy : y ≠ 0) (hlog : Real.log y ≠ 0) :
    cauchyVolterraFUCurvature H y =
      y ^ 2 * cauchyVolterraFUProfileDerivTwo H y := by
  unfold cauchyVolterraFUCurvature cauchyVolterraFUDensityNumerator
    cauchyVolterraFUProfileDerivTwo
  field_simp [hH, hy, hlog]
  ring

theorem cauchyVolterraFUDensityNumerator_pos
    {H t : ℝ} (ht : 0 < t) (htH : 2 * t ≤ H) :
    0 < cauchyVolterraFUDensityNumerator H t := by
  have hfactor : 0 < 12 + 9 * t + 2 * t ^ 2 := by positivity
  have hscale :
      2 * t * (12 + 9 * t + 2 * t ^ 2) ≤
        H * (12 + 9 * t + 2 * t ^ 2) :=
    mul_le_mul_of_nonneg_right htH hfactor.le
  unfold cauchyVolterraFUDensityNumerator
  nlinarith

theorem cauchyVolterraFUCurvature_pos
    {H y : ℝ} (hy : 1 < y) (hlogH : 2 * Real.log y ≤ H) :
    0 < cauchyVolterraFUCurvature H y := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hH : 0 < H := lt_of_lt_of_le (by linarith) hlogH
  unfold cauchyVolterraFUCurvature
  exact div_pos
    (mul_pos (by norm_num) (cauchyVolterraFUDensityNumerator_pos hlog hlogH))
    (mul_pos (mul_pos hy0 hH) (pow_pos hlog 5))

/-- The literal FU curvature times a Cauchy cell is integrable on every active compact clock
interval.  This is the analytic certificate needed for finite signed transport; it makes no
estimate of the arithmetic cell coefficient. -/
theorem cauchyVolterraFUCurvature_mul_kernel_intervalIntegrable
    {H x Y : ℝ} (hH : 0 < H) (hx : 1 < x) (hxY : x ≤ Y) :
    IntervalIntegrable
      (fun y : ℝ => cauchyVolterraFUCurvature H y * cauchyVolterraKernel x y)
      volume x Y := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hcont' : ContinuousOn (cauchyVolterraFUProfileDerivTwo H) (Set.Icc x Y) := by
    intro y hy
    have hy1 : 1 < y := hx.trans_le hy.1
    have hy0 : y ≠ 0 := ne_of_gt (by linarith)
    have hlog0 : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy1)
    have hlogcont : ContinuousAt Real.log y := (Real.hasDerivAt_log hy0).continuousAt
    have hpre : ContinuousAt (fun z : ℝ => 4 / z ^ 3) y :=
      continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero _ hy0)
    have hterm1 : ContinuousAt (fun z : ℝ => 12 / Real.log z ^ 5) y :=
      continuousAt_const.div (hlogcont.pow 5) (pow_ne_zero _ hlog0)
    have hterm2 : ContinuousAt (fun z : ℝ => (9 - 12 / H) / Real.log z ^ 4) y :=
      continuousAt_const.div (hlogcont.pow 4) (pow_ne_zero _ hlog0)
    have hterm3 : ContinuousAt (fun z : ℝ => (2 - 12 / H) / Real.log z ^ 3) y :=
      continuousAt_const.div (hlogcont.pow 3) (pow_ne_zero _ hlog0)
    have hden : ContinuousAt (fun z : ℝ => H * Real.log z ^ 2) y :=
      continuousAt_const.mul (hlogcont.pow 2)
    have hterm4 : ContinuousAt (fun z : ℝ => 4 / (H * Real.log z ^ 2)) y :=
      continuousAt_const.div hden (mul_ne_zero hHne (pow_ne_zero _ hlog0))
    exact (hpre.mul (((hterm1.add hterm2).add hterm3).sub hterm4)).continuousWithinAt
  have hcurv : ContinuousOn (fun y : ℝ => cauchyVolterraFUCurvature H y) (Set.Icc x Y) := by
    intro y hy
    apply ((continuousAt_id.pow 2).continuousWithinAt.mul (hcont' y hy)).congr_of_mem _ hy
    intro z hz
    have hz1 : 1 < z := hx.trans_le hz.1
    exact cauchyVolterraFUCurvature_eq_profileDerivTwo hHne
      (ne_of_gt (by linarith)) (ne_of_gt (Real.log_pos hz1))
  have hkernel : ContinuousOn (fun y : ℝ => cauchyVolterraKernel x y) (Set.Icc x Y) := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt (by linarith [hx, hy.1])
    unfold cauchyVolterraKernel
    exact ((continuousAt_const.div continuousAt_id hy0).sub
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ hy0))).continuousWithinAt
  exact (hcurv.mul hkernel).intervalIntegrable_of_Icc hxY

/-- Exact positive Cauchy--Volterra mixture on every active square-root clock interval.  The
endpoint term is retained because the literal profile vanishes only to first order at the wall. -/
theorem cauchyVolterraFUProfile_reconstruction
    {H x : ℝ} (hH : 0 < H) (hx : 1 < x) (hxY : x ≤ Real.exp (H / 2)) :
    cauchyVolterraFUProfile H x =
      (-Real.exp (H / 2) * cauchyVolterraFUProfileDeriv H (Real.exp (H / 2))) *
          (1 - x / Real.exp (H / 2)) +
        ∫ y in x..Real.exp (H / 2),
          cauchyVolterraFUCurvature H y * cauchyVolterraKernel x y := by
  have hHne : H ≠ 0 := ne_of_gt hH
  have hYpos : 0 < Real.exp (H / 2) := Real.exp_pos _
  have hderiv : ∀ y ∈ Set.Icc x (Real.exp (H / 2)),
      HasDerivAt (cauchyVolterraFUProfile H) (cauchyVolterraFUProfileDeriv H y) y := by
    intro y hy
    have hy1 : 1 < y := hx.trans_le hy.1
    exact hasDerivAt_cauchyVolterraFUProfile hHne (ne_of_gt (by linarith))
      (ne_of_gt (Real.log_pos hy1))
  have hderiv' : ∀ y ∈ Set.Icc x (Real.exp (H / 2)),
      HasDerivAt (cauchyVolterraFUProfileDeriv H)
        (cauchyVolterraFUProfileDerivTwo H y) y := by
    intro y hy
    have hy1 : 1 < y := hx.trans_le hy.1
    exact hasDerivAt_cauchyVolterraFUProfileDeriv hHne (ne_of_gt (by linarith))
      (ne_of_gt (Real.log_pos hy1))
  have hcont : ContinuousOn (cauchyVolterraFUProfileDeriv H)
      (Set.Icc x (Real.exp (H / 2))) := by
    intro y hy
    exact (hderiv' y hy).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (cauchyVolterraFUProfileDerivTwo H)
      (Set.Icc x (Real.exp (H / 2))) := by
    intro y hy
    have hy1 : 1 < y := hx.trans_le hy.1
    have hy0 : y ≠ 0 := ne_of_gt (by linarith)
    have hlog0 : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy1)
    have hlogcont : ContinuousAt Real.log y := (Real.hasDerivAt_log hy0).continuousAt
    have hpre : ContinuousAt (fun z : ℝ => 4 / z ^ 3) y :=
      continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero _ hy0)
    have hterm1 : ContinuousAt (fun z : ℝ => 12 / Real.log z ^ 5) y :=
      continuousAt_const.div (hlogcont.pow 5) (pow_ne_zero _ hlog0)
    have hterm2 : ContinuousAt (fun z : ℝ => (9 - 12 / H) / Real.log z ^ 4) y :=
      continuousAt_const.div (hlogcont.pow 4) (pow_ne_zero _ hlog0)
    have hterm3 : ContinuousAt (fun z : ℝ => (2 - 12 / H) / Real.log z ^ 3) y :=
      continuousAt_const.div (hlogcont.pow 3) (pow_ne_zero _ hlog0)
    have hden : ContinuousAt (fun z : ℝ => H * Real.log z ^ 2) y :=
      continuousAt_const.mul (hlogcont.pow 2)
    have hterm4 : ContinuousAt (fun z : ℝ => 4 / (H * Real.log z ^ 2)) y :=
      continuousAt_const.div hden (mul_ne_zero hHne (pow_ne_zero _ hlog0))
    exact (hpre.mul (((hterm1.add hterm2).add hterm3).sub hterm4)).continuousWithinAt
  have hint : IntervalIntegrable (cauchyVolterraFUProfileDeriv H) volume x
      (Real.exp (H / 2)) := hcont.intervalIntegrable_of_Icc hxY
  have hint' : IntervalIntegrable (cauchyVolterraFUProfileDerivTwo H) volume x
      (Real.exp (H / 2)) := hcont'.intervalIntegrable_of_Icc hxY
  have hrec := cauchyVolterra_reconstruction_cauchy
    (f := cauchyVolterraFUProfile H) (f' := cauchyVolterraFUProfileDeriv H)
    (f'' := cauchyVolterraFUProfileDerivTwo H)
    (show 0 < x by linarith) hxY hYpos.ne'
    (cauchyVolterraFUProfile_terminal hHne) hderiv hderiv' hint hint'
  rw [hrec]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hxY] at hy
  have hy1 : 1 < y := hx.trans_le hy.1
  change y ^ 2 * cauchyVolterraFUProfileDerivTwo H y * (1 / y - x / y ^ 2) =
    cauchyVolterraFUCurvature H y * cauchyVolterraKernel x y
  rw [← cauchyVolterraFUCurvature_eq_profileDerivTwo hHne
    (ne_of_gt (by linarith)) (ne_of_gt (Real.log_pos hy1))]
  rfl

end

end RHTower
