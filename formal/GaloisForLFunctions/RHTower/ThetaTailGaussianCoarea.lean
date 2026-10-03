import GaloisForLFunctions.RHTower.ThetaCoordinateCanonicalGlobal
import GaloisForLFunctions.RHTower.ThetaTailCommonTranslationLoewnerNoGo
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Exact Gaussian coarea for the literal first-moment tail kernel.
The coordinate u=t(t+x+y) removes the linear kernel weight. -/

noncomputable section
open MeasureTheory Set
namespace RHTower.ThetaGaussianCoarea

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "U" => ThetaCoordinate.sourcePotential

def length (x y u : ℝ) : ℝ := Real.sqrt ((x+y)^2+4*u)
def shift (x y u : ℝ) : ℝ := (length x y u-x-y)/2
def coordinate (x y t : ℝ) : ℝ := t*(t+x+y)
def potential (x y u : ℝ) : ℝ :=
  U (x+shift x y u)+U (y+shift x y u)-U x-U y
def density (x y u : ℝ) : ℝ := Real.exp (-potential x y u)

theorem length_pos (x y : ℝ) {u : ℝ} (hu : 0 < u) : 0 < length x y u := by
  unfold length
  exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg (x+y)])

theorem length_sq (x y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    length x y u^2=(x+y)^2+4*u := by
  exact Real.sq_sqrt (by nlinarith [sq_nonneg (x+y)])

theorem length_eq (x y u : ℝ) : length x y u=x+y+2*shift x y u := by
  unfold shift
  ring

theorem shift_pos {x y u : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 < u) :
    0 < shift x y u := by
  have hs := length_sq x y hu.le
  have hp := length_pos x y hu
  have h : x+y < length x y u := by nlinarith
  unfold shift
  linarith

theorem shift_zero {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : shift x y 0=0 := by
  simp only [shift,length,mul_zero,add_zero,Real.sqrt_sq (add_nonneg hx hy)]
  ring

theorem coordinate_shift {x y u : ℝ} (hu : 0 ≤ u) :
    coordinate x y (shift x y u)=u := by
  have hs := length_sq x y hu
  dsimp only [coordinate,shift]
  nlinarith only [hs]

theorem shift_coordinate {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) :
    shift x y (coordinate x y t)=t := by
  have he : (x+y)^2+4*coordinate x y t=(x+y+2*t)^2 := by
    unfold coordinate
    ring
  simp only [shift,length,he,Real.sqrt_sq (by positivity : 0 ≤ x+y+2*t)]
  ring

theorem coordinate_hasDerivAt (x y t : ℝ) :
    HasDerivAt (coordinate x y) (x+y+2*t) t := by
  convert! (hasDerivAt_id t).mul (((hasDerivAt_id t).add_const x).add_const y) using 1
  dsimp
  ring

private theorem coordinate_injOn {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    InjOn (coordinate x y) (Ioi 0) := by
  intro a ha b hb he
  have h := congrArg (shift x y) he
  simpa only [shift_coordinate hx hy ha.le,shift_coordinate hx hy hb.le] using h

private theorem coordinate_image {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    coordinate x y '' Ioi 0=Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩
    have ht0 : 0 < t := ht
    change 0 < t*(t+x+y)
    exact mul_pos ht0 (by linarith)
  · intro hu
    exact ⟨shift x y u,shift_pos hx hy hu,coordinate_shift hu.le⟩

theorem potential_comm (x y u : ℝ) : potential x y u=potential y x u := by
  have hs : shift x y u=shift y x u := by
    unfold shift length
    rw [add_comm x y]
    ring
  simp only [potential,hs]
  ring

theorem potential_zero {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : potential x y 0=0 := by
  simp only [potential,shift_zero hx hy,add_zero]
  ring

theorem potential_continuous (x y : ℝ) : Continuous (potential x y) := by
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun t =>
    (ThetaCoordinate.sourcePotential_hasDerivAt t).continuousAt
  have hs : Continuous (shift x y) := by unfold shift length; fun_prop
  exact (((hU.comp (continuous_const.add hs)).add
    (hU.comp (continuous_const.add hs))).sub continuous_const).sub continuous_const

theorem density_pos (x y u : ℝ) : 0 < density x y u := Real.exp_pos _

theorem density_continuous (x y : ℝ) : Continuous (density x y) :=
  Real.continuous_exp.comp (potential_continuous x y).neg

theorem density_eq (x y u : ℝ) :
    density x y u=k (x+shift x y u)*k (y+shift x y u)/(k x*k y) := by
  have he : -potential x y u =
      (Real.log (k (x+shift x y u))+Real.log (k (y+shift x y u)))-
        (Real.log (k x)+Real.log (k y)) := by
    unfold potential ThetaCoordinate.sourcePotential thetaCuspLogSource
    ring
  rw [density,he,Real.exp_sub,Real.exp_add,Real.exp_add]
  simp only [Real.exp_log (thetaCuspFullSource_pos_all _)]

private theorem density_coordinate {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t) :
    |x+y+2*t| • density x y (coordinate x y t)=
      thetaTailCommonTranslationIntegrand x y t/(k x*k y) := by
  rw [density_eq,shift_coordinate hx hy ht.le,abs_of_pos (by linarith : 0 < x+y+2*t),
    smul_eq_mul]
  unfold thetaTailCommonTranslationIntegrand
  ring

/-- Integrability transports from the already integrable actual common-tail density. -/
theorem density_integrable {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IntegrableOn (density x y) (Ioi 0) := by
  have he := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0:ℝ)) => (coordinate_hasDerivAt x y t).hasDerivWithinAt)
    (coordinate_injOn hx hy) (density x y)
  rw [coordinate_image hx hy] at he
  apply he.mpr
  apply ((integrable_thetaTailCommonTranslationIntegrand x y).div_const (k x*k y)).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (density_coordinate hx hy ht).symm

/-- Exact coarea identity for the literal source-normalized full-tail kernel. -/
theorem integral_density {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∫ u in Ioi 0, density x y u)=H x y/(k x*k y) := by
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t (_ : t ∈ Ioi (0:ℝ)) => (coordinate_hasDerivAt x y t).hasDerivWithinAt)
    (coordinate_injOn hx hy) (density x y)
  rw [coordinate_image hx hy] at he
  rw [he]
  calc
    _ = ∫ t in Ioi 0, thetaTailCommonTranslationIntegrand x y t/(k x*k y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact density_coordinate hx hy ht
    _ = _ := by
      rw [integral_div]
      congr 1
      simpa only [add_zero] using (thetaTailFirstMomentKernel_commonShift_eq_tail 0 x y).symm

end RHTower.ThetaGaussianCoarea
