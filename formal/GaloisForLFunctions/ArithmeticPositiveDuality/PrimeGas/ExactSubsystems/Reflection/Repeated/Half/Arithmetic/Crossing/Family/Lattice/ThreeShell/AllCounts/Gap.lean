import GaloisForLFunctions.RHTower.C5FixedActionDescentLemmas
import GaloisForLFunctions.RHTower.ReflectedBiHeatArbitraryTwoRateReceiverCone
import GaloisForLFunctions.HTGeometry.HyperbolicSineScaleMonotonicity

/-! # Strict decrease of centered hyperbolic sine gap ratios -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Real Set

/-- Subtracting the linear moment cancels the first-order response at zero. -/
def gap (a b x : ℝ) := a*sinh (b*x)-b*sinh (a*x)

theorem gap_pos {a b x : ℝ} (ha : 0<a) (hab : a<b) (hx : 0<x) : 0<gap a b x := by
  have ap := mul_pos ha hx
  have bp := mul_pos (ha.trans hab) hx
  have h := (div_lt_div_iff₀ ap bp).mp (_root_.HTGeometry.strictMonoOn_sinh_div_self ap bp
    (mul_lt_mul_of_pos_right hab hx))
  apply sub_pos.mpr
  apply (mul_lt_mul_iff_left₀ hx).mp
  calc (b*sinh (a*x))*x = sinh (a*x)*(b*x) := by ring
       _ < sinh (b*x)*(a*x) := h
       _ = (a*sinh (b*x))*x := by ring

/-- The low-rate boundary includes a missing upper level and coincident rates. -/
theorem gap_nonpos {a b x : ℝ} (hb : 0≤b) (hba : b≤a) (hx : 0<x) : gap a b x≤0 := by
  rcases hb.eq_or_lt with hz | hp
  · rw [← hz]; simp [gap]
  rcases hba.eq_or_lt with rfl | lt
  · simp [gap]
  · have h := gap_pos hp lt hx
    dsimp only [gap] at h ⊢
    linarith only [h]

def speed (a b x : ℝ) := a*b*(cosh (b*x)-cosh (a*x))

theorem differentiated (a b x : ℝ) : HasDerivAt (gap a b) (speed a b x) x := by
  have h (r : ℝ) : HasDerivAt (fun y : ℝ => sinh (r*y)) (cosh (r*x)*r) x := by
    simpa only [Function.comp_def,mul_one] using
      (hasDerivAt_sinh (r*x)).comp x ((hasDerivAt_id x).const_mul r)
  rw [show speed a b x=a*(cosh (b*x)*b)-b*(cosh (a*x)*a) by unfold speed; ring]
  exact ((h b).const_mul a).sub ((h a).const_mul b)

theorem factor_speed (a b x : ℝ) :
    speed a b x=2*a*b*sinh (((b+a)/2)*x)*sinh (((b-a)/2)*x) := by
  let U := ((b+a)/2)*x
  let V := ((b-a)/2)*x
  have e : b*x=U+V := by dsimp only [U,V]; ring
  have f : a*x=U-V := by dsimp only [U,V]; ring
  rw [speed,e,f,cosh_add,cosh_sub]
  dsimp only [U,V]
  ring

private theorem rev_ratio {b c : ℝ} (hb : 0<b) (hbc : b<c) :
    StrictAntiOn (fun x => sinh (b*x)/sinh (c*x)) (Ioi 0) := by
  intro x hx y hy lt
  have h := _root_.RHTower.sinh_rate_ratio_strictMonoOn hb hbc hx hy lt
  have pos (z : ℝ) (hz : 0<z) : 0<sinh (c*z)/sinh (b*z) :=
    div_pos (sinh_pos_iff.mpr (mul_pos (hb.trans hbc) hz)) (sinh_pos_iff.mpr (mul_pos hb hz))
  have inv := (inv_lt_inv₀ (pos y hy) (pos x hx)).mpr h
  simpa only [inv_div] using inv

/-- The ratio of the two moment-cancelled responses falls strictly with damping. -/
theorem gap_ratio_strictAnti {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    StrictAntiOn (fun x => gap a b x/gap a c x) (Ioi 0) := by
  have hb := ha.trans hab
  have hc := hb.trans hbc
  let hi (r : ℝ) := (r+a)/2
  let lo (r : ℝ) := (r-a)/2
  have hp : 0<hi b := half_pos (add_pos hb ha)
  have lp : 0<lo b := half_pos (sub_pos.mpr hab)
  have hh : hi b<hi c := div_lt_div_of_pos_right (add_lt_add_left hbc _) zero_lt_two
  have ll : lo b<lo c := div_lt_div_of_pos_right (sub_lt_sub_right hbc _) zero_lt_two
  have sp {r x : ℝ} (hr : 0<r) (hx : 0<x) : 0<sinh (r*x) := sinh_pos_iff.mpr (mul_pos hr hx)
  have form (x : ℝ) (hx : 0<x) : speed a b x/speed a c x=
      b/c*((sinh (hi b*x)/sinh (hi c*x))*(sinh (lo b*x)/sinh (lo c*x))) := by
    rw [factor_speed,factor_speed]
    change 2*a*b*sinh (hi b*x)*sinh (lo b*x)/(2*a*c*sinh (hi c*x)*sinh (lo c*x))=_
    field_simp [ha.ne',hc.ne',(sp (hp.trans hh) hx).ne',(sp (lp.trans ll) hx).ne']
  have anti : StrictAntiOn (fun x => speed a b x/speed a c x) (Ioi 0) := by
    intro x hx y hy h
    change speed a b y/speed a c y<speed a b x/speed a c x
    rw [form x hx,form y hy]
    apply mul_lt_mul_of_pos_left _ (div_pos hb hc)
    exact (mul_lt_mul_of_pos_right ((rev_ratio hp hh) hx hy h)
      (div_pos (sp lp hy) (sp (lp.trans ll) hy))).trans
      (mul_lt_mul_of_pos_left ((rev_ratio lp ll) hx hy h) (div_pos (sp hp hx) (sp (hp.trans hh) hx)))
  intro x hx y hy hxy
  have pos (v : ℝ) (hv : 0<v) : 0<speed a c v := by
    rw [factor_speed]
    exact mul_pos (mul_pos (mul_pos (mul_pos zero_lt_two ha) hc) (sp (hp.trans hh) hv)) (sp (lp.trans ll) hv)
  exact _root_.RHTower.strictAntiOn_ratio_of_strictAnti_derivRatio (N := gap a b) (D := gap a c)
    hy (by simp [gap]) (by simp [gap]) (by unfold gap; fun_prop) (by unfold gap; fun_prop)
    (fun z _ => differentiated a b z) (fun z _ => differentiated a c z)
    (fun z hz => pos z hz.1) (anti.mono fun _ hz => hz.1)
    ⟨hx,hxy.le⟩ ⟨hy,le_rfl⟩ hxy

#print axioms gap_ratio_strictAnti

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
