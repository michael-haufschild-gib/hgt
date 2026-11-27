import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts.Gap
import Mathlib.Analysis.Calculus.LHopital

/-! # Positive range of the quotient of two centered sine gaps -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts

open Real Set Filter Topology

/-- Ratio of the first surviving cubic coefficients at zero damping. -/
def wall (a b c : ℝ) := b*(b^2-a^2)/(c*(c^2-a^2))

theorem gap_ratio_wall {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    Tendsto (fun x => gap a b x/gap a c x) (𝓝[>] 0) (𝓝 (wall a b c)) := by
  let P (r : ℝ) := (r+a)/2
  let M (r : ℝ) := (r-a)/2
  have hb := ha.trans hab
  have hc := hb.trans hbc
  have hp (r : ℝ) (ar : a<r) : 0<P r := half_pos (add_pos (ha.trans ar) ha)
  have hm (r : ℝ) (ar : a<r) : 0<M r := half_pos (sub_pos.mpr ar)
  have ac := hab.trans hbc
  have ratio {i j : ℝ} (hi : 0 < i) (hj : 0<j) :
      Tendsto (fun x => sinh (i*x)/sinh (j*x)) (𝓝[>] 0) (𝓝 (i/j)) :=
    (_root_.RHTower.tendsto_sinh_rate_ratio_nhdsNE_zero hj.ne' hi.ne').mono_left
      (nhdsWithin_mono _ (fun _ h => ne_of_gt h))
  have dlim := (tendsto_const_nhds (x := b/c) (f := 𝓝[>] (0 : ℝ))).mul
    ((ratio (hp b hab) (hp c ac)).mul (ratio (hm b hab) (hm c ac)))
  have w : b/c*((P b/P c)*(M b/M c))=wall a b c := by
    dsimp only [wall,P,M]
    have cub : c^2-a^2=(c+a)*(c-a) := by ring
    rw [cub]
    field_simp [hc.ne',(add_pos hc ha).ne',(sub_pos.mpr ac).ne']; ring
  rw [w] at dlim
  have sp (r : ℝ) (hr : 0<r) (x : ℝ) (hx : 0<x) := sinh_pos_iff.mpr (mul_pos hr hx)
  have dl : Tendsto (fun x => speed a b x/speed a c x) (𝓝[>] 0) (𝓝 (wall a b c)) := by
    apply dlim.congr'
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
    rw [factor_speed,factor_speed]
    change _=2*a*b*sinh (P b*x)*sinh (M b*x)/(2*a*c*sinh (P c*x)*sinh (M c*x))
    field_simp [ha.ne',hc.ne',(sp _ (hp c ac) x hx).ne',(sp _ (hm c ac) x hx).ne']
  have zero (r : ℝ) : Tendsto (gap a r) (𝓝[>] 0) (𝓝 0) := by
    have cont : Continuous (gap a r) := by unfold gap; fun_prop
    simpa only [gap,mul_zero,sinh_zero,sub_self] using (cont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_nhdsGT (Eventually.of_forall (differentiated a b))
    (Eventually.of_forall (differentiated a c)) _ (zero b) (zero c) dl
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
  rw [factor_speed]
  exact (mul_pos (mul_pos (mul_pos (mul_pos zero_lt_two ha) hc) (sp _ (hp c ac) x hx))
    (sp _ (hm c ac) x hx)).ne'

theorem gap_ratio_infty {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c) :
    Tendsto (fun x => gap a b x/gap a c x) atTop (𝓝 0) := by
  have small {r : ℝ} (hr : 0<r) (lt : r<c) :
      Tendsto (fun x => sinh (r*x)/sinh (c*x)) atTop (𝓝 0) := by
    have inv := (_root_.RHTower.tendsto_sinh_rate_ratio_atTop hr lt).inv_tendsto_atTop
    change Tendsto (fun x => (sinh (c*x)/sinh (r*x))⁻¹) atTop (𝓝 0) at inv
    simpa only [inv_div] using inv
  have lo := small ha (hab.trans hbc)
  have mid := small (ha.trans hab) hbc
  have lim := ((mid.const_mul a).sub (lo.const_mul b)).div
    ((tendsto_const_nhds (x := a)).sub (lo.const_mul c)) (by simpa only [mul_zero,sub_zero] using ha.ne')
  simp only [mul_zero,sub_zero,zero_div] at lim
  apply lim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have nz := (sinh_pos_iff.mpr (mul_pos ((ha.trans hab).trans hbc) hx)).ne'
  change (a*(sinh (b*x)/sinh (c*x))-b*(sinh (a*x)/sinh (c*x)))/
    (a-c*(sinh (a*x)/sinh (c*x)))=gap a b x/gap a c x
  rw [show a*(sinh (b*x)/sinh (c*x))-b*(sinh (a*x)/sinh (c*x))=gap a b x/sinh (c*x) by
    unfold gap; ring,
    show a-c*(sinh (a*x)/sinh (c*x))=gap a c x/sinh (c*x) by unfold gap; field_simp]
  exact div_div_div_cancel_right₀ nz _ _

/-- The cubic wall and zero are the unattained endpoint values. Each interior
value occurs at exactly one positive clock. -/
theorem gap_ratio_unique_iff {a b c : ℝ} (ha : 0<a) (hab : a<b) (hbc : b<c) (q : ℝ) :
    (∃! x : ℝ, 0<x ∧ gap a b x/gap a c x=q) ↔ 0<q ∧ q<wall a b c := by
  let f (x : ℝ) := gap a b x/gap a c x
  have anti : StrictAntiOn f (Ioi 0) := gap_ratio_strictAnti ha hab hbc
  have hz := gap_ratio_wall ha hab hbc
  have bound {x : ℝ} (hx : 0<x) : f x<wall a b c := by
    have half := half_pos hx
    have order := anti half hx (half_lt_self hx)
    apply order.trans_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hz
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0),
      (eventually_lt_nhds half).filter_mono nhdsWithin_le_nhds] with y hy hlt
    exact (anti hy half hlt).le
  constructor
  · rintro ⟨x,⟨hx,rfl⟩,_⟩
    exact ⟨div_pos (gap_pos ha hab hx) (gap_pos ha (hab.trans hbc) hx),bound hx⟩
  · rintro ⟨hq,hw⟩
    have ev := tendsto_const_nhds.eventually_lt hz hw
    have positive : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<x := self_mem_nhdsWithin
    obtain ⟨x,hx,hxq⟩ := (positive.and ev).exists
    have small := (gap_ratio_infty ha hab hbc).eventually_lt tendsto_const_nhds hq
    obtain ⟨y,hxy,hyq⟩ := ((eventually_gt_atTop x).and small).exists
    have xc : 0<x := hx
    have cont : ContinuousOn f (Icc x y) := by
      apply ContinuousOn.div (by unfold gap; fun_prop) (by unfold gap; fun_prop)
      exact fun z hz => (gap_pos ha (hab.trans hbc) (xc.trans_le hz.1)).ne'
    obtain ⟨z,hz',val⟩ := intermediate_value_Icc' hxy.le cont (show q ∈ Icc (f y) (f x) from ⟨hyq.le,hxq.le⟩)
    have pos := xc.trans_le hz'.1
    exact ⟨z,⟨pos,val⟩,fun w hw => anti.injOn hw.1 pos (hw.2.trans val.symm)⟩

#print axioms gap_ratio_wall
#print axioms gap_ratio_infty
#print axioms gap_ratio_unique_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.AllCounts
