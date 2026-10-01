import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set Filter
open scoped Topology
namespace RHTower
noncomputable section

def liClockCoshCosCutoff (u v a T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T,
    Real.exp (-a * t) *
      (1 - Real.cos (u * t) * Real.cosh (v * t)) / t

private def cgNumerator (u v a t : ℝ) : ℝ :=
  Real.exp (-a*t)*(1-Real.cos (u*t)*Real.cosh (v*t))

private def cgProfile (u v a t : ℝ) : ℝ := cgNumerator u v a t/t

private theorem cgNumerator_hasDerivAt_zero (u v a : ℝ) :
    HasDerivAt (cgNumerator u v a) 0 0 := by
  have he := (Real.hasDerivAt_exp (-a*0)).comp 0 ((hasDerivAt_id 0).const_mul (-a))
  have hc := (Real.hasDerivAt_cos (u*0)).comp 0 ((hasDerivAt_id 0).const_mul u)
  have hh := (Real.hasDerivAt_cosh (v*0)).comp 0 ((hasDerivAt_id 0).const_mul v)
  convert he.mul ((hasDerivAt_const 0 (1:ℝ)).sub (hc.mul hh)) using 1 <;>
    first | rfl | norm_num

private theorem cgProfile_eq_dslope (u v a : ℝ) :
    cgProfile u v a = dslope (cgNumerator u v a) 0 := by
  funext t
  by_cases ht : t=0
  · subst t
    rw [dslope_same, (cgNumerator_hasDerivAt_zero u v a).deriv]
    simp [cgProfile]
  · rw [dslope_of_ne _ ht, slope_def_field]
    simp [cgProfile, cgNumerator]

private theorem cgProfile_continuous (u v a : ℝ) : Continuous (cgProfile u v a) := by
  rw [cgProfile_eq_dslope]
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    exact continuousAt_dslope_same.mpr (cgNumerator_hasDerivAt_zero u v a).differentiableAt
  · apply (continuousAt_dslope_of_ne ht).mpr
    unfold cgNumerator
    fun_prop

private theorem cgCutoff_hasDerivAt_time (u v a T : ℝ) :
    HasDerivAt (liClockCoshCosCutoff u v a) (cgProfile u v a T) T := by
  have h := cgProfile_continuous u v a
  exact intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 T)
    h.stronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt

private theorem cgCutoff_continuous (u v a : ℝ) :
    Continuous (liClockCoshCosCutoff u v a) :=
  continuous_iff_continuousAt.mpr (fun T => (cgCutoff_hasDerivAt_time u v a T).continuousAt)

private theorem cgWeightedSine_nonneg {w w' : ℝ → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hw : ContinuousOn w (Icc 0 R)) (hw' : ContinuousOn w' (Icc 0 R))
    (hd : ∀ x ∈ Icc 0 R, HasDerivAt w (w' x) x)
    (hn : ∀ x ∈ Icc 0 R, 0 ≤ w x) (hneg : ∀ x ∈ Icc 0 R, w' x ≤ 0) :
    0 ≤ ∫ x in 0..R, w x * Real.sin x := by
  have hH : Continuous (fun x : ℝ => 1-Real.cos x) := by fun_prop
  have hwc : ContinuousOn w (uIcc 0 R) := by simpa [uIcc_of_le hR] using hw
  have hwc' : ContinuousOn w' (uIcc 0 R) := by simpa [uIcc_of_le hR] using hw'
  have hi := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hwc hH.continuousOn
    (fun x hx => hd x (by simpa [min_eq_left hR,max_eq_right hR] using Ioo_subset_Icc_self hx))
    (fun x _ => by simpa using (Real.hasDerivAt_cos x).const_sub 1)
    hwc'.intervalIntegrable (Real.continuous_sin.intervalIntegrable 0 R)
  have hprod : IntervalIntegrable (fun x => w' x*(1-Real.cos x)) volume 0 R :=
    (hwc'.mul hH.continuousOn).intervalIntegrable
  have hsin : IntervalIntegrable (fun x => w x*Real.sin x) volume 0 R :=
    (hwc.mul Real.continuous_sin.continuousOn).intervalIntegrable
  rw [intervalIntegral.integral_add hprod hsin] at hi
  simp only [Real.cos_zero, sub_self, mul_zero, sub_zero] at hi
  have hnon : 0 ≤ ∫ x in 0..R, -(w' x*(1-Real.cos x)) :=
    intervalIntegral.integral_nonneg hR (fun x hx => by
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hneg x hx)
        (sub_nonneg.mpr (Real.cos_le_one x))))
  rw [intervalIntegral.integral_neg] at hnon
  have hend : 0 ≤ w R*(1-Real.cos R) :=
    mul_nonneg (hn R ⟨hR,le_rfl⟩) (sub_nonneg.mpr (Real.cos_le_one R))
  linarith

private theorem cgDampedSine_nonneg {b u T : ℝ} (hb : 0 ≤ b) (hu : 0 < u)
    (hT : 0 ≤ T) : 0 ≤ ∫ t in 0..T, Real.exp (-b*t)*Real.sin (u*t) := by
  let w := fun x : ℝ => Real.exp (-(b/u)*x)
  let w' := fun x : ℝ => -(b/u)*Real.exp (-(b/u)*x)
  have hd (x : ℝ) : HasDerivAt w (w' x) x := by
    convert (Real.hasDerivAt_exp (-(b/u)*x)).comp x
      ((hasDerivAt_id x).const_mul (-(b/u))) using 1 <;>
      first | rfl | (dsimp only [w,w']; ring)
  have hn := cgWeightedSine_nonneg (mul_nonneg hu.le hT)
    (by dsimp [w]; fun_prop) (by dsimp [w']; fun_prop)
    (fun x _ => hd x) (fun x _ => (Real.exp_pos _).le)
    (fun x _ => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hb hu.le))
      (Real.exp_pos _).le)
  have he : (fun t : ℝ => Real.exp (-b*t)*Real.sin (u*t)) =
      fun t => (w (u*t)*Real.sin (u*t)) := by
    funext t
    dsimp [w]
    congr 2
    field_simp [hu.ne']
  rw [he, intervalIntegral.integral_comp_mul_left
    (fun x => w x*Real.sin x) hu.ne', mul_zero]
  exact mul_nonneg (inv_nonneg.mpr hu.le) hn

private def cgCosCoshDerivative (x : ℝ) : ℝ :=
  Real.cos x*Real.sinh x-Real.sin x*Real.cosh x

private theorem cgCosCoshDerivative_hasDerivAt (x : ℝ) :
    HasDerivAt cgCosCoshDerivative (-2*Real.sin x*Real.sinh x) x := by
  convert ((Real.hasDerivAt_cos x).mul (Real.hasDerivAt_sinh x)).sub
    ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cosh x)) using 1 <;>
    first | rfl | ring

private theorem cgCosCosh_hasDerivAt (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos x*Real.cosh x) (cgCosCoshDerivative x) x := by
  convert (Real.hasDerivAt_cos x).mul (Real.hasDerivAt_cosh x) using 1 <;>
    first | rfl | (dsimp [cgCosCoshDerivative]; ring)

private theorem cgCosCosh_lt_one {x : ℝ} (hx : 0 < x) (hB : x ≤ Real.pi/2) :
    Real.cos x*Real.cosh x < 1 := by
  have hq : StrictAntiOn cgCosCoshDerivative (Icc 0 (Real.pi/2)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) (by unfold cgCosCoshDerivative; fun_prop)
      (fun t ht => by
        rw [interior_Icc] at ht
        rw [(cgCosCoshDerivative_hasDerivAt t).deriv]
        have hsin := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
        have hsinh := Real.sinh_pos_iff.mpr ht.1
        nlinarith)
  have hqn (t : ℝ) (ht : t ∈ Ioo 0 (Real.pi/2)) : cgCosCoshDerivative t < 0 := by
    have h := hq ⟨le_rfl, (by positivity)⟩ ⟨ht.1.le,ht.2.le⟩ ht.1
    simpa [cgCosCoshDerivative] using h
  have hh : StrictAntiOn (fun t : ℝ => Real.cos t*Real.cosh t) (Icc 0 (Real.pi/2)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop) (fun t ht => by
      rw [interior_Icc] at ht
      rw [(cgCosCosh_hasDerivAt t).deriv]
      exact hqn t ht)
  have h := hh ⟨le_rfl, (by positivity)⟩ ⟨hx.le,hB⟩ hx
  simpa using h

private theorem cgDiagonal_small_pos {X : ℝ} (hX : 0 < X) (hB : X ≤ Real.pi/2) :
    0 < liClockCoshCosCutoff 1 1 1 X := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((cgProfile_continuous 1 1 1).intervalIntegrable 0 X) _ hX
  intro x hx
  have hc := cgCosCosh_lt_one hx.1 (hx.2.le.trans hB)
  dsimp [cgProfile, cgNumerator]
  simp only [one_mul]
  exact div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr hc)) hx.1

private theorem cgProfile_hasDerivAt_frequency (u v a t : ℝ) :
    HasDerivAt (fun u => cgProfile u v a t)
      (Real.exp (-a*t)*Real.cosh (v*t)*Real.sin (u*t)) u := by
  by_cases ht : t=0
  · subst t
    simpa [cgProfile, cgNumerator] using (hasDerivAt_const u (0:ℝ))
  · have hc := (Real.hasDerivAt_cos (u*t)).comp u ((hasDerivAt_id u).mul_const t)
    have hd := ((hc.mul_const (Real.cosh (v*t))).const_sub 1).const_mul
      (Real.exp (-a*t))
    convert hd.div_const t using 1 <;> first | rfl | field_simp [ht]

private theorem cgCutoff_hasDerivAt_frequency (u v a T : ℝ)
    (hv : 0 ≤ v) (ha : v ≤ a) (hT : 0 ≤ T) :
    HasDerivAt (fun u => liClockCoshCosCutoff u v a T)
      (∫ t in 0..T, Real.exp (-a*t)*Real.cosh (v*t)*Real.sin (u*t)) u := by
  have hc (u : ℝ) : Continuous (fun t => Real.exp (-a*t)*Real.cosh (v*t)*Real.sin (u*t)) := by
    fun_prop
  have hb (u t : ℝ) (ht : t ∈ uIoc 0 T) :
      ‖Real.exp (-a*t)*Real.cosh (v*t)*Real.sin (u*t)‖ ≤ Real.cosh (v*T) := by
    rw [uIoc_of_le hT] at ht
    have hat : -a*t ≤ 0 := by
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg (hv.trans ha) ht.1.le)
    have he : Real.exp (-a*t) ≤ 1 := by simpa using Real.exp_le_exp.mpr hat
    have hc : Real.cosh (v*t) ≤ Real.cosh (v*T) :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg (mul_nonneg hv ht.1.le), abs_of_nonneg (mul_nonneg hv hT)]
        exact mul_le_mul_of_nonneg_left ht.2 hv)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.cosh_pos _).le, Real.norm_eq_abs]
    calc
      _ ≤ Real.exp (-a*t)*Real.cosh (v*t)*1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
      _ ≤ Real.cosh (v*t) := by nlinarith [Real.cosh_pos (v*t)]
      _ ≤ Real.cosh (v*T) := hc
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=univ) (bound:=fun _ => Real.cosh (v*T)) (by simp)
    (Eventually.of_forall (fun u => (cgProfile_continuous u v a).stronglyMeasurable.aestronglyMeasurable))
    ((cgProfile_continuous u v a).intervalIntegrable 0 T)
    (hc u).stronglyMeasurable.aestronglyMeasurable
    (ae_of_all _ (fun t ht u _ => hb u t ht)) (continuous_const.intervalIntegrable 0 T)
    (ae_of_all _ (fun t _ u _ => cgProfile_hasDerivAt_frequency u v a t))).2

private theorem cgExpCosh (a v t : ℝ) :
    Real.exp (-a*t)*Real.cosh (v*t) =
      (Real.exp (-(a-v)*t)+Real.exp (-(a+v)*t))/2 := by
  rw [Real.cosh_eq]
  rw [← mul_div_assoc, mul_add, ← Real.exp_add, ← Real.exp_add]
  rw [show -a*t+v*t=-(a-v)*t by ring,
    show -a*t+ -(v*t)=-(a+v)*t by ring]

private theorem cgCutoff_frequency_derivative_nonneg {u v a T : ℝ}
    (hu : 0 < u) (hv : 0 ≤ v) (ha : v ≤ a) (hT : 0 ≤ T) :
    0 ≤ ∫ t in 0..T, Real.exp (-a*t)*Real.cosh (v*t)*Real.sin (u*t) := by
  have h1 : IntervalIntegrable (fun t => Real.exp (-(a-v)*t)*Real.sin (u*t)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h2 : IntervalIntegrable (fun t => Real.exp (-(a+v)*t)*Real.sin (u*t)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have he : (fun t : ℝ => Real.exp (-a*t)*Real.cosh (v*t)*Real.sin (u*t)) =
      fun t => (1/2:ℝ)*(Real.exp (-(a-v)*t)*Real.sin (u*t)+
        Real.exp (-(a+v)*t)*Real.sin (u*t)) := by
    funext t
    rw [cgExpCosh]
    ring
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2]
  exact mul_nonneg (by norm_num) (add_nonneg
    (cgDampedSine_nonneg (sub_nonneg.mpr ha) hu hT)
    (cgDampedSine_nonneg (by linarith) hu hT))

private theorem cgCutoff_monotone_frequency {v a T : ℝ}
    (hv : 0 ≤ v) (ha : v ≤ a) (hT : 0 ≤ T) :
    MonotoneOn (fun u => liClockCoshCosCutoff u v a T) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun u _ => (cgCutoff_hasDerivAt_frequency u v a T hv ha hT).continuousAt.continuousWithinAt)
    (fun u _ => (cgCutoff_hasDerivAt_frequency u v a T hv ha hT).differentiableAt.differentiableWithinAt)
  intro u hu
  rw [interior_Ioi] at hu
  rw [(cgCutoff_hasDerivAt_frequency u v a T hv ha hT).deriv]
  exact cgCutoff_frequency_derivative_nonneg hu hv ha hT

private def cgShiftedWeight (y : ℝ) : ℝ :=
  (1+Real.exp (-2*(Real.pi/2+y)))/(2*(Real.pi/2+y))

private def cgShiftedWeightPrime (y : ℝ) : ℝ :=
  -Real.exp (-2*(Real.pi/2+y))/(Real.pi/2+y)-
    (1+Real.exp (-2*(Real.pi/2+y)))/(2*(Real.pi/2+y)^2)

private theorem cgShiftedWeight_hasDerivAt {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt cgShiftedWeight (cgShiftedWeightPrime y) y := by
  have hz : Real.pi/2+y ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
  have hlin := (hasDerivAt_id y).const_add (Real.pi/2)
  have he := (Real.hasDerivAt_exp (-2*(Real.pi/2+y))).comp y (hlin.const_mul (-2))
  have hn := he.const_add 1
  have hd := hlin.const_mul 2
  convert hn.div hd (by dsimp; exact mul_ne_zero (by norm_num) hz) using 1 <;>
    first | rfl | (dsimp only [cgShiftedWeightPrime,Function.comp_def,id_eq]; field_simp [hz])

private theorem cgShiftedSine_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ ∫ y in 0..R, cgShiftedWeight y*Real.sin y := by
  have hz (y : ℝ) (hy : y ∈ Icc 0 R) : Real.pi/2+y ≠ 0 :=
    ne_of_gt (by linarith [hy.1,Real.pi_pos])
  have hc1 : ContinuousOn (fun y : ℝ => -Real.exp (-2*(Real.pi/2+y))/(Real.pi/2+y)) (Icc 0 R) :=
    (by fun_prop : Continuous (fun y : ℝ => -Real.exp (-2*(Real.pi/2+y)))).continuousOn.div
      (by fun_prop) hz
  have hc2 : ContinuousOn (fun y : ℝ => (1+Real.exp (-2*(Real.pi/2+y)))/(2*(Real.pi/2+y)^2)) (Icc 0 R) :=
    (by fun_prop : Continuous (fun y : ℝ => 1+Real.exp (-2*(Real.pi/2+y)))).continuousOn.div
      (by fun_prop) (fun y hy => mul_ne_zero (by norm_num) (pow_ne_zero _ (hz y hy)))
  apply cgWeightedSine_nonneg hR
    ((by fun_prop : Continuous (fun y : ℝ => 1+Real.exp (-2*(Real.pi/2+y)))).continuousOn.div
      (by fun_prop) (fun y hy => mul_ne_zero (by norm_num) (hz y hy)))
    (hc1.sub hc2) (fun y hy => cgShiftedWeight_hasDerivAt hy.1)
  · intro y hy
    dsimp [cgShiftedWeight]
    have hp : 0 < Real.pi/2+y := by linarith [hy.1,Real.pi_pos]
    exact div_nonneg (by positivity) (by positivity)
  · intro y hy
    dsimp [cgShiftedWeightPrime]
    have hp : 0 < Real.pi/2+y := by linarith [hy.1,Real.pi_pos]
    exact sub_nonpos.mpr (le_trans (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.exp_pos _).le) hp.le) (by positivity))

private theorem cgDiagonal_tail_profile {x : ℝ} (_hx : Real.pi/2 ≤ x) :
    cgProfile 1 1 1 x = Real.exp (-x)/x+
      cgShiftedWeight (x-Real.pi/2)*Real.sin (x-Real.pi/2) := by
  have hcos : Real.cos x = -Real.sin (x-Real.pi/2) := by
    have hz : x-Real.pi/2+Real.pi/2=x := by ring
    rw [← hz]
    simpa only [hz] using Real.cos_add_pi_div_two (x-Real.pi/2)
  have hE : Real.exp (-x)*Real.cosh x = (1+Real.exp (-2*x))/2 := by
    convert cgExpCosh 1 1 x using 1 <;> norm_num
  dsimp [cgProfile,cgNumerator,cgShiftedWeight]
  rw [show Real.pi/2+(x-Real.pi/2)=x by ring]
  simp only [one_mul, neg_one_mul]
  rw [hcos]
  linear_combination (Real.sin (x-Real.pi/2)/x)*hE

private theorem cgDiagonal_tail_eq {X : ℝ} (hX : Real.pi/2 ≤ X) :
    liClockCoshCosCutoff 1 1 1 X = liClockCoshCosCutoff 1 1 1 (Real.pi/2)+
      (∫ x in Real.pi/2..X, Real.exp (-x)/x)+
      ∫ y in 0..X-Real.pi/2, cgShiftedWeight y*Real.sin y := by
  have hE : IntervalIntegrable (fun x : ℝ => Real.exp (-x)/x) volume (Real.pi/2) X := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hX]
    exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x))).continuousOn.div
      continuous_id.continuousOn (fun x hx => ne_of_gt (by linarith [hx.1,Real.pi_pos]))
  have hW : ContinuousOn (fun x : ℝ => cgShiftedWeight (x-Real.pi/2)*Real.sin (x-Real.pi/2))
      (uIcc (Real.pi/2) X) := by
    rw [uIcc_of_le hX]
    apply ContinuousOn.mul _ (by fun_prop)
    unfold cgShiftedWeight
    exact (by fun_prop : Continuous (fun x : ℝ => 1+Real.exp (-2*(Real.pi/2+(x-Real.pi/2))))).continuousOn.div
      (by fun_prop) (fun x hx => by
        apply mul_ne_zero (by norm_num)
        have hp : 0 < Real.pi/2+(x-Real.pi/2) := by linarith [hx.1,Real.pi_pos]
        exact hp.ne')
  have htr := intervalIntegral.integral_comp_add_right
    (fun x : ℝ => cgShiftedWeight (x-Real.pi/2)*Real.sin (x-Real.pi/2)) (Real.pi/2)
    (a:=0) (b:=X-Real.pi/2)
  simp only [zero_add, sub_add_cancel, add_sub_cancel_right] at htr
  calc
    liClockCoshCosCutoff 1 1 1 X = liClockCoshCosCutoff 1 1 1 (Real.pi/2)+
        ∫ x in Real.pi/2..X, cgProfile 1 1 1 x := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((cgProfile_continuous 1 1 1).intervalIntegrable 0 (Real.pi/2))
        ((cgProfile_continuous 1 1 1).intervalIntegrable (Real.pi/2) X)).symm
    _ = _ := by
      rw [intervalIntegral.integral_congr (fun x hx => cgDiagonal_tail_profile (by
        exact (by simpa only [uIcc_of_le hX] using hx : x ∈ Icc (Real.pi/2) X).1)),
        intervalIntegral.integral_add hE hW.intervalIntegrable, ← htr]
      ring

private theorem cgDiagonal_pos {X : ℝ} (hX : 0 < X) :
    0 < liClockCoshCosCutoff 1 1 1 X := by
  by_cases hB : X ≤ Real.pi/2
  · exact cgDiagonal_small_pos hX hB
  · have hBX : Real.pi/2 ≤ X := (lt_of_not_ge hB).le
    rw [cgDiagonal_tail_eq hBX]
    have h0 := cgDiagonal_small_pos (show 0 < Real.pi/2 by positivity) le_rfl
    have h1 : 0 ≤ ∫ x in Real.pi/2..X, Real.exp (-x)/x :=
      intervalIntegral.integral_nonneg hBX (fun x hx => div_nonneg (Real.exp_pos _).le
        (by linarith [hx.1,Real.pi_pos]))
    have h2 := cgShiftedSine_nonneg (sub_nonneg.mpr hBX)
    linarith

private theorem cgDiagonal_scale {v T : ℝ} (hv : 0 < v) :
    liClockCoshCosCutoff v v v T = liClockCoshCosCutoff 1 1 1 (v*T) := by
  have he : cgProfile v v v = fun t => v*cgProfile 1 1 1 (v*t) := by
    funext t
    by_cases ht : t=0
    · subst t; simp [cgProfile,cgNumerator]
    · dsimp [cgProfile,cgNumerator]
      simp only [one_mul]
      field_simp [hv.ne',ht]
  change (∫ t in 0..T, cgProfile v v v t) = _
  rw [he, intervalIntegral.integral_const_mul]
  change v*(∫ t in 0..T, cgProfile 1 1 1 (v*t)) = ∫ t in 0..v*T, cgProfile 1 1 1 t
  simpa only [smul_eq_mul, mul_zero] using
    intervalIntegral.smul_integral_comp_mul_left (cgProfile 1 1 1) v (a:=0) (b:=T)

private theorem cgBaseline_pos {u v T : ℝ} (hv : 0 < v) (huv : v ≤ u) (hT : 0 < T) :
    0 < liClockCoshCosCutoff u v v T := by
  have h0 : 0 < liClockCoshCosCutoff v v v T := by
    rw [cgDiagonal_scale hv]
    exact cgDiagonal_pos (mul_pos hv hT)
  have h1 := cgCutoff_monotone_frequency hv.le le_rfl hT.le hv (hv.trans_le huv) huv
  exact h0.trans_le h1

private theorem cgDamping_eq (u v a T : ℝ) :
    liClockCoshCosCutoff u v a T =
      Real.exp (-(a-v)*T)*liClockCoshCosCutoff u v v T+
      (a-v)*∫ t in 0..T, Real.exp (-(a-v)*t)*liClockCoshCosCutoff u v v t := by
  let Q := liClockCoshCosCutoff u v v
  let k := fun t : ℝ => Real.exp (-(a-v)*t)
  let k' := fun t : ℝ => -(a-v)*Real.exp (-(a-v)*t)
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hk' : Continuous k' := by dsimp [k']; fun_prop
  have hd (t : ℝ) : HasDerivAt k (k' t) t := by
    convert (Real.hasDerivAt_exp (-(a-v)*t)).comp t
      ((hasDerivAt_id t).const_mul (-(a-v))) using 1 <;> first | rfl | (dsimp only [k,k']; ring)
  have hQ : Continuous Q := cgCutoff_continuous u v v
  have hP := cgProfile_continuous u v v
  have hi := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hQ.continuousOn hk.continuousOn
    (fun t _ => cgCutoff_hasDerivAt_time u v v t) (fun t _ => hd t)
    (hP.intervalIntegrable 0 T) (hk'.intervalIntegrable 0 T)
  have h1 : (∫ t in 0..T, cgProfile u v v t*k t) = liClockCoshCosCutoff u v a T := by
    apply intervalIntegral.integral_congr
    intro t _
    have he : Real.exp (-a*t) = Real.exp (-v*t)*Real.exp (-(a-v)*t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    dsimp [cgProfile,cgNumerator,k,liClockCoshCosCutoff]
    rw [he]
    ring
  have h2 : (∫ t in 0..T, Q t*k' t) = -(a-v)*∫ t in 0..T, k t*Q t := by
    have he : (fun t => Q t*k' t) = fun t => -(a-v)*(k t*Q t) := by
      funext t
      dsimp [k,k']
      ring
    rw [he,intervalIntegral.integral_const_mul]
  have hprod : IntervalIntegrable (fun t => cgProfile u v v t*k t) volume 0 T :=
    (hP.mul hk).intervalIntegrable 0 T
  have hprod' : IntervalIntegrable (fun t => Q t*k' t) volume 0 T :=
    (hQ.mul hk').intervalIntegrable 0 T
  rw [intervalIntegral.integral_add hprod hprod',h1,h2] at hi
  have hQ0 : Q 0=0 := by simp [Q,liClockCoshCosCutoff]
  rw [hQ0,zero_mul,sub_zero] at hi
  dsimp [Q,k] at hi ⊢
  linarith

private theorem cgPositiveHyperbolic_pos {u v a T : ℝ}
    (hv : 0 < v) (huv : v ≤ u) (ha : v ≤ a) (hT : 0 < T) :
    0 < liClockCoshCosCutoff u v a T := by
  rw [cgDamping_eq]
  have h0 := cgBaseline_pos hv huv hT
  have h1 : 0 ≤ ∫ t in 0..T, Real.exp (-(a-v)*t)*liClockCoshCosCutoff u v v t :=
    intervalIntegral.integral_nonneg hT.le (fun t ht => mul_nonneg (Real.exp_pos _).le (by
      rcases eq_or_lt_of_le ht.1 with h | h
      · subst t; simp [liClockCoshCosCutoff]
      · exact (cgBaseline_pos hv huv h).le))
  exact add_pos_of_pos_of_nonneg (mul_pos (Real.exp_pos _) h0)
    (mul_nonneg (sub_nonneg.mpr ha) h1)

private theorem cgZeroHyperbolic_profile_nonneg {u a t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cgProfile u 0 a t := by
  by_cases h : t=0
  · subst t; simp [cgProfile]
  · dsimp [cgProfile,cgNumerator]
    simp only [zero_mul,Real.cosh_zero,mul_one]
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _))) ht

private theorem cgZeroHyperbolic_pos {u a T : ℝ} (hu : 0 < u) (hT : 0 < T) :
    0 < liClockCoshCosCutoff u 0 a T := by
  let E := min T (Real.pi/u)
  have hE : 0 < E := lt_min hT (div_pos Real.pi_pos hu)
  have hET : E ≤ T := min_le_left _ _
  have hEp : E ≤ Real.pi/u := min_le_right _ _
  have h0 : 0 < ∫ t in 0..E, cgProfile u 0 a t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((cgProfile_continuous u 0 a).intervalIntegrable 0 E) _ hE
    intro t ht
    have hut : 0 < u*t := mul_pos hu ht.1
    have hup : u*t ≤ Real.pi := by
      have htE : t ≤ Real.pi/u := ht.2.le.trans hEp
      have := mul_le_mul_of_nonneg_left htE hu.le
      have he : u*(Real.pi/u)=Real.pi := by field_simp
      rwa [he] at this
    have hc : Real.cos (u*t) < 1 := by
      simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) hup hut
    dsimp [cgProfile,cgNumerator]
    simp only [zero_mul,Real.cosh_zero,mul_one]
    exact div_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr hc)) ht.1
  have h1 : 0 ≤ ∫ t in E..T, cgProfile u 0 a t :=
    intervalIntegral.integral_nonneg hET (fun t ht => cgZeroHyperbolic_profile_nonneg (hE.le.trans ht.1))
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((cgProfile_continuous u 0 a).intervalIntegrable 0 E)
    ((cgProfile_continuous u 0 a).intervalIntegrable E T)
  change 0 < ∫ t in 0..T, cgProfile u 0 a t
  rw [← hi]
  exact add_pos_of_pos_of_nonneg h0 h1

theorem liClockCoshCosCutoff_pos {u v a T : ℝ}
    (hv : 0 ≤ v) (huv : v ≤ u) (hu : 0 < u)
    (ha : v ≤ a) (hT : 0 < T) :
    0 < liClockCoshCosCutoff u v a T := by
  rcases eq_or_lt_of_le hv with h | h
  · subst v
    exact cgZeroHyperbolic_pos hu hT
  · exact cgPositiveHyperbolic_pos h huv ha hT

end
end RHTower
