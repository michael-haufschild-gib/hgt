import GaloisForLFunctions.RHTower.EulerDeletionRemainderFirstCoefficient

/-!
# An exact nonnegative quartic correction of the ordinary arithmetic remainder

The centered Bernoulli kernel has a cubic periodic primitive. Its next primitive is
`fract(x)^2 * (1-fract(x))^2 / 24`, nonnegative and bounded by `1/384`.
Right-derivative integration identifies both primitives, and the continuous integral
representation supplies the full derivative at every integer join.

Integration by parts on the actual half-line remainder retains the integer and
infinite endpoints. It gives a quartic correction with two extra inverse powers
relative to the leading Bernoulli mean, without an assumed asymptotic estimate.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

private def bernoulliCubic (x : ℝ) : ℝ :=
  Int.fract x ^ 3 / 6 - Int.fract x ^ 2 / 4 + Int.fract x / 12

private theorem cubic_continuous : Continuous bernoulliCubic := by
  have hc : Continuous (fun x : ℝ => x^3/6-x^2/4+x/12) := by fun_prop
  exact hc.continuousOn.comp_fract'' (by norm_num)

private theorem cubic_right (x : ℝ) :
    HasDerivWithinAt bernoulliCubic (RHTower.bernoulliPeriodic x+1/12) (Ioi x) x := by
  have hf := tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  have he : bernoulliCubic =ᶠ[𝓝[≥] x]
      (fun y : ℝ => (y-(Int.floor x:ℝ))^3/6-(y-(Int.floor x:ℝ))^2/4+
        (y-(Int.floor x:ℝ))/12) := by
    filter_upwards [hf] with y hy
    simp only [bernoulliCubic,Int.fract,hy]
  have hi := (hasDerivAt_id x).sub_const (Int.floor x:ℝ)
  have hd : HasDerivAt
      (fun y : ℝ => (y-(Int.floor x:ℝ))^3/6-(y-(Int.floor x:ℝ))^2/4+
        (y-(Int.floor x:ℝ))/12) (RHTower.bernoulliPeriodic x+1/12) x := by
    convert! (((hi.pow 3).div_const 6).sub ((hi.pow 2).div_const 4)).add (hi.div_const 12) using 1
    simp only [Int.fract,RHTower.bernoulliPeriodic]
    norm_num
    ring
  exact (hd.hasDerivWithinAt.congr_of_eventuallyEq he rfl).mono Ioi_subset_Ici_self

/-- The centered periodic primitive is exactly the cubic Bernoulli polynomial. -/
theorem bernoulliCenteredPrimitive_eq_cubic (x : ℝ) :
    bernoulliCenteredPrimitive x =
      Int.fract x ^ 3 / 6 - Int.fract x ^ 2 / 4 + Int.fract x / 12 := by
  have hb : Continuous RHTower.bernoulliPeriodic := by
    have hc : Continuous (fun x : ℝ => (x^2-x)/2) := by fun_prop
    exact hc.continuousOn.comp_fract'' (by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (a:=0) (b:=x) cubic_continuous.continuousOn (fun y _ => cubic_right y)
    ((hb.add continuous_const).intervalIntegrable 0 x)
  change (∫ y in (0:ℝ)..x, RHTower.bernoulliPeriodic y+1/12) = _
  simpa [bernoulliCubic] using h

/-- A nonnegative periodic quartic primitive with zero integer endpoints. -/
def bernoulliQuarticPrimitive (x : ℝ) : ℝ :=
  Int.fract x ^ 2 * (1-Int.fract x)^2 / 24

private theorem quartic_continuous : Continuous bernoulliQuarticPrimitive := by
  have hc : Continuous (fun x : ℝ => x^2*(1-x)^2/24) := by fun_prop
  exact hc.continuousOn.comp_fract'' (by norm_num)

private theorem quartic_right (x : ℝ) :
    HasDerivWithinAt bernoulliQuarticPrimitive (bernoulliCubic x) (Ioi x) x := by
  have hf := tendsto_pure.mp (tendsto_floor_right_pure_floor x)
  have he : bernoulliQuarticPrimitive =ᶠ[𝓝[≥] x]
      (fun y : ℝ => (y-(Int.floor x:ℝ))^2*(1-(y-(Int.floor x:ℝ)))^2/24) := by
    filter_upwards [hf] with y hy
    simp only [bernoulliQuarticPrimitive,Int.fract,hy]
  have hi := (hasDerivAt_id x).sub_const (Int.floor x:ℝ)
  have hd : HasDerivAt
      (fun y : ℝ => (y-(Int.floor x:ℝ))^2*(1-(y-(Int.floor x:ℝ)))^2/24)
      (bernoulliCubic x) x := by
    convert! ((hi.pow 2).mul ((hi.const_sub 1).pow 2)).div_const 24 using 1
    simp only [bernoulliCubic,Int.fract]
    norm_num
    ring
  exact (hd.hasDerivWithinAt.congr_of_eventuallyEq he rfl).mono Ioi_subset_Ici_self

/-- The quartic has the centered primitive as its derivative even at integer joins. -/
theorem hasDerivAt_bernoulliQuarticPrimitive (x : ℝ) :
    HasDerivAt bernoulliQuarticPrimitive (bernoulliCenteredPrimitive x) x := by
  have he (y : ℝ) : (∫ z in (0:ℝ)..y, bernoulliCubic z) = bernoulliQuarticPrimitive y := by
    have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (a:=0) (b:=y) quartic_continuous.continuousOn (fun z _ => quartic_right z)
      (cubic_continuous.intervalIntegrable 0 y)
    simpa [bernoulliQuarticPrimitive] using h
  rw [bernoulliCenteredPrimitive_eq_cubic]
  change HasDerivAt bernoulliQuarticPrimitive (bernoulliCubic x) x
  have hfun : bernoulliQuarticPrimitive = fun y => ∫ z in (0:ℝ)..y, bernoulliCubic z :=
    funext (fun y => (he y).symm)
  rw [hfun]
  exact intervalIntegral.integral_hasDerivAt_right
    (cubic_continuous.intervalIntegrable 0 x)
    (cubic_continuous.stronglyMeasurableAtFilter _ _)
    cubic_continuous.continuousAt

/-- The sharp pointwise quartic bounds. -/
theorem bernoulliQuarticPrimitive_bounds (x : ℝ) :
    0 ≤ bernoulliQuarticPrimitive x ∧ bernoulliQuarticPrimitive x ≤ 1/384 := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  have ha : 0 ≤ Int.fract x*(1-Int.fract x) := mul_nonneg h0 (by linarith)
  have hb : Int.fract x*(1-Int.fract x) ≤ 1/4 := by nlinarith [sq_nonneg (Int.fract x-1/2)]
  dsimp [bernoulliQuarticPrimitive]
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr hb) (by positivity : 0 ≤ 1/4+Int.fract x*(1-Int.fract x))]

/-- Every integer endpoint of the quartic primitive is zero. -/
theorem bernoulliQuarticPrimitive_nat (N : ℕ) : bernoulliQuarticPrimitive N = 0 := by
  simp [bernoulliQuarticPrimitive]


private theorem integrable_bounded_cpow {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) {z : ℂ} (hz : z.re < -1)
    {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun x : ℝ => (f x : ℂ)*(x:ℂ)^z) (Ioi (N:ℝ)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hi := (integrableOn_Ioi_rpow_of_lt hz hNp).const_mul C
  apply Integrable.mono hi
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    apply ContinuousWithinAt.mul
    · exact (Complex.continuous_ofReal.comp hf).continuousAt.continuousWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (hNp.trans hx)) (by
        intro he; rw [he] at hz; norm_num at hz)).continuousAt.continuousWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hxp := hNp.trans hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hxp]
    simpa only [Pi.mul_apply, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (abs_nonneg (f 0)) (hb 0)),
      abs_of_nonneg (Real.rpow_nonneg hxp.le _)] using
      mul_le_mul_of_nonneg_right (hb x) (Real.rpow_nonneg hxp.le z.re)

/-- The complete quartic correction, integrated with its literal arithmetic kernel. -/
def quarticPrimitiveTail (N : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (N:ℝ), (bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-4)

/-- Absolute convergence of the quartic correction on the ordinary remainder half-plane. -/
theorem integrable_quarticPrimitiveTail {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    IntegrableOn (fun x : ℝ => (bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-4))
      (Ioi (N:ℝ)) := by
  apply integrable_bounded_cpow quartic_continuous (C:=1/384)
    (fun x => by simpa [abs_of_nonneg (bernoulliQuarticPrimitive_bounds x).1] using
      (bernoulliQuarticPrimitive_bounds x).2) ?_ hN
  simp; linarith

/-- The exact quartic bound supplies two additional inverse powers after normalization. -/
theorem norm_quarticPrimitiveTail_le {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    ‖quarticPrimitiveTail N s‖ ≤ (N:ℝ)^(-s.re-3)/(384*(s.re+3)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hre : -s.re-4 < -1 := by linarith
  have hi := (integrableOn_Ioi_rpow_of_lt hre hNp).const_mul (1/384:ℝ)
  have hb : ‖quarticPrimitiveTail N s‖ ≤
      ∫ x in Ioi (N:ℝ), (1/384:ℝ)*x^(-s.re-4) := by
    apply norm_integral_le_of_norm_le hi
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (bernoulliQuarticPrimitive_bounds x).1,
      Complex.norm_cpow_eq_rpow_re_of_pos (hNp.trans hx)]
    have he : (-s-4).re = -s.re-4 := by simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (bernoulliQuarticPrimitive_bounds x).2
      (Real.rpow_nonneg (hNp.trans hx).le _)
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hre hNp,
    show -s.re-4+1 = -(s.re+3) by ring, neg_div_neg_eq]
  rw [show -(s.re+3) = -s.re-3 by ring]
  field_simp

/-- Integration by parts from the cubic to the quartic retains both zero boundaries. -/
theorem centeredPrimitiveTail_eq_quartic {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    centeredPrimitiveTail N s = (s+3)*quarticPrimitiveTail N s := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hre : (-s-3).re < -1 := by simp; linarith
  have hrne : -s-3 ≠ 0 := by intro h; rw [h] at hre; norm_num at hre
  have hd (x : ℝ) (hx : 0<x) : HasDerivAt (fun y : ℝ => (y:ℂ)^(-s-3))
      ((-s-3)*(x:ℂ)^(-s-4)) x := by
    simpa only [show -s-3-1 = -s-4 by ring] using
      hasDerivAt_ofReal_cpow_const hx.ne' hrne
  have hpc : Continuous bernoulliCenteredPrimitive := by
    have he : bernoulliCenteredPrimitive=bernoulliCubic := by
      funext x; exact bernoulliCenteredPrimitive_eq_cubic x
    rw [he]; exact cubic_continuous
  have hi := integrable_bounded_cpow hpc abs_bernoulliCenteredPrimitive_le hre hN
  have hip := (integrable_quarticPrimitiveTail hs hN).const_mul (-s-3)
  have hprod0 : Tendsto (fun x : ℝ => (bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-3))
      (𝓝[>] (N:ℝ)) (𝓝 0) := by
    have hc := ((hasDerivAt_bernoulliQuarticPrimitive (N:ℝ)).ofReal_comp.mul (hd N hNp)).continuousAt
    simpa [bernoulliQuarticPrimitive_nat, Pi.mul_def] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprodt : Tendsto (fun x : ℝ => (bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-3))
      atTop (𝓝 0) := by
    have ht := tendsto_rpow_neg_atTop (by linarith : 0<s.re+3)
    rw [show -(s.re+3) = -s.re-3 by ring] at ht
    apply squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (bernoulliQuarticPrimitive_bounds x).1,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have he : (-s-3).re = -s.re-3 := by simp
    rw [he]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hx.le _)
      (le_trans (bernoulliQuarticPrimitive_bounds x).2 (by norm_num))
  have hb := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x:ℂ)^(-s-3))
    (u' := fun x : ℝ => (-s-3)*(x:ℂ)^(-s-4))
    (v := fun x : ℝ => (bernoulliQuarticPrimitive x:ℂ))
    (v' := fun x : ℝ => (bernoulliCenteredPrimitive x:ℂ))
    (a := (N:ℝ)) (a' := (0:ℂ)) (b' := (0:ℂ))
    (fun x hx => hd x (hNp.trans hx))
    (fun x _ => (hasDerivAt_bernoulliQuarticPrimitive x).ofReal_comp)
    (by simpa [Pi.mul_def, mul_comm] using hi)
    (by simpa [IntegrableOn, Pi.mul_def, mul_assoc, mul_left_comm, mul_comm] using hip)
    (by simpa [Pi.mul_def, mul_comm] using hprod0)
    (by simpa [Pi.mul_def, mul_comm] using hprodt)
  simp only [zero_sub, sub_zero] at hb
  calc
    _ = ∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-3)*(bernoulliCenteredPrimitive x:ℂ) := by
      apply integral_congr_ae; filter_upwards with x; ring
    _ = -(∫ x in Ioi (N:ℝ), ((-s-3)*(x:ℂ)^(-s-4))*(bernoulliQuarticPrimitive x:ℂ)) := hb
    _ = (s+3)*quarticPrimitiveTail N s := by
      rw [show (fun x : ℝ => ((-s-3)*(x:ℂ)^(-s-4))*(bernoulliQuarticPrimitive x:ℂ)) =
        (fun x : ℝ => (-s-3)*((bernoulliQuarticPrimitive x:ℂ)*(x:ℂ)^(-s-4))) by
          funext x; ring, integral_const_mul]
      dsimp [quarticPrimitiveTail]
      ring

/-- Exact Bernoulli mean and nonnegative quartic-kernel correction. -/
theorem bernoulliTail_eq_mean_add_quartic {s : ℂ} (hs : -1<s.re) {N : ℕ} (hN : 1≤N) :
    RHTower.zetaBernoulliTail N s = -(N:ℂ)^(-s-1)/(12*(s+1))+
      ((s+2)*(s+3))*quarticPrimitiveTail N s := by
  rw [bernoulliTail_eq_mean_add_primitive hs hN, centeredPrimitiveTail_eq_quartic hs hN]
  ring

/-- Exact quartic correction of the ordinary power-sum remainder. -/
theorem powerSumRemainder_eq_mean_add_quartic {s : ℂ} (hs : -1<s.re) (hs1 : s≠1)
    {N : ℕ} (hN : 1≤N) :
    powerSumRemainder s N = -s/12*(N:ℂ)^(-s-1)+
      (s*(s+1)*(s+2)*(s+3))*quarticPrimitiveTail N s := by
  rw [powerSumRemainder_eq_mean_add_primitive hs hs1 hN, centeredPrimitiveTail_eq_quartic hs hN]
  ring

end RHTower.DeletionMixedRefinement
