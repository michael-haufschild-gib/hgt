import Mathlib.Analysis.MellinTransform
import GaloisForLFunctions.HTGeometry.InfiniteProductFiniteHead
import GaloisForLFunctions.HTGeometry.IntervalUnitProbability
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.HTGeometry.InfiniteProductNonvanishing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The box factors of the smooth prime midpoint

Uniform logarithmic dilations have normalized hyperbolic-sine transforms.
The dyadic box factors have a summable quadratic departure from one, and
none can vanish in the right half-plane. The three signed endpoints leave
every open-strip frequency visible.
-/

noncomputable section
open Complex Filter Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Transform of a uniform logarithmic displacement of radius one. -/
def midpointBoxFactor : ℂ → ℂ := dslope Complex.sinh 0

private theorem box_value {z : ℂ} (hz : z ≠ 0) : midpointBoxFactor z=Complex.sinh z/z := by
  simp only [midpointBoxFactor,dslope_of_ne _ hz,slope_def_field,Complex.sinh_zero,sub_zero]

private theorem box_zero : midpointBoxFactor 0=1 := by
  rw [midpointBoxFactor,dslope_same,(Complex.hasDerivAt_sinh 0).deriv,Complex.cosh_zero]

theorem differentiable_midpoint_box_factor : Differentiable ℂ midpointBoxFactor :=
  differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
    Complex.differentiable_sinh.differentiableOn)

private theorem box_ne_zero {z : ℂ} (hz : 0 < z.re) : midpointBoxFactor z ≠ 0 := by
  have hz' : z ≠ 0 := fun h => by simp only [h,zero_re,lt_self_iff_false] at hz
  rw [box_value hz']
  apply div_ne_zero _ hz'
  intro h
  have he : Complex.exp z=Complex.exp (-z) := by
    have := (div_eq_zero_iff.mp h).resolve_right (by norm_num)
    exact sub_eq_zero.mp this
  have hh := congrArg norm he
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at hh
  linarith only [Real.exp_injective hh,hz]

/-- Every box factor agrees with one to second order uniformly on the unit disk. -/
theorem midpoint_box_quadratic {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖midpointBoxFactor z-1‖ ≤ ‖z‖^2 := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [box_zero]
  have ht (w : ℂ) (hw : ‖w‖ ≤ 1) :
      ‖Complex.exp w-(1+w+w^2/2)‖ ≤ ‖w‖^3/3 := by
    have h := Complex.exp_bound' (x:=w) (n:=3) (by norm_num; linarith only [hw])
    norm_num [sum_range_succ,Nat.factorial] at h
    convert h using 1
    ring
  have h1 := ht z hz
  have h2 := ht (-z) (by simpa only [norm_neg] using hz)
  rw [norm_neg] at h2
  have hh := norm_sub_le (Complex.exp z-(1+z+z^2/2)) (Complex.exp (-z)-(1+(-z)+(-z)^2/2))
  have hform : Complex.exp z-(1+z+z^2/2)-(Complex.exp (-z)-(1+(-z)+(-z)^2/2))=
      2*(Complex.sinh z-z) := by rw [Complex.sinh]; ring
  rw [hform,norm_mul,show ‖(2:ℂ)‖=2 by norm_num] at hh
  rw [box_value hz0,show Complex.sinh z/z-1=(Complex.sinh z-z)/z by field_simp,
    norm_div,div_le_iff₀ (norm_pos_iff.mpr hz0)]
  linarith only [hh,h1,h2,pow_nonneg (norm_nonneg z) 3]

private def boxRadius (j : ℕ) : ℝ := (1/2:ℝ)^(j+1)

private theorem norm_box_argument (j : ℕ) (z : ℂ) :
    ‖(boxRadius j:ℂ)*z‖=boxRadius j*‖z‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by dsimp [boxRadius]; positivity)]

/-- Product of the transforms of the independent dyadic log dilations. -/
def dyadicMidpointMultiplier (z : ℂ) : ℂ := ∏' j : ℕ,midpointBoxFactor ((boxRadius j:ℂ)*z)

theorem dyadic_midpoint_box_summable (z : ℂ) :
    Summable fun j : ℕ => ‖midpointBoxFactor ((boxRadius j:ℂ)*z)-1‖ := by
  have hgeom := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have hs : Summable (fun j : ℕ => boxRadius j*‖z‖) :=
    ((summable_nat_add_iff (f:=fun j : ℕ => (1/2:ℝ)^j) 1).mpr hgeom).mul_right _
  apply hs.of_norm_bounded_eventually_nat
  have hsmall := hs.tendsto_atTop_zero.eventually_lt_const (by norm_num : (0:ℝ)<1)
  filter_upwards [hsmall] with j hj
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have h := midpoint_box_quadratic (z:=(boxRadius j:ℂ)*z)
    (by rw [norm_box_argument]; exact hj.le)
  rw [norm_box_argument,pow_two] at h
  exact h.trans (mul_le_of_le_one_right (by dsimp [boxRadius]; positivity) hj.le)

/-- The dyadic smoothing preserves every frequency with positive real part. -/
theorem dyadic_midpoint_multiplier_ne_zero {z : ℂ} (hz : 0 < z.re) :
    dyadicMidpointMultiplier z ≠ 0 := by
  have hn (j : ℕ) : midpointBoxFactor ((boxRadius j:ℂ)*z) ≠ 0 := by
    apply box_ne_zero
    rw [Complex.re_ofReal_mul]
    exact mul_pos (by dsimp [boxRadius]; positivity) hz
  have hshift (x : ℂ) : 1+(x-1)=x := by ring
  have h := GaloisForLFunctions.HTGeometry.tprod_one_add_ne_zero_of_summable
    (dyadic_midpoint_box_summable z) (fun j => by simpa only [hshift] using hn j)
  simpa only [dyadicMidpointMultiplier,hshift] using h

/-- The signed three-endpoint transform with log smoothing of total radius log(65/64). -/
def smoothPrimeMidpointMultiplier (z : ℂ) : ℂ :=
  ((((15/4:ℝ):ℂ)^z-2*(3:ℂ)^z+((9/4:ℝ):ℂ)^z)/z)*
    dyadicMidpointMultiplier ((Real.log (65/64):ℂ)*z)

theorem smooth_prime_midpoint_multiplier_one : smoothPrimeMidpointMultiplier 1=0 := by
  norm_num [smoothPrimeMidpointMultiplier,Complex.ofReal_div]

theorem smooth_prime_midpoint_multiplier_ne_zero {z : ℂ} (hz : 0 < z.re) (h1 : z.re < 1) :
    smoothPrimeMidpointMultiplier z ≠ 0 := by
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 65/64)
  apply mul_ne_zero _ (dyadic_midpoint_multiplier_ne_zero (by simpa only [Complex.re_ofReal_mul] using mul_pos hlog hz))
  apply div_ne_zero _ (fun he => by simp only [he,zero_re,lt_self_iff_false] at hz)
  intro he
  have hm := (Real.strictConcaveOn_rpow hz h1).2
    (show (9/4:ℝ) ∈ Set.Ici 0 by norm_num) (show (15/4:ℝ) ∈ Set.Ici 0 by norm_num)
    (by norm_num : (9/4:ℝ) ≠ 15/4) (by norm_num : 0 < (1/2:ℝ)) (by norm_num : 0 < (1/2:ℝ))
    (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul,show (1/2:ℝ)*(9/4)+1/2*(15/4)=3 by norm_num] at hm
  have hh : ((15/4:ℝ):ℂ)^z+((9/4:ℝ):ℂ)^z=2*(3:ℂ)^z := by linear_combination he
  have ht := norm_add_le (((15/4:ℝ):ℂ)^z) (((9/4:ℝ):ℂ)^z)
  rw [hh,norm_mul,show ‖(2:ℂ)‖=2 by norm_num,
    show ‖(3:ℂ)^z‖=(3:ℝ)^z.re from Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<3) z,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<15/4),
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<9/4)] at ht
  linarith only [ht,hm]

open MeasureTheory

/-- A box factor is the normalized integral over the actual logarithmic displacement. -/
theorem midpoint_box_integral (z : ℂ) :
    midpointBoxFactor z=(∫ t in (-1:ℝ)..1,Complex.exp (z*t))/2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [box_zero]
    <;> norm_num
  rw [box_value hz,integral_exp_mul_complex hz]
  simp only [Complex.ofReal_one,Complex.ofReal_neg,mul_neg,mul_one,Complex.sinh]
  ring

private theorem norm_sinh_realpart (z : ℂ) : ‖Complex.sinh z‖≤Real.exp |z.re| := by
  have he := norm_sub_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at he
  rw [Complex.sinh,norm_div,show ‖(2:ℂ)‖=2 by norm_num]
  linarith only [he,Real.exp_le_exp.mpr (le_abs_self z.re),Real.exp_le_exp.mpr (neg_le_abs z.re)]

private theorem box_norm_realpart (z : ℂ) : ‖midpointBoxFactor z‖ ≤ Real.exp |z.re| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=(-1:ℝ)) (b:=1)
    (C:=Real.exp |z.re|) (f:=fun t : ℝ => Complex.exp (z*t)) (fun t ht => by
      rw [Set.uIoc_of_le (by norm_num : (-1:ℝ)≤1)] at ht
      rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans
        (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨ht.1.le,ht.2⟩))))
  norm_num only [sub_neg_eq_add,one_add_one_eq_two,abs_ofNat] at h
  rw [midpoint_box_integral,norm_div,show ‖(2:ℂ)‖=2 by norm_num]
  linarith only [h]

private theorem box_radius_sum (N : ℕ) : (∑ j ∈ range N,boxRadius j)=1-(1/2:ℝ)^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,ih,boxRadius,pow_succ]
    ring

private theorem multipliable_midpoint_boxes (z : ℂ) :
    Multipliable (fun j : ℕ => midpointBoxFactor ((boxRadius j:ℂ)*z)) := by
  have h := Complex.multipliable_one_add_of_summable (dyadic_midpoint_box_summable z).of_norm
  simpa only [show ∀ x : ℂ, 1+(x-1)=x from fun x => by ring] using h

/-- The dyadic multiplier gains any fixed number of powers at vertical
infinity. The exponential factor depends only on the real part. -/
theorem dyadic_midpoint_vertical_decay (K : ℕ) (z : ℂ) :
    ‖z‖^K*‖dyadicMidpointMultiplier z‖ ≤ (∏ j ∈ range K,(boxRadius j)⁻¹)*Real.exp |z.re| := by
  let F := fun j : ℕ => midpointBoxFactor ((boxRadius j:ℂ)*z)
  let E := fun j : ℕ => Real.exp (boxRadius j*|z.re|)
  have hr (j : ℕ) : 0<boxRadius j := by dsimp only [boxRadius]; positivity
  have hre (j : ℕ) : |((boxRadius j:ℂ)*z).re|=boxRadius j*|z.re| := by
    rw [Complex.re_ofReal_mul,abs_mul,abs_of_pos (hr j)]
  have hF (j : ℕ) : ‖F j‖≤E j := (box_norm_realpart _).trans_eq (congrArg Real.exp (hre j))
  have hstrong (j : ℕ) : ‖z‖*‖F j‖ ≤ (boxRadius j)⁻¹*E j := by
    rcases eq_or_ne z 0 with rfl | hz
    · rw [norm_zero,zero_mul]; exact mul_nonneg (inv_nonneg.mpr (hr j).le) (Real.exp_pos _).le
    have harg := mul_ne_zero (Complex.ofReal_ne_zero.mpr (hr j).ne') hz
    rw [show ‖F j‖=‖Complex.sinh ((boxRadius j:ℂ)*z)‖/(boxRadius j*‖z‖) by
      rw [F,box_value harg,norm_div,norm_box_argument]]
    have hh := norm_sinh_realpart ((boxRadius j:ℂ)*z)
    rw [hre] at hh
    calc _ = (boxRadius j)⁻¹*‖Complex.sinh ((boxRadius j:ℂ)*z)‖ := by
               field_simp [(hr j).ne',norm_ne_zero_iff.mpr hz]
         _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (hr j).le)
  have hfinite (N : ℕ) : ‖z‖^K*‖∏ j ∈ range (K+N),F j‖ ≤
      (∏ j ∈ range K,(boxRadius j)⁻¹)*Real.exp |z.re| := by
    rw [norm_prod,prod_range_add,←mul_assoc]
    have heq : ‖z‖^K*(∏ j ∈ range K,‖F j‖)=∏ j ∈ range K,(‖z‖*‖F j‖) := by
      rw [prod_mul_distrib,prod_const,card_range]
    rw [heq]
    have head := prod_le_prod (s:=range K) (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun j _ => hstrong j)
    have tail := prod_le_prod (s:=range N) (fun j _ => norm_nonneg (F (K+j))) (fun j _ => hF (K+j))
    apply (mul_le_mul head tail (prod_nonneg fun _ _ => norm_nonneg _) (prod_nonneg fun j _ =>
      mul_nonneg (inv_nonneg.mpr (hr j).le) (Real.exp_pos _).le)).trans
    rw [prod_mul_distrib,mul_assoc,←prod_range_add]
    apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun j _ => inv_nonneg.mpr (hr j).le)
    change (∏ j ∈ range (K+N),Real.exp (boxRadius j*|z.re|))≤_
    rw [←Real.exp_sum,←sum_mul,box_radius_sum]
    exact Real.exp_le_exp.mpr (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self _ (by positivity)))
  have hlim := ((multipliable_midpoint_boxes z).tendsto_prod_tprod_nat.comp
    (tendsto_atTop_add_const_left atTop K tendsto_id)).norm.const_mul (‖z‖^K)
  exact le_of_tendsto' hlim hfinite

private def logBoxCoordinate (x : ℝ) : ℝ := 2*max 1 (min 2 x)-3

private theorem log_box_coordinate_bound (x : ℝ) : |logBoxCoordinate x|≤1 := by
  have hl := le_max_left (1:ℝ) (min 2 x)
  have hu : max 1 (min 2 x)≤2 := max_le (by norm_num) (min_le_left ..)
  rw [logBoxCoordinate,abs_le]
  constructor <;> linarith only [hl,hu]

/-- Independent coordinates, uniform on [1,2] before rescaling to [-1,1]. -/
private def logBoxLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => intervalUnitProbability)

private instance : IsProbabilityMeasure logBoxLaw := by unfold logBoxLaw; infer_instance

private def logBoxPartial (N : ℕ) (u : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range N,boxRadius j*logBoxCoordinate (u j)

/-- The normalized random logarithmic displacement lies in [-1,1]. -/
def midpointLogDisplacement (u : ℕ → ℝ) : ℝ :=
  ∑' j : ℕ,boxRadius j*logBoxCoordinate (u j)

private theorem log_box_summable (u : ℕ → ℝ) :
    Summable (fun j : ℕ => boxRadius j*logBoxCoordinate (u j)) := by
  have hb := (summable_nat_add_iff (f:=fun j : ℕ => (1/2:ℝ)^j) 1).mpr
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1))
  apply hb.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0≤boxRadius j by dsimp [boxRadius]; positivity)]
  exact mul_le_of_le_one_right (by dsimp [boxRadius]; positivity) (log_box_coordinate_bound _)

private theorem log_box_partial_bound (N : ℕ) (u : ℕ → ℝ) : |logBoxPartial N u|≤1 := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (g:=boxRadius) (fun j _ => ?_)).trans
  · rw [box_radius_sum]
    exact sub_le_self _ (by positivity)
  · rw [abs_mul,abs_of_nonneg (show 0≤boxRadius j by dsimp [boxRadius]; positivity)]
    exact mul_le_of_le_one_right (by dsimp [boxRadius]; positivity) (log_box_coordinate_bound _)

theorem midpoint_log_displacement_bound (u : ℕ → ℝ) : |midpointLogDisplacement u|≤1 :=
  le_of_tendsto' (continuous_abs.continuousAt.tendsto.comp (log_box_summable u).hasSum.tendsto_sum_nat)
    (fun N => log_box_partial_bound N u)

private theorem log_box_single_transform (z : ℂ) :
    (∫ x : ℝ,Complex.exp (z*(logBoxCoordinate x:ℂ)) ∂intervalUnitProbability)=midpointBoxFactor z := by
  rw [intervalUnitProbability,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
  let g := fun t : ℝ => Complex.exp (z*(t:ℂ))
  trans ∫ x in (1:ℝ)..2,g (2*x+(-3))
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
    simp only [g,logBoxCoordinate,min_eq_right hx.2,max_eq_right hx.1,sub_eq_add_neg]
  rw [intervalIntegral.integral_comp_mul_add g (by norm_num : (2:ℝ)≠0),midpoint_box_integral]
  norm_num only [mul_one,Real.reduceMul,Real.reduceNeg,Real.reduceAdd]
  simp only [g,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_ofNat,div_eq_mul_inv,mul_comm]

private theorem log_box_head_transform (N : ℕ) (z : ℂ) :
    (∫ u,Complex.exp (z*(logBoxPartial N u:ℂ)) ∂logBoxLaw)=
      ∏ j ∈ range N,midpointBoxFactor ((boxRadius j:ℂ)*z) := by
  let f := fun (j : Fin N) (x : ℝ) => Complex.exp (((boxRadius j:ℝ):ℂ)*z*(logBoxCoordinate x:ℂ))
  let F := fun x : Fin N → ℝ => ∏ j,f j (x j)
  have hm : Measurable F := by dsimp [F,f,logBoxCoordinate]; fun_prop
  have hpi : Measurable (HTGeometry.countableProductHead (α:=ℝ) N) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (i:ℕ))
  have he (u : ℕ → ℝ) : Complex.exp (z*(logBoxPartial N u:ℂ))=F (HTGeometry.countableProductHead N u) := by
    simp only [logBoxPartial,Nat.cast_ofNat,ofReal_sum,ofReal_mul,mul_sum,Complex.exp_sum,F,f,
      HTGeometry.countableProductHead,Fin.prod_univ_eq_prod_range]
    apply prod_congr rfl
    intro j _
    congr 1
    ring
  simp_rw [he]
  rw [←integral_map hpi.aemeasurable hm.aestronglyMeasurable,logBoxLaw,
    HTGeometry.map_countableProductHead_infinitePi]
  change (∫ x : Fin N → ℝ,∏ j,f j (x j) ∂(Measure.pi (fun _ : Fin N => intervalUnitProbability)))=_
  rw [integral_fintype_prod_eq_prod]
  simp only [f,log_box_single_transform,Fin.prod_univ_eq_prod_range]

/-- The transform of the actual infinite sum of uniform logarithmic dilations is
the dyadic product. Finite heads use product measure and the limit is dominated. -/
theorem midpoint_log_displacement_transform (z : ℂ) :
    (∫ u,Complex.exp (z*(midpointLogDisplacement u:ℂ)) ∂logBoxLaw)=dyadicMidpointMultiplier z := by
  let F := fun (N : ℕ) (u : ℕ → ℝ) => Complex.exp (z*(logBoxPartial N u:ℂ))
  have hlim := tendsto_integral_of_dominated_convergence (μ:=logBoxLaw) (F:=F)
    (f:=fun u => Complex.exp (z*(midpointLogDisplacement u:ℂ))) (fun _ => Real.exp |z.re|)
    (fun N => by dsimp [F,logBoxPartial,logBoxCoordinate]; fun_prop)
    (integrable_const _) (fun N => Eventually.of_forall (fun u => by
      rw [F,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      apply Real.exp_le_exp.mpr
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (log_box_partial_bound N u)))
    (Eventually.of_forall (fun u => Complex.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (log_box_summable u).hasSum.tendsto_sum_nat))))
  simp only [F,log_box_head_transform] at hlim
  exact tendsto_nhds_unique hlim (multipliable_midpoint_boxes z).tendsto_prod_tprod_nat

private def logDilation (u : ℕ → ℝ) : ℝ :=
  Real.exp (Real.log (65/64)*midpointLogDisplacement u)

private theorem measurable_log_dilation : Measurable logDilation := by
  have h : Measurable midpointLogDisplacement :=
    measurable_of_tendsto_metrizable (f:=logBoxPartial) (fun N => by dsimp [logBoxPartial,logBoxCoordinate]; fun_prop)
      (tendsto_pi_nhds.mpr fun u => (log_box_summable u).hasSum.tendsto_sum_nat)
  exact Real.measurable_exp.comp (measurable_const.mul h)

private theorem log_dilation_range (u : ℕ → ℝ) : 64/65 ≤ logDilation u ∧ logDilation u ≤ 65/64 := by
  have hu := abs_le.mp (midpoint_log_displacement_bound u)
  have hh := Real.log_nonneg (by norm_num : (1:ℝ)≤65/64)
  have hlo := Real.exp_le_exp.mpr (show -Real.log (65/64)≤Real.log (65/64)*midpointLogDisplacement u by
    linarith only [mul_le_mul_of_nonneg_left hu.1 hh])
  have hhi := Real.exp_le_exp.mpr (show Real.log (65/64)*midpointLogDisplacement u≤Real.log (65/64) by
    linarith only [mul_le_mul_of_nonneg_left hu.2 hh])
  rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<65/64)] at hlo
  rw [Real.exp_log (by norm_num : (0:ℝ)<65/64)] at hhi
  exact ⟨by convert hlo using 1 <;> norm_num,hhi⟩

private def dilationBox (a b : ℝ) (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  if x∈Set.Ioc (a*logDilation u) (b*logDilation u) then 1 else 0

private def midpointWindowAt (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  dilationBox 3 (15/4) u x-dilationBox (9/4) 3 u x

/-- Signed weight obtained by uniformly and independently dilating the three
endpoints in logarithmic scale. -/
def smoothPrimeMidpointWeight (x : ℝ) : ℝ := ∫ u,midpointWindowAt u x ∂logBoxLaw

private theorem dilation_box_support {a b : ℝ} (ha : 9/4≤a) (hb : b≤15/4) (u : ℕ → ℝ) :
    Set.Ioc (a*logDilation u) (b*logDilation u) ⊆ Set.Ioc (2:ℝ) 4 := by
  intro x hx
  have hd := Real.exp_pos (Real.log (65/64)*midpointLogDisplacement u)
  obtain ⟨hl,hu⟩ := log_dilation_range u
  constructor
  · exact (lt_of_lt_of_le (by norm_num : (2:ℝ)<(9/4)*(64/65))
      (mul_le_mul ha hl (by norm_num) (by linarith only [ha]))).trans hx.1
  · exact hx.2.trans ((mul_le_mul hb hu hd.le (by norm_num)).trans (by norm_num))

private theorem midpoint_window_zero {x : ℝ} (hx : x∉Set.Ioc (2:ℝ) 4) (u : ℕ → ℝ) :
    midpointWindowAt u x=0 := by
  have hz {a b : ℝ} (ha : 9/4≤a) (hb : b≤15/4) : dilationBox a b u x=0 :=
    if_neg (fun h => hx (dilation_box_support ha hb u h))
  rw [midpointWindowAt,hz (by norm_num) le_rfl,hz le_rfl (by norm_num),sub_zero]

theorem smooth_prime_midpoint_weight_support {x : ℝ} (hx : x∉Set.Ioc (2:ℝ) 4) :
    smoothPrimeMidpointWeight x=0 := by
  simp only [smoothPrimeMidpointWeight,midpoint_window_zero hx,integral_zero]

private theorem measurable_dilation_box (a b : ℝ) :
    Measurable (fun h : ℝ × (ℕ → ℝ) => dilationBox a b h.2 h.1) := by
  exact Measurable.ite ((measurableSet_lt (measurable_const.mul (measurable_log_dilation.comp measurable_snd))
    measurable_fst).inter (measurableSet_le measurable_fst
    (measurable_const.mul (measurable_log_dilation.comp measurable_snd)))) measurable_const measurable_const

private theorem midpoint_window_bound (u : ℕ → ℝ) (x : ℝ) : |midpointWindowAt u x|≤2 := by
  unfold midpointWindowAt dilationBox
  split_ifs <;> norm_num

private theorem dilated_box_integral {a b : ℝ} (ha : 9/4≤a) (hab : a≤b) (hb : b≤15/4)
    {z : ℂ} (hz : z≠0) (u : ℕ → ℝ) :
    (∫ x : ℝ in Set.Ioc 2 4,(x:ℂ)^(z-1)*(dilationBox a b u x:ℂ))=
      ((b:ℂ)^z-(a:ℂ)^z)/z * Complex.exp (((Real.log (65/64):ℂ)*z)*(midpointLogDisplacement u:ℂ)) := by
  let d := logDilation u
  have hd : 0<d := Real.exp_pos _
  have hl := mul_pos (by linarith only [ha] : 0<a) hd
  have hle := mul_le_mul_of_nonneg_right hab hd.le
  let S := Set.Ioc (a*d) (b*d)
  have pt (x : ℝ) : (x:ℂ)^(z-1)*(dilationBox a b u x:ℂ)=S.indicator (fun x : ℝ => (x:ℂ)^(z-1)) x := by
    by_cases hx : x∈S <;> simp only [dilationBox,Set.indicator,S,d] at hx ⊢ <;> simp [hx]
  simp_rw [pt]
  rw [setIntegral_indicator measurableSet_Ioc,Set.inter_eq_right.mpr (dilation_box_support ha hb u),
    ←intervalIntegral.integral_of_le hle,integral_cpow (Or.inr ⟨by intro h; apply hz; linear_combination h,
      by rw [Set.uIcc_of_le hle]; exact fun h => hl.not_ge h.1⟩),sub_add_cancel]
  have hdz : ((d:ℂ)^z)=Complex.exp (((Real.log (65/64):ℂ)*z)*(midpointLogDisplacement u:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hd.ne'),←Complex.ofReal_log hd.le]
    simp only [d,logDilation,Real.log_exp,Complex.ofReal_mul]
    ring_nf
  rw [Complex.ofReal_mul,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by linarith only [ha,hab]) hd.le,
    Complex.mul_cpow_ofReal_nonneg (by linarith only [ha]) hd.le,hdz]
  ring

/-- Mellin transform of the smooth signed weight on the actual two intervals. -/
theorem mellin_smooth_prime_midpoint_weight {z : ℂ} (hz : z≠0) :
    mellin (fun x => (smoothPrimeMidpointWeight x:ℂ)) z=smoothPrimeMidpointMultiplier z := by
  let I := Set.Ioc (2:ℝ) 4
  let μ : Measure ℝ := volume.restrict I
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by simp [I,Real.volume_Ioc])
  let F := fun (x : ℝ) (u : ℕ → ℝ) => (x:ℂ)^(z-1)*(midpointWindowAt u x:ℂ)
  have hw : Measurable (fun h : ℝ × (ℕ → ℝ) => midpointWindowAt h.2 h.1) :=
    (measurable_dilation_box _ _).sub (measurable_dilation_box _ _)
  have hm : Measurable (Function.uncurry F) := by
    dsimp only [Function.uncurry,F]
    exact (by fun_prop : Measurable (fun h : ℝ × (ℕ → ℝ) => (h.1:ℂ)^(z-1))).mul
      (Complex.continuous_ofReal.measurable.comp hw)
  let B := Real.exp (Real.log 4*|(z-1).re|)
  have hpow {x : ℝ} (hx : x∈I) : ‖(x:ℂ)^(z-1)‖≤B := by
    have hx0 : 0<x := (by norm_num : (0:ℝ)<2).trans hx.1
    have hlog := Real.log_nonneg ((by norm_num : (1:ℝ)≤2).trans hx.1.le)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0,Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hlog).trans
      (mul_le_mul_of_nonneg_right (Real.log_le_log hx0 hx.2) (abs_nonneg _))
  have hi : Integrable (Function.uncurry F) (μ.prod logBoxLaw) := by
    apply (integrable_const (B*2)).mono' hm.aestronglyMeasurable
    apply Eventually.of_forall
    rintro ⟨x,u⟩
    by_cases hx : x∈I
    · rw [Function.uncurry,F,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (hpow hx) (midpoint_window_bound u x) (abs_nonneg _) (Real.exp_pos _).le
    · simp only [Function.uncurry,F,midpoint_window_zero hx,Complex.ofReal_zero,mul_zero,norm_zero]
      dsimp only [B]; positivity
  have inner (u : ℕ → ℝ) : (∫ x,F x u ∂μ)=
      ((((15/4:ℝ):ℂ)^z-2*(3:ℂ)^z+((9/4:ℝ):ℂ)^z)/z)*
        Complex.exp (((Real.log (65/64):ℂ)*z)*(midpointLogDisplacement u:ℂ)) := by
    have hInt (a b : ℝ) : Integrable (fun x : ℝ => (x:ℂ)^(z-1)*(dilationBox a b u x:ℂ)) μ := by
      have hh := (measurable_dilation_box a b).comp (measurable_id.prodMk measurable_const)
      apply (integrable_const B).mono' ((by fun_prop : Measurable (fun x : ℝ => (x:ℂ)^(z-1))).mul
        (Complex.continuous_ofReal.measurable.comp hh)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(2:ℝ)) (b:=4))] with x hx
      unfold dilationBox
      split_ifs <;> simpa only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,norm_zero] using
        (by first | exact hpow hx | exact (Real.exp_pos _).le)
    simp only [F,midpointWindowAt,Complex.ofReal_sub,mul_sub,integral_sub (hInt _ _) (hInt _ _)]
    rw [show μ=volume.restrict (Set.Ioc 2 4) by rfl,
      dilated_box_integral (by norm_num) (by norm_num) le_rfl hz,
      dilated_box_integral le_rfl (by norm_num) (by norm_num) hz]
    push_cast
    ring
  rw [mellin,setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (s:=I) (fun _ h => (by norm_num : (0:ℝ)<2).trans h.1)
    (fun _ h => by rw [smooth_prime_midpoint_weight_support h.2,Complex.ofReal_zero,smul_zero])]
  change (∫ x,(x:ℂ)^(z-1)*(smoothPrimeMidpointWeight x:ℂ) ∂μ)=_
  simp only [smoothPrimeMidpointWeight,←integral_complex_ofReal,←integral_const_mul]
  rw [integral_integral_swap (f:=F) hi]
  simp_rw [inner]
  rw [integral_const_mul,midpoint_log_displacement_transform]
  rfl

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
