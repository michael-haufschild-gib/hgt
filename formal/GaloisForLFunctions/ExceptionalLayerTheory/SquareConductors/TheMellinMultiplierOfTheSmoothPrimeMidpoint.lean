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

#print axioms midpoint_box_quadratic
#print axioms dyadic_midpoint_multiplier_ne_zero
#print axioms smooth_prime_midpoint_multiplier_one
#print axioms smooth_prime_midpoint_multiplier_ne_zero

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
