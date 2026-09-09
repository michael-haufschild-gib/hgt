import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalRiemannKernel
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial evaluation of the original causal BM source and its Einstein-current factor

The actual Legendre kernel transfers the original source's angular factor onto
explicit cubic radial weights. Both endpoints of the first adjoint flux vanish.
A second transfer evaluates the angular operator in the Einstein horizon current
and retains its forced, explicitly evaluated AdS-origin circle term.

The source polynomial is identified with the corpus's original mixed-source
remainder. All integral and endpoint identities are proved for the actual kernel,
with arbitrary complex source rate and angular degree. The full angular circle
construction, physical causal admission, complete tensor pairing and extinction
remain separate obligations.
-/

namespace RHTower.D4BMCausalSourceKernel
open Complex Set Filter Topology
open D4BMCausalKernel D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

abbrev Delay := {E : ℝ // 1 < E}
def slope (E : Delay) (image : Bool) : ℝ := if image then E.val+1 else E.val-1
def other (E : Delay) (image : Bool) : ℝ := if image then E.val-1 else E.val+1
def upper (E : Delay) (image : Bool) : ℝ := if image then (E.val-1)/(E.val+1) else 1
def argument (E : Delay) (image : Bool) (u : ℝ) : ℝ := E.val-slope E image*u
def ratio (E : Delay) (image : Bool) : ℂ := (other E image : ℂ)/(slope E image : ℂ)
def metricCoeff (E : Delay) (image : Bool) (u : ℝ) : ℂ := (1-u)*(ratio E image-u)
def metricFirst (E : Delay) (image : Bool) (u : ℝ) : ℂ := 2*u-1-ratio E image

private theorem slope_pos (E : Delay) (image : Bool) : 0 < slope E image := by
  cases image <;> dsimp [slope] <;> linarith [E.property]

private theorem upper_bounds (E : Delay) (image : Bool) : 0 < upper E image ∧ upper E image ≤ 1 := by
  cases image
  · norm_num [upper]
  · dsimp [upper]
    have hp : 0 < E.val+1 := by linarith [E.property]
    constructor
    · exact div_pos (by linarith [E.property]) hp
    · apply (div_le_one hp).mpr
      linarith

private theorem argument_ge_one (E : Delay) (image : Bool) {u : ℝ} (hu : u ∈ Icc 0 (upper E image)) :
    1 ≤ argument E image u := by
  have hs := slope_pos E image
  have h := mul_le_mul_of_nonneg_left hu.2 hs.le
  cases image
  · dsimp [slope,upper,argument] at h ⊢
    nlinarith
  · dsimp [slope,upper,argument] at h ⊢
    have hn : E.val+1 ≠ 0 := by linarith [E.property]
    have he : (E.val+1)*((E.val-1)/(E.val+1))=E.val-1 := by field_simp
    rw [he] at h
    linarith

private theorem metric_geometry (E : Delay) (image : Bool) (u : ℝ) :
    (slope E image : ℂ)^2*metricCoeff E image u=(argument E image u : ℂ)^2-1 ∧
    -(slope E image : ℂ)*metricFirst E image u=2*(argument E image u : ℂ) := by
  have hn : (slope E image : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (slope_pos E image))
  simp only [metricCoeff,metricFirst,ratio,argument]
  push_cast
  cases image <;> dsimp [slope,other] at hn ⊢ <;> push_cast at hn ⊢ <;> constructor <;> field_simp [hn] <;> ring

private theorem metric_endpoint (E : Delay) (image : Bool) : metricCoeff E image (upper E image)=0 := by
  cases image
  · simp [metricCoeff,upper]
  · simp [metricCoeff,ratio,other,slope,upper]

private theorem metric_hasDerivAt (E : Delay) (image : Bool) (u : ℝ) :
    HasDerivAt (metricCoeff E image) (metricFirst E image u) u := by
  have hx := (hasDerivAt_id u).ofReal_comp
  apply ((hx.const_sub 1).mul (hx.const_sub (ratio E image))).congr_deriv
  simp only [metricFirst,id_eq,Complex.ofReal_one]
  ring

private theorem argument_hasDerivAt (E : Delay) (image : Bool) (u : ℝ) :
    HasDerivAt (argument E image) (-slope E image) u := by
  convert! ((hasDerivAt_id u).const_mul (slope E image)).const_sub E.val using 1
  simp

def branchKernel (nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ := legendreKernel nu (argument E image u)
def branchFirst (nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  -(slope E image : ℂ)*legendreKernelFirst nu (argument E image u)
def branchSecond (nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (slope E image : ℂ)^2*legendreKernelSecond nu (argument E image u)

private theorem branch_derivatives (nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    HasDerivAt (branchKernel nu E image) (branchFirst nu E image u) u ∧
    HasDerivAt (branchFirst nu E image) (branchSecond nu E image u) u := by
  have hz : 0 < argument E image u := lt_of_lt_of_le (by norm_num) (argument_ge_one E image hu)
  obtain ⟨h,h1⟩ := legendreKernel_derivatives nu hz
  have ha := argument_hasDerivAt E image u
  constructor
  · convert! h.scomp u ha using 1
    simp [branchFirst,Complex.real_smul]
  · convert! (h1.scomp u ha).const_mul (-(slope E image : ℂ)) using 1
    simp [branchSecond,Complex.real_smul]
    ring

private theorem branch_equation (nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    metricCoeff E image u*branchSecond nu E image u+
      metricFirst E image u*branchFirst nu E image u=nu*(nu+1)*branchKernel nu E image u := by
  have hz : 0 < argument E image u := lt_of_lt_of_le (by norm_num) (argument_ge_one E image hu)
  have he := legendreKernel_equation nu hz
  obtain ⟨hg,hg1⟩ := metric_geometry E image u
  dsimp [branchSecond,branchFirst,branchKernel]
  linear_combination he + legendreKernelSecond nu (argument E image u)*hg +
    legendreKernelFirst nu (argument E image u)*hg1

def weight (s : ℂ) (u : ℝ) : ℂ := (u:ℂ)^3*power (2*s) (1+u)
def weightFirst (s : ℂ) (u : ℝ) : ℂ :=
  3*(u:ℂ)^2*power (2*s) (1+u)+(u:ℂ)^3*powerFirst (2*s) (1+u)
def weightSecond (s : ℂ) (u : ℝ) : ℂ :=
  6*(u:ℂ)*power (2*s) (1+u)+6*(u:ℂ)^2*powerFirst (2*s) (1+u)+
    (u:ℂ)^3*powerSecond (2*s) (1+u)

private theorem weight_derivatives (s : ℂ) {u : ℝ} (hu : 0 < 1+u) :
    HasDerivAt (weight s) (weightFirst s u) u ∧
    HasDerivAt (weightFirst s) (weightSecond s u) u := by
  have hx := (hasDerivAt_id u).ofReal_comp
  obtain ⟨hp,hp1⟩ := power_derivatives (2*s) hu
  have ha := (hasDerivAt_id u).const_add 1
  have h := hp.scomp u ha
  have h1 := hp1.scomp u ha
  constructor
  · convert! (hx.pow 3).mul h using 1
    simp [weightFirst]
  · convert! (((hx.pow 2).const_mul 3).mul h).add ((hx.pow 3).mul h1) using 1
    simp [weightSecond]
    ring

def flux (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  weight s u*metricCoeff E image u*branchFirst nu E image u-
    weightFirst s u*metricCoeff E image u*branchKernel nu E image u

def transportedWeight (s : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  metricCoeff E image u*weightSecond s u+metricFirst E image u*weightFirst s u

private theorem flux_derivative (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    HasDerivAt (flux s nu E image)
      ((nu*(nu+1)*weight s u-transportedWeight s E image u)*branchKernel nu E image u) u := by
  obtain ⟨hk,hk1⟩ := branch_derivatives nu E image hu
  obtain ⟨hw,hw1⟩ := weight_derivatives s (by linarith [hu.1] : 0 < 1+u)
  have hm := metric_hasDerivAt E image u
  have hd := (((hw.mul hm).mul hk1).sub ((hw1.mul hm).mul hk))
  apply hd.congr_deriv
  have he := branch_equation nu E image hu
  dsimp [transportedWeight]
  linear_combination weight s u*he

private theorem flux_endpoints (s nu : ℂ) (E : Delay) (image : Bool) :
    flux s nu E image (upper E image)=0 ∧ flux s nu E image 0=0 := by
  constructor
  · simp [flux,metric_endpoint]
  · simp [flux,weight,weightFirst]


def sourceA (s : ℂ) : ℂ := (5*s^2+15*s+4)/4
def sourceK (s : ℂ) : ℂ := s*(s-1)/4
def sourceB (s : ℂ) : ℂ := (s+2)*(2*s+3)

def originalDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (u:ℂ)*power (2*s) (1+u)*(sourceA s+sourceK s*(u:ℂ)^2*(sourceB s-nu*(nu+1)/2))*
    branchKernel nu E image u

def adjointDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (((sourceA s)*(u:ℂ)+sourceK s*sourceB s*(u:ℂ)^3)*power (2*s) (1+u)-
    sourceK s/2*transportedWeight s E image u)*branchKernel nu E image u

private theorem power_continuousAt (s : ℂ) {u : ℝ} (hu : 0 < 1+u) :
    ContinuousAt (fun v : ℝ => power (2*s) (1+v)) u :=
  (power_derivatives (2*s) hu).1.continuousAt.comp
    (continuous_const.add continuous_id).continuousAt

private theorem transportedWeight_continuousAt (s : ℂ) (E : Delay) (image : Bool)
    {u : ℝ} (hu : 0 < 1+u) : ContinuousAt (transportedWeight s E image) u := by
  have hp := power_continuousAt s hu
  have hn : ((1+u:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  unfold transportedWeight weightFirst weightSecond metricCoeff metricFirst powerFirst powerSecond
  fun_prop (disch := first | assumption | exact pow_ne_zero 2 hn)

private theorem densities_continuousAt (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    ContinuousAt (originalDensity s nu E image) u ∧ ContinuousAt (adjointDensity s nu E image) u := by
  have hp := power_continuousAt s (show 0 < 1+u by linarith [hu.1])
  have ht := transportedWeight_continuousAt s E image (show 0 < 1+u by linarith [hu.1])
  have hk := (branch_derivatives nu E image hu).1.continuousAt
  constructor
  · unfold originalDensity
    fun_prop
  · unfold adjointDensity
    fun_prop

/-- The actual original source moment transfers its entire angular eigenvalue factor to radial
weights. Both physical endpoints vanish in the integration-by-parts flux. -/
theorem original_source_integral_eq_adjoint (s nu : ℂ) (E : Delay) (image : Bool) :
    (∫ u in (0:ℝ)..upper E image, originalDensity s nu E image u) =
      ∫ u in (0:ℝ)..upper E image, adjointDensity s nu E image u := by
  have hi0 : IntervalIntegrable (originalDensity s nu E image) MeasureTheory.volume 0 (upper E image) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (upper_bounds E image).1.le]
    intro u hu
    exact (densities_continuousAt s nu E image hu).1.continuousWithinAt
  have hi1 : IntervalIntegrable (adjointDensity s nu E image) MeasureTheory.volume 0 (upper E image) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (upper_bounds E image).1.le]
    intro u hu
    exact (densities_continuousAt s nu E image hu).2.continuousWithinAt
  let f : ℝ → ℂ := fun u =>
    (nu*(nu+1)*weight s u-transportedWeight s E image u)*branchKernel nu E image u
  have hi : IntervalIntegrable f MeasureTheory.volume 0 (upper E image) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (upper_bounds E image).1.le]
    intro u hu
    have hw := (weight_derivatives s (show 0 < 1+u by linarith [hu.1])).1.continuousAt
    have ht := transportedWeight_continuousAt s E image (show 0 < 1+u by linarith [hu.1])
    have hk := (branch_derivatives nu E image hu).1.continuousAt
    exact (((hw.const_mul (nu*(nu+1))).sub ht).mul hk).continuousWithinAt
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := flux s nu E image) (f' := f)
    (fun u hu => flux_derivative s nu E image
      ((uIcc_of_le (upper_bounds E image).1.le) ▸ hu)) hi
  rw [(flux_endpoints s nu E image).1,(flux_endpoints s nu E image).2,sub_self] at hf
  apply sub_eq_zero.mp
  rw [← intervalIntegral.integral_sub hi0 hi1]
  have hd : (fun u => originalDensity s nu E image u-adjointDensity s nu E image u) =
      fun u => (-sourceK s/2)*f u := by
    funext u
    dsimp [originalDensity,adjointDensity,weight,f]
    ring
  rw [hd,intervalIntegral.integral_const_mul,hf,mul_zero]

private def c0 (s D : ℂ) : ℂ := sourceA s-3*sourceK s*D
private def c1 (s D : ℂ) : ℂ := 2*sourceA s+9*sourceK s/2-3*sourceK s*D*(4*s+1)/2
private def c2 (s D : ℂ) : ℂ := sourceA s+sourceK s*(2*s^2+14*s+9-D*(2*s^2-2*s-6))
private def c3 (s D : ℂ) : ℂ := sourceK s*(2*s+3)*(6*s+3+D*(2*s+3))/2

/-- Explicit cubic remaining after the original source coefficient cancels the fourth radial power. -/
def cubicPolynomial (s D u : ℂ) : ℂ := c0 s D+c1 s D*u+c2 s D*u^2+c3 s D*u^3
private def cubicFirst (s D u : ℂ) : ℂ := c1 s D+2*c2 s D*u+3*c3 s D*u^2
private def cubicSecond (s D u : ℂ) : ℂ := 2*c2 s D+6*c3 s D*u

def cubicDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (u:ℂ)*power (2*s) (1+u)/((1+u:ℝ):ℂ)^2*
    cubicPolynomial s (ratio E image) u*branchKernel nu E image u

/-- Pointwise evaluation of the transported source, with the physical rate left arbitrary. -/
theorem adjointDensity_eq_cubic (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : 0 < 1+u) : adjointDensity s nu E image u=cubicDensity s nu E image u := by
  have hn : (1:ℂ)+u ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  dsimp [adjointDensity,cubicDensity,cubicPolynomial,transportedWeight,weightFirst,weightSecond,
    powerFirst,powerSecond,metricCoeff,metricFirst,c0,c1,c2,c3,sourceA,sourceK,sourceB]
  push_cast
  field_simp [hn]
  ring

/-- The complete direct or reflected source integral is exactly the explicit cubic-weight integral.
No angular denominator, unevaluated integration-by-parts flux, or endpoint hypothesis remains. -/
theorem original_source_integral_eq_cubic (s nu : ℂ) (E : Delay) (image : Bool) :
    (∫ u in (0:ℝ)..upper E image, originalDensity s nu E image u) =
      ∫ u in (0:ℝ)..upper E image, cubicDensity s nu E image u := by
  rw [original_source_integral_eq_adjoint]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (upper_bounds E image).1.le] at hu
  exact adjointDensity_eq_cubic s nu E image (by linarith [hu.1])


private theorem cubic_derivatives (s D : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => cubicPolynomial s D v) (cubicFirst s D u) u ∧
    HasDerivAt (fun v : ℝ => cubicFirst s D v) (cubicSecond s D u) u := by
  have hx := (hasDerivAt_id u).ofReal_comp
  constructor
  · convert! (((hx.const_mul (c1 s D)).const_add (c0 s D)).add
      ((hx.pow 2).const_mul (c2 s D))).add ((hx.pow 3).const_mul (c3 s D)) using 1
    simp [cubicFirst]
    ring
  · convert! ((hx.const_mul (2*c2 s D)).const_add (c1 s D)).add
      ((hx.pow 2).const_mul (3*c3 s D)) using 1
    simp [cubicSecond]
    ring

def cubicWeight (s : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (u:ℂ)*power (2*s-2) (1+u)*cubicPolynomial s (ratio E image) u
private def cubicWeightFirst (s : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  power (2*s-2) (1+u)*cubicPolynomial s (ratio E image) u+
    (u:ℂ)*powerFirst (2*s-2) (1+u)*cubicPolynomial s (ratio E image) u+
    (u:ℂ)*power (2*s-2) (1+u)*cubicFirst s (ratio E image) u
private def cubicWeightSecond (s : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  2*powerFirst (2*s-2) (1+u)*cubicPolynomial s (ratio E image) u+
    (u:ℂ)*powerSecond (2*s-2) (1+u)*cubicPolynomial s (ratio E image) u+
    2*power (2*s-2) (1+u)*cubicFirst s (ratio E image) u+
    2*(u:ℂ)*powerFirst (2*s-2) (1+u)*cubicFirst s (ratio E image) u+
    (u:ℂ)*power (2*s-2) (1+u)*cubicSecond s (ratio E image) u

private theorem cubicWeight_derivatives (s : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : 0 < 1+u) :
    HasDerivAt (cubicWeight s E image) (cubicWeightFirst s E image u) u ∧
    HasDerivAt (cubicWeightFirst s E image) (cubicWeightSecond s E image u) u := by
  have hx := (hasDerivAt_id u).ofReal_comp
  obtain ⟨h,h1⟩ := power_derivatives (2*s-2) hu
  have ha := (hasDerivAt_id u).const_add 1
  have hp := h.scomp u ha
  have hp1 := h1.scomp u ha
  obtain ⟨hc,hc1⟩ := cubic_derivatives s (ratio E image) u
  constructor
  · apply ((hx.mul hp).mul hc).congr_deriv
    simp [cubicWeightFirst]
    ring
  · apply (((hp.mul hc).add ((hx.mul hp1).mul hc)).add ((hx.mul hp).mul hc1)).congr_deriv
    simp [cubicWeightSecond]
    ring

private theorem cubicDensity_weight (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : 0 < 1+u) :
    cubicDensity s nu E image u=cubicWeight s E image u*branchKernel nu E image u := by
  have hn : ((1+u:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  simp only [cubicDensity,cubicWeight,power,Complex.cpow_sub _ _ hn,Complex.cpow_two]
  ring

private def actionFlux (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  cubicWeight s E image u*metricCoeff E image u*branchFirst nu E image u-
    cubicWeightFirst s E image u*metricCoeff E image u*branchKernel nu E image u

/-- Radial density evaluating the angular factor in the Einstein horizon current. -/
def actionDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (metricCoeff E image u*cubicWeightSecond s E image u+
    metricFirst E image u*cubicWeightFirst s E image u-2*cubicWeight s E image u)*
      branchKernel nu E image u

private theorem actionFlux_derivative (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    HasDerivAt (actionFlux s nu E image)
      ((nu*(nu+1)-2)*cubicDensity s nu E image u-actionDensity s nu E image u) u := by
  obtain ⟨hk,hk1⟩ := branch_derivatives nu E image hu
  obtain ⟨hw,hw1⟩ := cubicWeight_derivatives s E image (by linarith [hu.1] : 0 < 1+u)
  have hm := metric_hasDerivAt E image u
  apply (((hw.mul hm).mul hk1).sub ((hw1.mul hm).mul hk)).congr_deriv
  rw [cubicDensity_weight s nu E image (by linarith [hu.1])]
  have he := branch_equation nu E image hu
  dsimp [actionDensity]
  linear_combination cubicWeight s E image u*he

private theorem actionFlux_endpoints (s nu : ℂ) (E : Delay) (image : Bool) :
    actionFlux s nu E image (upper E image)=0 ∧
    actionFlux s nu E image 0= -ratio E image*c0 s (ratio E image)*legendreKernel nu E.val := by
  constructor
  · simp [actionFlux,metric_endpoint]
  · simp only [actionFlux,cubicWeight,cubicWeightFirst,cubicPolynomial,power,metricCoeff,branchKernel,argument]
    norm_num
    ring_nf
    simp

private theorem actionDensity_continuousAt (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) : ContinuousAt (actionDensity s nu E image) u := by
  have hp : ContinuousAt (fun v : ℝ => power (2*s-2) (1+v)) u :=
    (power_derivatives (2*s-2) (show 0 < 1+u by linarith [hu.1])).1.continuousAt.comp
      (continuous_const.add continuous_id).continuousAt
  have hn : ((1+u:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hu.1])
  have hk := (branch_derivatives nu E image hu).1.continuousAt
  unfold actionDensity cubicWeightSecond cubicWeightFirst cubicWeight metricCoeff metricFirst
    cubicPolynomial cubicFirst cubicSecond powerFirst powerSecond
  fun_prop (disch := first | assumption | exact pow_ne_zero 2 hn)

/-- The angular factor in the actual Einstein current is a radial integral plus its forced
AdS-origin circle value; the latter is evaluated, not discarded. -/
private theorem cubic_integral_action (s nu : ℂ) (E : Delay) (image : Bool) :
    (nu*(nu+1)-2)*(∫ u in (0:ℝ)..upper E image, cubicDensity s nu E image u) =
      ratio E image*c0 s (ratio E image)*legendreKernel nu E.val+
        ∫ u in (0:ℝ)..upper E image, actionDensity s nu E image u := by
  have hi0 : IntervalIntegrable (cubicDensity s nu E image) MeasureTheory.volume 0 (upper E image) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (upper_bounds E image).1.le]
    intro u hu
    have hw := (cubicWeight_derivatives s E image (show 0 < 1+u by linarith [hu.1])).1.continuousAt
    have hk := (branch_derivatives nu E image hu).1.continuousAt
    have he : cubicDensity s nu E image =ᶠ[𝓝 u] fun v => cubicWeight s E image v*branchKernel nu E image v := by
      filter_upwards [lt_mem_nhds (show -1 < u by linarith [hu.1])] with v hv
      exact cubicDensity_weight s nu E image (by linarith)
    exact ((hw.mul hk).congr_of_eventuallyEq he).continuousWithinAt
  have hi1 : IntervalIntegrable (actionDensity s nu E image) MeasureTheory.volume 0 (upper E image) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (upper_bounds E image).1.le]
    intro u hu
    exact (actionDensity_continuousAt s nu E image hu).continuousWithinAt
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => actionFlux_derivative s nu E image
      ((uIcc_of_le (upper_bounds E image).1.le) ▸ hu))
    ((hi0.const_mul (nu*(nu+1)-2)).sub hi1)
  rw [intervalIntegral.integral_sub (hi0.const_mul _) hi1,intervalIntegral.integral_const_mul,
    (actionFlux_endpoints s nu E image).1,(actionFlux_endpoints s nu E image).2] at hf
  linear_combination hf

/-- Full direct-minus-image horizon kernel of the original scalar potential source. -/
def sourceKernel (s nu a : ℂ) (E : Delay) : ℂ :=
  -a^2*(∫ u in (0:ℝ)..upper E false, originalDensity s nu E false u)+
    a^2*(∫ u in (0:ℝ)..upper E true, originalDensity s nu E true u)

/-- Explicit circle coefficient forced by the two AdS-origin radial jets. -/
def circleCoefficient (s a : ℂ) (E : Delay) : ℂ :=
  -4*a^2*(E.val:ℂ)/((E.val:ℂ)^2-1)*
    (sourceA s-6*sourceK s*((E.val:ℂ)^2+1)/((E.val:ℂ)^2-1))

private theorem circleCoefficient_eq (s a : ℂ) (E : Delay) :
    circleCoefficient s a E = a^2*(ratio E true*c0 s (ratio E true)-ratio E false*c0 s (ratio E false)) := by
  have hp : (E.val:ℂ)+1 ≠ 0 := by exact_mod_cast (show E.val+1 ≠ 0 by linarith [E.property])
  have hm : (E.val:ℂ)-1 ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < E.val-1 by linarith [E.property]))
  have hq : (E.val:ℂ)^2-1 ≠ 0 := by
    rw [show (E.val:ℂ)^2-1=((E.val:ℂ)-1)*((E.val:ℂ)+1) by ring]
    exact mul_ne_zero hm hp
  simp only [circleCoefficient,ratio,other,slope,c0,Bool.false_eq_true,ite_false,ite_true]
  push_cast
  field_simp [hp,hm,hq]
  ring

/-- Complete angular-action evaluation for the original direct/image source kernel. Every
radial endpoint is fixed by the causal domain, with the nonzero circle term retained. -/
theorem sourceKernel_action (s nu a : ℂ) (E : Delay) :
    (nu*(nu+1)-2)*sourceKernel s nu a E =
      -a^2*(∫ u in (0:ℝ)..upper E false, actionDensity s nu E false u)+
        a^2*(∫ u in (0:ℝ)..upper E true, actionDensity s nu E true u)+
        circleCoefficient s a E*legendreKernel nu E.val := by
  simp only [sourceKernel,original_source_integral_eq_cubic,circleCoefficient_eq]
  linear_combination -a^2*cubic_integral_action s nu E false+a^2*cubic_integral_action s nu E true


/-- The kernel's source polynomial is the corpus's original mixed-source remainder, with its
full angular coefficient represented by the actual Legendre eigenvalue. -/
theorem originalDensity_sourceRemainder (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : 0 ≤ u) :
    originalDensity s nu E image u = (u:ℂ)*
      sourceRemainder s 0 1 1 (nu*(nu+1)/2-(s+1)*(s+2)) 1 (1-u^2)*
        branchKernel nu E image u := by
  simp only [originalDensity,sourceRemainder,sub_sub_cancel,Real.sqrt_sq hu,
    mul_one,one_pow,sub_zero]
  dsimp [sourceA,sourceK,sourceB]
  push_cast
  ring

end
end RHTower.D4BMCausalSourceKernel
