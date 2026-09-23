import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalRiemannKernel
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Radial evaluation of the original causal BM source and its Einstein-current factor

The actual Legendre kernel transfers the original source's angular factor onto
explicit cubic radial weights. Both endpoints of the first adjoint flux vanish.
A second transfer evaluates the angular operator in the Einstein horizon current
and evaluates its forced AdS-origin circle term. The actual constant and linear
Legendre solutions cancel that coefficient against the retained radial moments.
The remaining first-jet-subtracted kernel is its integral second Taylor remainder;
its radial displacement cancels the apparent square pole of the source weight.
An explicit numerator is jointly continuous even at zero direct slope.

The source polynomial is identified with the corpus's original mixed-source
remainder. All integral and endpoint identities are proved for the actual kernel,
with arbitrary complex source rate and angular degree. The full angular circle
construction, joint integral admission at zero delay, physical causal admission,
complete tensor pairing and extinction
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
    (slope E image : ℂ)^(2 : ℕ)*metricCoeff E image u=(argument E image u : ℂ)^(2 : ℕ)-1 ∧
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
  (slope E image : ℂ)^(2 : ℕ)*legendreKernelSecond nu (argument E image u)

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

def weight (s : ℂ) (u : ℝ) : ℂ := (u:ℂ)^(3 : ℕ)*power (2*s) (1+u)
def weightFirst (s : ℂ) (u : ℝ) : ℂ :=
  3*(u:ℂ)^(2 : ℕ)*power (2*s) (1+u)+(u:ℂ)^(3 : ℕ)*powerFirst (2*s) (1+u)
def weightSecond (s : ℂ) (u : ℝ) : ℂ :=
  6*(u:ℂ)*power (2*s) (1+u)+6*(u:ℂ)^(2 : ℕ)*powerFirst (2*s) (1+u)+
    (u:ℂ)^(3 : ℕ)*powerSecond (2*s) (1+u)

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


def sourceA (s : ℂ) : ℂ := (5*s^(2 : ℕ)+15*s+4)/4
def sourceK (s : ℂ) : ℂ := s*(s-1)/4
def sourceB (s : ℂ) : ℂ := (s+2)*(2*s+3)

def originalDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (u:ℂ)*power (2*s) (1+u)*(sourceA s+sourceK s*(u:ℂ)^(2 : ℕ)*(sourceB s-nu*(nu+1)/2))*
    branchKernel nu E image u

def adjointDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (((sourceA s)*(u:ℂ)+sourceK s*sourceB s*(u:ℂ)^(3 : ℕ))*power (2*s) (1+u)-
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
private def c2 (s D : ℂ) : ℂ := sourceA s+sourceK s*(2*s^(2 : ℕ)+14*s+9-D*(2*s^(2 : ℕ)-2*s-6))
private def c3 (s D : ℂ) : ℂ := sourceK s*(2*s+3)*(6*s+3+D*(2*s+3))/2

/-- Explicit cubic remaining after the original source coefficient cancels the fourth radial power. -/
def cubicPolynomial (s D u : ℂ) : ℂ := c0 s D+c1 s D*u+c2 s D*u^(2 : ℕ)+c3 s D*u^(3 : ℕ)
private def cubicFirst (s D u : ℂ) : ℂ := c1 s D+2*c2 s D*u+3*c3 s D*u^(2 : ℕ)
private def cubicSecond (s D u : ℂ) : ℂ := 2*c2 s D+6*c3 s D*u

def cubicDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  (u:ℂ)*power (2*s) (1+u)/((1+u:ℝ):ℂ)^(2 : ℕ)*
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
  -a^(2 : ℕ)*(∫ u in (0:ℝ)..upper E false, originalDensity s nu E false u)+
    a^(2 : ℕ)*(∫ u in (0:ℝ)..upper E true, originalDensity s nu E true u)

/-- Explicit circle coefficient forced by the two AdS-origin radial jets. -/
def circleCoefficient (s a : ℂ) (E : Delay) : ℂ :=
  -4*a^(2 : ℕ)*(E.val:ℂ)/((E.val:ℂ)^(2 : ℕ)-1)*
    (sourceA s-6*sourceK s*((E.val:ℂ)^(2 : ℕ)+1)/((E.val:ℂ)^(2 : ℕ)-1))

private theorem circleCoefficient_eq (s a : ℂ) (E : Delay) :
    circleCoefficient s a E = a^(2 : ℕ)*(ratio E true*c0 s (ratio E true)-ratio E false*c0 s (ratio E false)) := by
  have hp : (E.val:ℂ)+1 ≠ 0 := by exact_mod_cast (show E.val+1 ≠ 0 by linarith [E.property])
  have hm : (E.val:ℂ)-1 ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < E.val-1 by linarith [E.property]))
  have hq : (E.val:ℂ)^(2 : ℕ)-1 ≠ 0 := by
    rw [show (E.val:ℂ)^(2 : ℕ)-1=((E.val:ℂ)-1)*((E.val:ℂ)+1) by ring]
    exact mul_ne_zero hm hp
  simp only [circleCoefficient,ratio,other,slope,c0,Bool.false_eq_true,ite_false,ite_true]
  push_cast
  field_simp [hp,hm,hq]
  ring

/-- Complete angular-action evaluation for the original direct/image source kernel. Every
radial endpoint is fixed by the causal domain, with the nonzero circle term retained. -/
theorem sourceKernel_action (s nu a : ℂ) (E : Delay) :
    (nu*(nu+1)-2)*sourceKernel s nu a E =
      -a^(2 : ℕ)*(∫ u in (0:ℝ)..upper E false, actionDensity s nu E false u)+
        a^(2 : ℕ)*(∫ u in (0:ℝ)..upper E true, actionDensity s nu E true u)+
        circleCoefficient s a E*legendreKernel nu E.val := by
  simp only [sourceKernel,original_source_integral_eq_cubic,circleCoefficient_eq]
  linear_combination -a^(2 : ℕ)*cubic_integral_action s nu E false+a^(2 : ℕ)*cubic_integral_action s nu E true


/-- The kernel's source polynomial is the corpus's original mixed-source remainder, with its
full angular coefficient represented by the actual Legendre eigenvalue. -/
theorem originalDensity_sourceRemainder (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : 0 ≤ u) :
    originalDensity s nu E image u = (u:ℂ)*
      sourceRemainder s 0 1 1 (nu*(nu+1)/2-(s+1)*(s+2)) 1 (1-u^(2 : ℕ))*
        branchKernel nu E image u := by
  simp only [originalDensity,sourceRemainder,sub_sub_cancel,Real.sqrt_sq hu,
    mul_one,one_pow,sub_zero]
  dsimp [sourceA,sourceK,sourceB]
  push_cast
  ring

open scoped ContDiff
open GaloisForLFunctions.HTGeometry

private theorem gauss_zero (z : ℂ) : (ordinaryHypergeometricSeries ℂ (0:ℂ) 0 1).sum z=1 := by
  change (∑' n : ℕ, ordinaryHypergeometricSeries ℂ (0:ℂ) 0 1 n (fun _ => z))=1
  rw [tsum_eq_single 0]
  · rw [ordinaryHypergeometricSeries_apply_eq]
    norm_num
  · intro n hn
    have hz := ordinaryHypergeometricSeries_eq_zero_of_neg_nat (𝔸 := ℂ)
      (0:ℂ) 0 1 (k := 0) (Or.inl (by simp)) (Nat.pos_of_ne_zero hn)
    rw [hz]
    simp

private theorem gauss_one (z : ℂ) : (ordinaryHypergeometricSeries ℂ (-1:ℂ) (-1) 1).sum z=1+z := by
  change (∑' n : ℕ, ordinaryHypergeometricSeries ℂ (-1:ℂ) (-1) 1 n (fun _ => z))=1+z
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [ordinaryHypergeometricSeries_apply_eq]
    norm_num [ascPochhammer_succ_left]
  · intro n hn
    have hn2 : 1 < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have hz := ordinaryHypergeometricSeries_eq_zero_of_neg_nat (𝔸 := ℂ)
      (-1:ℂ) (-1) 1 (k := 1) (Or.inl (by simp)) hn2
    rw [hz]
    simp

/-- The constant Legendre kernel supplies the exact zeroth radial source moment. -/
theorem legendre_zero (z : ℝ) : legendreKernel 0 z=1 := by
  change power 0 ((z+1)/2)*(ordinaryHypergeometricSeries ℂ (-0) (-0) 1).sum (((z-1)/(z+1):ℝ):ℂ)=1
  simp only [neg_zero,gauss_zero,power,Complex.cpow_zero,mul_one]

/-- The linear Legendre kernel supplies the exact first radial source moment. -/
theorem legendre_one {z : ℝ} (hz : 0 < z) : legendreKernel 1 z=(z:ℂ) := by
  change power 1 ((z+1)/2)*(ordinaryHypergeometricSeries ℂ (-1:ℂ) (-1) 1).sum (((z-1)/(z+1):ℝ):ℂ)=(z:ℂ)
  rw [gauss_one]
  have hn : (z:ℂ)+1 ≠ 0 := by exact_mod_cast (show z+1 ≠ 0 by linarith)
  simp only [power,Complex.cpow_one]
  push_cast
  field_simp [hn]
  ring

private theorem power_contDiffAt (a : ℂ) {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ ∞ (power a) x := by
  have he : power a =ᶠ[𝓝 x] fun y : ℝ => Complex.exp (a*(Real.log y:ℂ)) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [power,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)),
      ← Complex.ofReal_log hy.le]
    congr 1
    ring
  have hn : x ≠ 0 := ne_of_gt hx
  have hh : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp (a*(Real.log y:ℂ))) x := by
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => (y:ℂ)) (Real.log x) := Complex.ofRealCLM.contDiff.contDiffAt
    have hl : ContDiffAt ℝ ∞ Real.log x := by fun_prop (disch := assumption)
    exact (contDiffAt_const.mul (hc.comp x hl)).cexp
  exact hh.congr_of_eventuallyEq he

/-- The actual positive-chart Riemann kernel is smooth, including at the characteristic value one. -/
theorem legendre_contDiffAt (nu : ℂ) {z : ℝ} (hz : 0 < z) : ContDiffAt ℝ ∞ (legendreKernel nu) z := by
  let p := ordinaryHypergeometricSeries ℂ (-nu) (-nu) 1
  have hrad : 1 ≤ p.radius := hypergeometric_radius_one_le _ _ _
  have hp : 0 < p.radius := lt_of_lt_of_le (by norm_num) hrad
  have hden : 0 < z+1 := by linarith
  have habs : |(z-1)/(z+1)| < 1 := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hden).mpr
      linarith
    · apply (div_lt_iff₀ hden).mpr
      linarith
  have hn : ‖(((z-1)/(z+1):ℝ):ℂ)‖ < 1 := by simpa only [Complex.norm_real,Real.norm_eq_abs] using habs
  have he : ‖(((z-1)/(z+1):ℝ):ℂ)‖ₑ < 1 := by
    rw [← ENNReal.coe_one,enorm_lt_coe]
    exact_mod_cast hn
  have ha := (p.hasFPowerSeriesOnBall hp).analyticAt_of_mem
    (show (((z-1)/(z+1):ℝ):ℂ) ∈ Metric.eball (0:ℂ) p.radius by
      simpa only [Metric.mem_eball,edist_zero_right] using he.trans_le hrad)
  have hs : ContDiffAt ℝ ∞ p.sum (((z-1)/(z+1):ℝ):ℂ) := ha.contDiffAt.restrict_scalars ℝ
  have hx : ContDiffAt ℝ ∞ (fun x : ℝ => (((x-1)/(x+1):ℝ):ℂ)) z := by
    have hc : ContDiffAt ℝ ∞ (fun y : ℝ => (y:ℂ)) ((z-1)/(z+1)) := Complex.ofRealCLM.contDiff.contDiffAt
    have hr : ContDiffAt ℝ ∞ (fun x : ℝ => (x-1)/(x+1)) z := by fun_prop (disch := linarith)
    exact hc.comp z hr
  have hf := power_contDiffAt nu (by linarith : 0 < (z+1)/2)
  change ContDiffAt ℝ ∞ (fun x : ℝ => power nu ((x+1)/2)*p.sum (((x-1)/(x+1):ℝ):ℂ)) z
  have hy : ContDiffAt ℝ ∞ (fun x : ℝ => (x+1)/2) z := by fun_prop
  exact (hf.comp z hy).mul (hs.comp z hx)

/-- The actual Legendre kernel with its constant and linear circle jets removed. -/
def circleRemainder (nu : ℂ) (E Z : ℝ) : ℂ :=
  legendreKernel nu Z-legendreKernel nu E-
    ((Z:ℂ)-(E:ℂ))*legendreKernelFirst nu E

/-- Source action density after removal of the first circle jet. -/
def actionRemainderDensity (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) : ℂ :=
  actionDensity s 0 E image u*circleRemainder nu E.val (argument E image u)

private theorem actionDensity_factor (s nu : ℂ) (E : Delay) (image : Bool) (u : ℝ) :
    actionDensity s nu E image u=actionDensity s 0 E image u*branchKernel nu E image u := by
  simp only [actionDensity,branchKernel,legendre_zero,mul_one]

private theorem actionRemainderDensity_eq (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    actionRemainderDensity s nu E image u = actionDensity s nu E image u+
      ((E.val:ℂ)*legendreKernelFirst nu E.val-legendreKernel nu E.val)*actionDensity s 0 E image u-
      legendreKernelFirst nu E.val*actionDensity s 1 E image u := by
  have hz : 0 < argument E image u := lt_of_lt_of_le (by norm_num) (argument_ge_one E image hu)
  rw [actionDensity_factor s nu, actionDensity_factor s 1]
  simp only [actionRemainderDensity,circleRemainder,branchKernel,legendre_one hz]
  ring

private theorem action_remainder_integral (s nu : ℂ) (E : Delay) (image : Bool) :
    (∫ u in (0:ℝ)..upper E image, actionRemainderDensity s nu E image u) =
      (∫ u in (0:ℝ)..upper E image, actionDensity s nu E image u)+
      ((E.val:ℂ)*legendreKernelFirst nu E.val-legendreKernel nu E.val)*
        (∫ u in (0:ℝ)..upper E image, actionDensity s 0 E image u)-
      legendreKernelFirst nu E.val*(∫ u in (0:ℝ)..upper E image, actionDensity s 1 E image u) := by
  have hi (v : ℂ) : IntervalIntegrable (actionDensity s v E image) MeasureTheory.volume 0 (upper E image) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (upper_bounds E image).1.le]
    exact fun u hu => (actionDensity_continuousAt s v E image hu).continuousWithinAt
  rw [intervalIntegral.integral_congr (fun u hu => actionRemainderDensity_eq s nu E image
    ((uIcc_of_le (upper_bounds E image).1.le) ▸ hu))]
  rw [intervalIntegral.integral_sub ((hi nu).add ((hi 0).const_mul _)) ((hi 1).const_mul _),
    intervalIntegral.integral_add (hi nu) ((hi 0).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

/-- The forced circle coefficient cancels exactly with the two actual radial moments.
The remainder is the first-jet-subtracted kernel inside both original causal integrals. -/
theorem sourceKernel_action_circle_cancel (s nu a : ℂ) (E : Delay) :
    (nu*(nu+1)-2)*sourceKernel s nu a E =
      2*sourceKernel s 0 a E*((E.val:ℂ)*legendreKernelFirst nu E.val-legendreKernel nu E.val)-
      a^(2 : ℕ)*(∫ u in (0:ℝ)..upper E false, actionRemainderDensity s nu E false u)+
      a^(2 : ℕ)*(∫ u in (0:ℝ)..upper E true, actionRemainderDensity s nu E true u) := by
  have h0 := sourceKernel_action s 0 a E
  have h1 := sourceKernel_action s 1 a E
  have hn := sourceKernel_action s nu a E
  simp only [legendre_zero,zero_add,zero_sub,mul_one] at h0
  rw [legendre_one (by linarith [E.property])] at h1
  norm_num at h1
  rw [action_remainder_integral,action_remainder_integral]
  linear_combination hn+
    ((E.val:ℂ)*legendreKernelFirst nu E.val-legendreKernel nu E.val)*h0-
    legendreKernelFirst nu E.val*h1

private theorem legendre_iteratedDeriv_two (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    iteratedDeriv 2 (legendreKernel nu) z=legendreKernelSecond nu z := by
  have he : deriv (legendreKernel nu) =ᶠ[𝓝 z] legendreKernelFirst nu := by
    filter_upwards [lt_mem_nhds hz] with y hy
    exact (legendreKernel_derivatives nu hy).1.deriv
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  exact ((legendreKernel_derivatives nu hz).2.congr_of_eventuallyEq he).deriv

/-- Integral second remainder of the actual Riemann kernel; defined also on the diagonal. -/
def circleSecondRemainder (nu : ℂ) (E Z : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, ((1-t:ℝ):ℂ)*legendreKernelSecond nu (E+t*(Z-E))

/-- The cancelled circle remainder contains the square of the radial displacement exactly. -/
theorem circleRemainder_eq_second (nu : ℂ) {E Z : ℝ} (hE : 0 < E) (hZ : 0 < Z) :
    circleRemainder nu E Z=((Z:ℂ)-(E:ℂ))^(2 : ℕ)*circleSecondRemainder nu E Z := by
  have hp (t : ℝ) (ht : t ∈ Icc 0 1) : 0 < E+t*(Z-E) := by
    have h1 := mul_nonneg ht.1 hZ.le
    have h2 := mul_nonneg (sub_nonneg.mpr ht.2) hE.le
    by_cases h : t=0
    · simp [h,hE]
    · have h3 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) hZ
      nlinarith
  have hf (t : ℝ) (ht : t ∈ Icc 0 1) : ContDiffAt ℝ (1+1:ℕ) (legendreKernel nu) (E+t • (Z-E)) :=
    (legendre_contDiffAt nu (hp t ht)).of_le (by
      change (↑(2:ℕ∞):WithTop ℕ∞) ≤ ↑(⊤:ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (f := legendreKernel nu)
    (x := E) (y := Z-E) hf
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,Nat.factorial_zero,Nat.factorial_one,
    Nat.cast_one,inv_one,pow_zero,pow_one,one_smul,zero_add,iteratedDeriv_zero,iteratedDeriv_one,
    smul_eq_mul,Nat.reduceAdd,add_sub_cancel] at ht
  rw [(legendreKernel_derivatives nu hE).1.deriv] at ht
  have hi : (∫ t in (0:ℝ)..1, (1-t) • ((Z-E)^(2 : ℕ) • iteratedDeriv 2 (legendreKernel nu) (E+t*(Z-E)))) =
      ((Z:ℂ)-(E:ℂ))^(2 : ℕ)*circleSecondRemainder nu E Z := by
    rw [circleSecondRemainder,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    dsimp only
    rw [legendre_iteratedDeriv_two nu (hp t ht)]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hi] at ht
  simp only [Complex.real_smul] at ht
  push_cast at ht
  dsimp [circleRemainder]
  linear_combination ht

/-- Both causal branches have a quadratic radial displacement after circle cancellation. -/
theorem actionRemainderDensity_eq_second (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    actionRemainderDensity s nu E image u =
      (u:ℂ)^(2 : ℕ)*((slope E image:ℂ)^(2 : ℕ)*actionDensity s 0 E image u)*
        circleSecondRemainder nu E.val (argument E image u) := by
  rw [actionRemainderDensity,circleRemainder_eq_second nu (by linarith [E.property])
    (lt_of_lt_of_le (by norm_num) (argument_ge_one E image hu))]
  simp only [argument]
  push_cast
  ring

/-- Homogenized source cubic: it is defined when the direct slope is zero. -/
def regularCubic (s : ℂ) (c d u : ℝ) : ℂ :=
  (c:ℂ)*cubicPolynomial s 0 u+(d:ℂ)*(cubicPolynomial s 1 u-cubicPolynomial s 0 u)
private def regularCubicFirst (s : ℂ) (c d u : ℝ) : ℂ :=
  (c:ℂ)*cubicFirst s 0 u+(d:ℂ)*(cubicFirst s 1 u-cubicFirst s 0 u)
private def regularCubicSecond (s : ℂ) (c d u : ℝ) : ℂ :=
  (c:ℂ)*cubicSecond s 0 u+(d:ℂ)*(cubicSecond s 1 u-cubicSecond s 0 u)

/-- Exact source-action numerator, with no division by the causal slope. -/
def regularActionWeight (s : ℂ) (c d u : ℝ) : ℂ :=
  (1-(u:ℂ))*((d:ℂ)-(c:ℂ)*u)*
    (2*powerFirst (2*s-2) (1+u)*regularCubic s c d u+
      (u:ℂ)*powerSecond (2*s-2) (1+u)*regularCubic s c d u+
      2*power (2*s-2) (1+u)*regularCubicFirst s c d u+
      2*(u:ℂ)*powerFirst (2*s-2) (1+u)*regularCubicFirst s c d u+
      (u:ℂ)*power (2*s-2) (1+u)*regularCubicSecond s c d u)+
  (2*(c:ℂ)*u-c-d)*
    (power (2*s-2) (1+u)*regularCubic s c d u+
      (u:ℂ)*powerFirst (2*s-2) (1+u)*regularCubic s c d u+
      (u:ℂ)*power (2*s-2) (1+u)*regularCubicFirst s c d u)-
  2*(c:ℂ)*(u:ℂ)*power (2*s-2) (1+u)*regularCubic s c d u

private theorem regularCubic_eq (s : ℂ) (c d u : ℝ) (hc : c ≠ 0) :
    regularCubic s c d u=(c:ℂ)*cubicPolynomial s ((d:ℂ)/(c:ℂ)) u ∧
    regularCubicFirst s c d u=(c:ℂ)*cubicFirst s ((d:ℂ)/(c:ℂ)) u ∧
    regularCubicSecond s c d u=(c:ℂ)*cubicSecond s ((d:ℂ)/(c:ℂ)) u := by
  have hn : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  dsimp [regularCubic,regularCubicFirst,regularCubicSecond,cubicPolynomial,cubicFirst,cubicSecond,c0,c1,c2,c3]
  constructor
  · field_simp [hn]
    ring
  constructor <;> field_simp [hn] <;> ring

/-- The apparent square pole of the radial adjoint density has an explicit regular numerator. -/
theorem regularActionWeight_eq (s : ℂ) (E : Delay) (image : Bool) (u : ℝ) :
    regularActionWeight s (slope E image) (other E image) u=
      (slope E image:ℂ)^(2 : ℕ)*actionDensity s 0 E image u := by
  have hn : (slope E image:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (slope_pos E image))
  obtain ⟨h0,h1,h2⟩ := regularCubic_eq s (slope E image) (other E image) u (ne_of_gt (slope_pos E image))
  unfold regularActionWeight
  rw [h0,h1,h2]
  simp only [actionDensity,branchKernel,legendre_zero,mul_one,cubicWeight,cubicWeightFirst,
    cubicWeightSecond,metricCoeff,metricFirst,ratio]
  field_simp [hn]

/-- Fully combined radial remainder; neither causal slope occurs in a denominator. -/
theorem actionRemainderDensity_eq_regular (s nu : ℂ) (E : Delay) (image : Bool) {u : ℝ}
    (hu : u ∈ Icc 0 (upper E image)) :
    actionRemainderDensity s nu E image u=(u:ℂ)^(2 : ℕ)*
      regularActionWeight s (slope E image) (other E image) u*
      circleSecondRemainder nu E.val (argument E image u) := by
  rw [actionRemainderDensity_eq_second s nu E image hu,regularActionWeight_eq]

/-- The source numerator is jointly continuous at zero direct slope as well as positive slope. -/
theorem regularActionWeight_continuousAt (s : ℂ) (c d u : ℝ) (hu : 0 < 1+u) :
    ContinuousAt (fun v : ℝ × ℝ × ℝ => regularActionWeight s v.1 v.2.1 v.2.2) (c,d,u) := by
  have hp : ContinuousAt (fun v : ℝ × ℝ × ℝ => power (2*s-2) (1+v.2.2)) (c,d,u) :=
    by
      have hc : ContinuousAt (fun v : ℝ × ℝ × ℝ => 1+v.2.2) (c,d,u) := by fun_prop
      exact (power_derivatives (2*s-2) hu).1.continuousAt.comp_of_eq hc rfl
  have hn : ((1+u:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  unfold regularActionWeight regularCubic regularCubicFirst regularCubicSecond
    cubicPolynomial cubicFirst cubicSecond powerFirst powerSecond
  fun_prop (disch := first | assumption | exact pow_ne_zero 2 hn)

end
end RHTower.D4BMCausalSourceKernel
