import GaloisForLFunctions.HTGeometry.HypergeometricSpatialJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerJets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Characteristic Riemann kernel for the original BM wave

An explicit Gauss series on a positive real chart gives a globally defined
Legendre kernel. Its actual derivatives and the hyperbolic characteristic
invariant yield the original BM time-domain wave equation at every causal
point and every complex angular frequency. The characteristic value fixes
the normalization; the reflected causal kernel vanishes at the AdS boundary.

These are differential and boundary identities for the constructed kernel.
The integrated forced Green action, its full angular circle-mean realization,
and the nonlinear Einstein pairing require further proofs.
-/

namespace RHTower.D4BMCausalKernel
open GaloisForLFunctions.HTGeometry D4BMLaplaceRadial
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private def legendreArgument (z : ℝ) : ℝ := (z-1)/(z+1)
private def legendrePrefactor (nu : ℂ) (z : ℝ) : ℂ := power nu ((z+1)/2)
private def legendreGauss (nu : ℂ) (z : ℝ) : ℂ :=
  (ordinaryHypergeometricSeries ℂ (-nu) (-nu) 1).sum (legendreArgument z : ℂ)
private def legendreGaussFirst (nu : ℂ) (z : ℝ) : ℂ :=
  ordinaryHypergeometricFirstDerivativeSeriesValue (-nu) (-nu) 1 (legendreArgument z)
private def legendreGaussSecond (nu : ℂ) (z : ℝ) : ℂ :=
  ordinaryHypergeometricSecondDerivativeSeriesValue (-nu) (-nu) 1 (legendreArgument z)

/-- Legendre solution expressed by a Gauss series whose argument stays inside the unit disk for positive real input. -/
def legendreKernel (nu : ℂ) (z : ℝ) : ℂ := legendrePrefactor nu z*legendreGauss nu z
/-- First derivative formula of the positive-chart Legendre kernel. -/
def legendreKernelFirst (nu : ℂ) (z : ℝ) : ℂ :=
  legendrePrefactor nu z*(nu*legendreGauss nu z/(z+1)+2*legendreGaussFirst nu z/(z+1)^2)
/-- Second derivative formula with every Gauss and prefactor term retained. -/
def legendreKernelSecond (nu : ℂ) (z : ℝ) : ℂ :=
  legendrePrefactor nu z*(nu*(nu-1)*legendreGauss nu z/(z+1)^2+
    4*(nu-1)*legendreGaussFirst nu z/(z+1)^3+4*legendreGaussSecond nu z/(z+1)^4)

private theorem argument_disk {z : ℝ} (hz : 0 < z) : ‖(legendreArgument z : ℂ)‖ₑ < 1 := by
  have hp : 0 < z+1 := by linarith
  have ha : |legendreArgument z| < 1 := by
    rw [abs_lt]
    unfold legendreArgument
    constructor
    · apply (lt_div_iff₀ hp).mpr
      linarith
    · apply (div_lt_iff₀ hp).mpr
      linarith
  have hn : ‖(legendreArgument z : ℂ)‖ < 1 := by simpa using ha
  rw [← ENNReal.coe_one,enorm_lt_coe]
  exact_mod_cast hn

private theorem argument_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt legendreArgument (2/(z+1)^2) z := by
  have h := ((hasDerivAt_id z).sub_const 1).div ((hasDerivAt_id z).add_const 1)
    (by linarith : z+1 ≠ 0)
  apply h.congr_deriv
  dsimp
  ring

private theorem prefactor_hasDerivAt (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (legendrePrefactor nu) (nu*legendrePrefactor nu z/(z+1)) z := by
  have hp := (power_derivatives nu (by linarith : 0 < (z+1)/2)).1
  have ha := ((hasDerivAt_id z).add_const 1).div_const 2
  have h := hp.scomp z ha
  apply h.congr_deriv
  simp only [powerFirst,legendrePrefactor,Complex.real_smul]
  push_cast
  field_simp [show (z:ℂ)+1 ≠ 0 by exact_mod_cast (by linarith : z+1 ≠ 0)]

private theorem gauss_derivatives (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (legendreGauss nu) (2*legendreGaussFirst nu z/(z+1)^2) z ∧
    HasDerivAt (legendreGaussFirst nu) (2*legendreGaussSecond nu z/(z+1)^2) z := by
  let p := ordinaryHypergeometricSeries ℂ (-nu) (-nu) 1
  have hrad : ‖(legendreArgument z : ℂ)‖ₑ < p.radius :=
    (argument_disk hz).trans_le (hypergeometric_radius_one_le _ _ _)
  have h0 := (p.hasFDerivAt_sum hrad).hasDerivAt
  have h1 := p.derivSeries.hasFDerivAt_sum (hrad.trans_le p.radius_le_radius_derivSeries)
  have h1' := (h1.clm_apply (hasFDerivAt_const (1:ℂ) (legendreArgument z : ℂ))).hasDerivAt
  have ha := (argument_hasDerivAt hz).ofReal_comp
  constructor
  · convert! h0.scomp z ha using 1
    simp [legendreGaussFirst,ordinaryHypergeometricFirstDerivativeSeriesValue,p,smul_eq_mul]
    ring
  · convert! h1'.scomp z ha using 1
    simp [legendreGaussSecond,ordinaryHypergeometricSecondDerivativeSeriesValue,p,smul_eq_mul]
    ring

/-- Both displayed Legendre jets are actual real derivatives for every complex degree. -/
theorem legendreKernel_derivatives (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (legendreKernel nu) (legendreKernelFirst nu z) z ∧
    HasDerivAt (legendreKernelFirst nu) (legendreKernelSecond nu z) z := by
  have hp := prefactor_hasDerivAt nu hz
  obtain ⟨hg,hg1⟩ := gauss_derivatives nu hz
  have hx := ((hasDerivAt_id z).ofReal_comp).add_const (1:ℂ)
  have hn : (z:ℂ)+1 ≠ 0 := by exact_mod_cast (by linarith : z+1 ≠ 0)
  constructor
  · apply (hp.mul hg).congr_deriv
    dsimp [legendreKernelFirst]
    ring
  · apply (hp.mul (((hg.const_mul nu).div hx hn).add
      ((hg1.const_mul 2).div (hx.pow 2) (pow_ne_zero 2 hn)))).congr_deriv
    dsimp [legendreKernelSecond]
    field_simp [hn]
    ring

/-- The constructed Legendre function solves its exact differential equation on the positive chart. -/
theorem legendreKernel_equation (nu : ℂ) {z : ℝ} (hz : 0 < z) :
    ((z:ℂ)^2-1)*legendreKernelSecond nu z+2*z*legendreKernelFirst nu z-
      nu*(nu+1)*legendreKernel nu z = 0 := by
  have hrad := (argument_disk hz).trans_le (hypergeometric_radius_one_le (-nu) (-nu) 1)
  have hc : ∀ j : ℕ, (j:ℂ) ≠ -(1:ℂ) := by
    intro j hj
    have h := congrArg Complex.re hj
    simp only [Complex.natCast_re,Complex.neg_re,Complex.one_re] at h
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have h := ordinaryHypergeometric_standardGaussODE (-nu) (-nu) 1 (legendreArgument z) hc hrad
  change (legendreArgument z:ℂ)*(1-(legendreArgument z:ℂ))*legendreGaussSecond nu z+
    (1-(-nu+-nu+1)*(legendreArgument z:ℂ))*legendreGaussFirst nu z-
      (-nu)*(-nu)*legendreGauss nu z = 0 at h
  have hn : (z:ℂ)+1 ≠ 0 := by exact_mod_cast (by linarith : z+1 ≠ 0)
  have he : ((z:ℂ)^2-1)*legendreKernelSecond nu z+2*z*legendreKernelFirst nu z-
      nu*(nu+1)*legendreKernel nu z = 2*legendrePrefactor nu z/((z:ℂ)+1)*
        ((legendreArgument z:ℂ)*(1-(legendreArgument z:ℂ))*legendreGaussSecond nu z+
        (1-(-nu+-nu+1)*(legendreArgument z:ℂ))*legendreGaussFirst nu z-
          (-nu)*(-nu)*legendreGauss nu z) := by
    unfold legendreKernel legendreKernelFirst legendreKernelSecond legendreArgument
    push_cast
    field_simp [hn]
    ring
  rw [he,h,mul_zero]

/-- The characteristic value of the constructed kernel is one. -/
theorem legendreKernel_one (nu : ℂ) : legendreKernel nu 1 = 1 := by
  simp only [legendreKernel,legendrePrefactor,legendreGauss,legendreArgument,power]
  norm_num
  exact ordinaryHypergeometric_zero _ _ _

/-- Two-point hyperbolic invariant in the original static time and tortoise coordinates. -/
def invariant (h x y : ℝ) : ℝ :=
  (Real.cosh h+Real.sinh x*Real.sinh y)/(Real.cosh x*Real.cosh y)
/-- Actual first derivative of the invariant in time separation. -/
def invariantTimeFirst (h x y : ℝ) : ℝ := Real.sinh h/(Real.cosh x*Real.cosh y)
/-- Actual second derivative of the invariant in time separation. -/
def invariantTimeSecond (h x y : ℝ) : ℝ := Real.cosh h/(Real.cosh x*Real.cosh y)
/-- Actual first derivative of the invariant in the target tortoise coordinate. -/
def invariantSpaceFirst (h x y : ℝ) : ℝ := Real.tanh y-Real.tanh x*invariant h x y
/-- Actual second derivative of the invariant in the target tortoise coordinate. -/
def invariantSpaceSecond (h x y : ℝ) : ℝ :=
  (2*Real.tanh x^2-1)*invariant h x y-Real.tanh x*Real.tanh y

/-- Both invariant time jets are obtained by differentiating the hyperbolic functions. -/
theorem invariant_time_derivatives (h x y : ℝ) :
    HasDerivAt (fun t => invariant t x y) (invariantTimeFirst h x y) h ∧
    HasDerivAt (fun t => invariantTimeFirst t x y) (invariantTimeSecond h x y) h := by
  constructor
  · exact ((Real.hasDerivAt_cosh h).add_const _).div_const _
  · exact (Real.hasDerivAt_sinh h).div_const _

private theorem tanh_derivative (x : ℝ) :
    HasDerivAt Real.tanh (1-Real.tanh x^2) x := by
  have hc := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  rw [show Real.tanh = Real.sinh / Real.cosh by
    funext r
    exact Real.tanh_eq_sinh_div_cosh r]
  apply h.congr_deriv
  simp only [Pi.div_apply]
  field_simp [hc]

/-- Both target-coordinate jets are actual derivatives of the original invariant. -/
theorem invariant_space_derivatives (h x y : ℝ) :
    HasDerivAt (fun r => invariant h r y) (invariantSpaceFirst h x y) x ∧
    HasDerivAt (fun r => invariantSpaceFirst h r y) (invariantSpaceSecond h x y) x := by
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  have hd := (((Real.hasDerivAt_sinh x).mul_const (Real.sinh y)).const_add (Real.cosh h)).div
    ((Real.hasDerivAt_cosh x).mul_const (Real.cosh y)) (mul_ne_zero hx hy)
  have hfirst : HasDerivAt (fun r => invariant h r y) (invariantSpaceFirst h x y) x := by
    apply hd.congr_deriv
    simp only [invariantSpaceFirst,invariant,Real.tanh_eq_sinh_div_cosh]
    field_simp [hx,hy]
  refine ⟨hfirst,?_⟩
  apply (((tanh_derivative x).mul hfirst).const_sub (Real.tanh y)).congr_deriv
  dsimp [invariantSpaceFirst,invariantSpaceSecond]
  ring

/-- Exact chain-rule coefficients converting the Legendre equation into the BM wave equation. -/
theorem invariant_wave_geometry (h x y : ℝ) :
    invariantTimeFirst h x y^2-invariantSpaceFirst h x y^2 =
      (invariant h x y^2-1)/Real.cosh x^2 ∧
    invariantTimeSecond h x y-invariantSpaceSecond h x y =
      2*invariant h x y/Real.cosh x^2 := by
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  have hs3 : Real.sinh x^3 = Real.sinh x*(Real.cosh x^2-1) := by
    rw [← Real.sinh_sq]
    ring
  have hs4 : Real.sinh x^4 = (Real.cosh x^2-1)^2 := by
    rw [← Real.sinh_sq]
    ring
  constructor
  · simp only [invariantTimeFirst,invariantSpaceFirst,invariant,Real.tanh_eq_sinh_div_cosh]
    field_simp [hx,hy]
    ring_nf
    simp only [Real.sinh_sq,hs3,hs4]
    ring
  · simp only [invariantTimeSecond,invariantSpaceSecond,invariant,Real.tanh_eq_sinh_div_cosh]
    field_simp [hx,hy]
    ring_nf
    simp only [Real.sinh_sq,hs3]
    ring

/-- A point inside the forward characteristic cone of the original wave coordinates. -/
structure CausalPoint where
  time : ℝ
  target : ℝ
  source : ℝ
  inside : |target-source| ≤ time

/-- The forward cone maps to the real Legendre chart at or above one. -/
theorem invariant_causal (p : CausalPoint) : 1 ≤ invariant p.time p.target p.source := by
  have htime : 0 ≤ p.time := (abs_nonneg _).trans p.inside
  have hcosh : Real.cosh (p.target-p.source) ≤ Real.cosh p.time :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg htime] using p.inside)
  rw [invariant,le_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))]
  rw [Real.cosh_sub] at hcosh
  linarith

/-- The invariant is one on the direct characteristic. -/
theorem invariant_characteristic (x y : ℝ) : invariant (x-y) x y = 1 := by
  unfold invariant
  rw [Real.cosh_sub]
  field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos y).ne']
  ring

/-- Direct and reflected invariants agree at the original AdS endpoint. -/
theorem invariant_AdS (h y : ℝ) : invariant h 0 y = invariant h 0 (-y) := by
  simp [invariant]

/-- Explicit Riemann function composed with the original characteristic invariant. -/
def riemannKernel (nu : ℂ) (h x y : ℝ) : ℂ := legendreKernel nu (invariant h x y)
/-- Actual first time derivative of the constructed Riemann function. -/
def riemannTimeFirst (nu : ℂ) (h x y : ℝ) : ℂ :=
  legendreKernelFirst nu (invariant h x y)*(invariantTimeFirst h x y : ℂ)
/-- Actual second time derivative, including the derivative of the invariant. -/
def riemannTimeSecond (nu : ℂ) (h x y : ℝ) : ℂ :=
  legendreKernelSecond nu (invariant h x y)*(invariantTimeFirst h x y : ℂ)^2+
    legendreKernelFirst nu (invariant h x y)*(invariantTimeSecond h x y : ℂ)
/-- Actual first target-coordinate derivative of the Riemann function. -/
def riemannSpaceFirst (nu : ℂ) (h x y : ℝ) : ℂ :=
  legendreKernelFirst nu (invariant h x y)*(invariantSpaceFirst h x y : ℂ)
/-- Actual second target-coordinate derivative, with both chain-rule terms. -/
def riemannSpaceSecond (nu : ℂ) (h x y : ℝ) : ℂ :=
  legendreKernelSecond nu (invariant h x y)*(invariantSpaceFirst h x y : ℂ)^2+
    legendreKernelFirst nu (invariant h x y)*(invariantSpaceSecond h x y : ℂ)

private theorem kernel_time_derivatives (nu : ℂ) (h x y : ℝ) (hz : 0 < invariant h x y) :
    HasDerivAt (fun t => riemannKernel nu t x y) (riemannTimeFirst nu h x y) h ∧
    HasDerivAt (fun t => riemannTimeFirst nu t x y) (riemannTimeSecond nu h x y) h := by
  obtain ⟨hp,hp1⟩ := legendreKernel_derivatives nu hz
  obtain ⟨hg,hg1⟩ := invariant_time_derivatives h x y
  constructor
  · simpa only [riemannKernel,riemannTimeFirst,Function.comp_def,Complex.real_smul,mul_comm] using
      hp.scomp h hg
  · convert! (hp1.scomp h hg).mul hg1.ofReal_comp using 1
    simp only [Complex.real_smul,riemannTimeSecond,Function.comp_apply]
    ring

private theorem kernel_space_derivatives (nu : ℂ) (h x y : ℝ) (hz : 0 < invariant h x y) :
    HasDerivAt (fun r => riemannKernel nu h r y) (riemannSpaceFirst nu h x y) x ∧
    HasDerivAt (fun r => riemannSpaceFirst nu h r y) (riemannSpaceSecond nu h x y) x := by
  obtain ⟨hp,hp1⟩ := legendreKernel_derivatives nu hz
  obtain ⟨hg,hg1⟩ := invariant_space_derivatives h x y
  constructor
  · simpa only [riemannKernel,riemannSpaceFirst,Function.comp_def,Complex.real_smul,mul_comm] using
      hp.scomp x hg
  · convert! (hp1.scomp x hg).mul hg1.ofReal_comp using 1
    simp only [Complex.real_smul,riemannSpaceSecond,Function.comp_apply]
    ring

/-- The constructed function solves the original tortoise wave with potential fixed by its Legendre degree. -/
theorem riemannKernel_wave (nu : ℂ) (p : CausalPoint) :
    deriv (deriv (fun h => riemannKernel nu h p.target p.source)) p.time-
      deriv (deriv (fun x => riemannKernel nu p.time x p.source)) p.target-
      nu*(nu+1)/(Real.cosh p.target : ℂ)^2*riemannKernel nu p.time p.target p.source = 0 := by
  have hz : 0 < invariant p.time p.target p.source := lt_of_lt_of_le (by norm_num) (invariant_causal p)
  have ht := kernel_time_derivatives nu p.time p.target p.source hz
  have hx := kernel_space_derivatives nu p.time p.target p.source hz
  have et : deriv (fun h => riemannKernel nu h p.target p.source) =ᶠ[𝓝 p.time]
      (fun h => riemannTimeFirst nu h p.target p.source) := by
    filter_upwards [(invariant_time_derivatives p.time p.target p.source).1.continuousAt.eventually_const_lt hz] with h hh
    exact (kernel_time_derivatives nu h p.target p.source hh).1.deriv
  have ex : deriv (fun x => riemannKernel nu p.time x p.source) =ᶠ[𝓝 p.target]
      (fun x => riemannSpaceFirst nu p.time x p.source) := by
    filter_upwards [(invariant_space_derivatives p.time p.target p.source).1.continuousAt.eventually_const_lt hz] with x hh
    exact (kernel_space_derivatives nu p.time x p.source hh).1.deriv
  rw [et.deriv_eq,ex.deriv_eq,ht.2.deriv,hx.2.deriv]
  have hg1 : (invariantTimeFirst p.time p.target p.source:ℂ)^2-
      (invariantSpaceFirst p.time p.target p.source:ℂ)^2 =
      ((invariant p.time p.target p.source:ℂ)^2-1)/(Real.cosh p.target:ℂ)^2 := by
    exact_mod_cast (invariant_wave_geometry p.time p.target p.source).1
  have hg2 : (invariantTimeSecond p.time p.target p.source:ℂ)-
      (invariantSpaceSecond p.time p.target p.source:ℂ) =
      2*(invariant p.time p.target p.source:ℂ)/(Real.cosh p.target:ℂ)^2 := by
    exact_mod_cast (invariant_wave_geometry p.time p.target p.source).2
  have he : riemannTimeSecond nu p.time p.target p.source-riemannSpaceSecond nu p.time p.target p.source-
      nu*(nu+1)/(Real.cosh p.target:ℂ)^2*riemannKernel nu p.time p.target p.source =
      (((invariant p.time p.target p.source:ℂ)^2-1)*legendreKernelSecond nu (invariant p.time p.target p.source)+
      2*(invariant p.time p.target p.source:ℂ)*legendreKernelFirst nu (invariant p.time p.target p.source)-
      nu*(nu+1)*legendreKernel nu (invariant p.time p.target p.source))/(Real.cosh p.target:ℂ)^2 := by
    dsimp only [riemannTimeSecond,riemannSpaceSecond,riemannKernel]
    linear_combination legendreKernelSecond nu (invariant p.time p.target p.source)*hg1+
      legendreKernelFirst nu (invariant p.time p.target p.source)*hg2
  rw [he,legendreKernel_equation nu hz,zero_div]

/-- Unit characteristic normalization follows from the actual Legendre value. -/
theorem riemannKernel_characteristic (nu : ℂ) (x y : ℝ) : riemannKernel nu (x-y) x y = 1 := by
  rw [riemannKernel,invariant_characteristic,legendreKernel_one]

/-- Subtracting the reflected function cancels the AdS value exactly. -/
theorem riemannKernel_AdS (nu : ℂ) (h y : ℝ) : riemannKernel nu h 0 y-riemannKernel nu h 0 (-y) = 0 := by
  rw [riemannKernel,riemannKernel,invariant_AdS,sub_self]

/-- Original BM angular-frequency parametrization of the Riemann function. -/
def bmRiemannKernel (chi : ℂ) (h x y : ℝ) : ℂ := riemannKernel (-1/2+Complex.I*chi) h x y

/-- Exact BM wave equation at every complex angular frequency and every point in the causal cone. -/
theorem bmRiemannKernel_wave (chi : ℂ) (p : CausalPoint) :
    deriv (deriv (fun h => bmRiemannKernel chi h p.target p.source)) p.time-
      deriv (deriv (fun x => bmRiemannKernel chi p.time x p.source)) p.target+
      (1/4+chi^2)/(Real.cosh p.target:ℂ)^2*bmRiemannKernel chi p.time p.target p.source = 0 := by
  have h := riemannKernel_wave (-1/2+Complex.I*chi) p
  have hc : -(-1/2+Complex.I*chi)*((-1/2+Complex.I*chi)+1) = 1/4+chi^2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  dsimp only [bmRiemannKernel]
  rw [← hc]
  linear_combination h

/-- Forward-cone kernel with the original AdS image and the characteristic factor one half. -/
def dirichletCausalKernel (chi : ℂ) (h x y : ℝ) : ℂ :=
  ((if |x-y| ≤ h then bmRiemannKernel chi h x y else 0)-
    (if |x+y| ≤ h then bmRiemannKernel chi h x (-y) else 0))/2

/-- The two causal image terms have the same support and value at the AdS boundary. -/
theorem dirichletCausalKernel_boundary (chi : ℂ) (h y : ℝ) : dirichletCausalKernel chi h 0 y = 0 := by
  simp [dirichletCausalKernel,bmRiemannKernel,riemannKernel,invariant]

/-- The constructed kernel vanishes before the source time. -/
theorem dirichletCausalKernel_before (chi : ℂ) (h x y : ℝ) (hh : h < 0) :
    dirichletCausalKernel chi h x y = 0 := by
  have h1 : ¬ |x-y| ≤ h := not_le.mpr (hh.trans_le (abs_nonneg _))
  have h2 : ¬ |x+y| ≤ h := not_le.mpr (hh.trans_le (abs_nonneg _))
  simp [dirichletCausalKernel,h1,h2]

end
end RHTower.D4BMCausalKernel
