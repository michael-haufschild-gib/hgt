import GaloisForLFunctions.HTGeometry.StrelitzMaximumModulusSet
import GaloisForLFunctions.HTGeometry.NevanlinnaCoeffFun
import GaloisForLFunctions.RHTower.LogModulusHorizontal

/-!
# Differential identity on a smooth maximum-modulus path

A smooth logarithmic polar path has velocity `z (1 + i θ')`.  If the path remains in the
maximum-modulus locus, the first Euler logarithmic jet remains real.  Differentiating that reality
constraint shows that the derivative of its real value is

`normSq(v) / Re(v)`,

whenever `Re(v) > 0`, where `v` is the second Euler logarithmic jet.  If `Re(v) = 0`, the same
constraint forces `v = 0`.  This is the exact maximum-path identity behind the positive-slope
Strelitz integration argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Set
open GaloisForLFunctions

/-- Logarithmic polar path with log radius `t` and angle `θ(t)`. -/
def strelitzLogPolarPath (θ : ℝ → ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) + Complex.I * (θ t : ℂ))

@[simp]
theorem norm_strelitzLogPolarPath (θ : ℝ → ℝ) (t : ℝ) :
    ‖strelitzLogPolarPath θ t‖ = Real.exp t := by
  simp [strelitzLogPolarPath, Complex.norm_exp]

@[simp]
theorem strelitzLogPolarPath_ne_zero (θ : ℝ → ℝ) (t : ℝ) :
    strelitzLogPolarPath θ t ≠ 0 := by
  exact Complex.exp_ne_zero _

/-- Velocity of a differentiable logarithmic polar path. -/
theorem hasDerivAt_strelitzLogPolarPath {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (strelitzLogPolarPath θ)
      (strelitzLogPolarPath θ t * (1 + Complex.I * (θ' : ℂ))) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hθc : HasDerivAt (fun s : ℝ => (θ s : ℂ)) (θ' : ℂ) t :=
    hθ.ofReal_comp
  have h := (ht.add (hθc.const_mul Complex.I)).cexp
  convert h using 1 <;> rfl

/-- Algebraic elimination of angular velocity from a real-valued holomorphic slope. -/
theorem re_mul_logPolarVelocity_eq_normSq_div_re
    {v : ℂ} {θ' : ℝ} (hv : 0 < v.re)
    (him : (v * (1 + Complex.I * (θ' : ℂ))).im = 0) :
    (v * (1 + Complex.I * (θ' : ℂ))).re = Complex.normSq v / v.re := by
  norm_num [Complex.mul_im] at him
  norm_num [Complex.mul_re, Complex.normSq_apply]
  field_simp [ne_of_gt hv]
  linear_combination -v.im * him

/-- A zero real part and the maximum-path reality constraint force the complete second jet to
vanish. -/
theorem eq_zero_of_re_eq_zero_of_im_mul_logPolarVelocity_eq_zero
    {v : ℂ} {θ' : ℝ} (hre : v.re = 0)
    (him : (v * (1 + Complex.I * (θ' : ℂ))).im = 0) :
    v = 0 := by
  norm_num [Complex.mul_im, hre] at him
  apply Complex.ext
  · simpa using hre
  · simpa using him

variable {a : ℕ → ℂ}

/-- A maximum-modulus point on a positive circle is nonvanishing whenever one coefficient is
nonzero. -/
theorem coeffFun_ne_zero_of_strelitzLogPolarPath_mem_circleMaximumSet
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ : ℝ → ℝ} {t : ℝ}
    (hmax : strelitzLogPolarPath θ t ∈ circleMaximumSet (coeffFun a)) :
    coeffFun a (strelitzLogPolarPath θ t) ≠ 0 := by
  obtain ⟨_, _, hμpos⟩ := exists_maxTerm_eq ha (Real.exp_pos t) hn₀
  have hfloor := maxTerm_le_norm_of_mem_circleMaximumSet ha
    (z := strelitzLogPolarPath θ t) (by simpa using Real.exp_pos t) hmax
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hμpos (by simpa using hfloor)))

/-- Along a differentiable path contained locally in the maximum-modulus locus, the imaginary
derivative of the real Euler logarithmic jet vanishes. -/
theorem im_eulerLogDerivSecond_mul_logPolarVelocity_eq_zero
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hmax : ∀ᶠ s : ℝ in nhds t,
      strelitzLogPolarPath θ s ∈ circleMaximumSet (coeffFun a)) :
    (eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ t) *
      (1 + Complex.I * (θ' : ℂ))).im = 0 := by
  let z := strelitzLogPolarPath θ t
  let v := eulerLogDerivSecond (coeffFun a) z
  have hfz : coeffFun a z ≠ 0 := by
    apply coeffFun_ne_zero_of_strelitzLogPolarPath_mem_circleMaximumSet ha hn₀
    exact hmax.self_of_nhds
  have hfa : AnalyticAt ℂ (coeffFun a) z :=
    GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha z (by simp)
  have hu : DifferentiableAt ℂ (eulerLogDeriv (coeffFun a)) z := by
    exact (differentiableAt_id.mul hfa.deriv.differentiableAt).div
      hfa.differentiableAt hfz
  have hpath := hasDerivAt_strelitzLogPolarPath hθ
  have huPath := hu.hasDerivAt.comp t hpath
  have hvalue :
      deriv (eulerLogDeriv (coeffFun a)) z *
          (strelitzLogPolarPath θ t * (1 + Complex.I * (θ' : ℂ))) =
        v * (1 + Complex.I * (θ' : ℂ)) := by
    dsimp [z, v, eulerLogDerivSecond]
    ring
  have himPath : HasDerivAt
      (fun s => (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ s)).im)
      (v * (1 + Complex.I * (θ' : ℂ))).im t := by
    simpa [Function.comp_def, hvalue] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t huPath
  have himZero :
      (fun s => (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ s)).im)
        =ᶠ[nhds t] (fun _ => 0) := by
    filter_upwards [hmax] with s hs
    exact eulerLogDeriv_im_eq_zero_of_mem_circleMaximumSet
      ha (strelitzLogPolarPath_ne_zero θ s)
        (coeffFun_ne_zero_of_strelitzLogPolarPath_mem_circleMaximumSet ha hn₀ hs) hs
  have himDerivZero : HasDerivAt
      (fun s => (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ s)).im) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq himZero
  exact himPath.unique himDerivZero

/-- On a smooth local maximum-modulus path, vanishing curvature forces the entire second Euler jet
to vanish. -/
theorem eulerLogDerivSecond_eq_zero_of_re_eq_zero_on_strelitzMaximumPath
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hmax : ∀ᶠ s : ℝ in nhds t,
      strelitzLogPolarPath θ s ∈ circleMaximumSet (coeffFun a))
    (hre : (eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ t)).re = 0) :
    eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ t) = 0 := by
  apply eq_zero_of_re_eq_zero_of_im_mul_logPolarVelocity_eq_zero hre
  exact im_eulerLogDerivSecond_mul_logPolarVelocity_eq_zero ha hn₀ hθ hmax

/-- Exact derivative of the real Euler logarithmic jet along a smooth local maximum-modulus path. -/
theorem hasDerivAt_re_eulerLogDeriv_strelitzMaximumPath
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t)
    (hmax : ∀ᶠ s : ℝ in nhds t,
      strelitzLogPolarPath θ s ∈ circleMaximumSet (coeffFun a))
    (hvpos : 0 < (eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ t)).re) :
    HasDerivAt
      (fun s => (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ s)).re)
      (Complex.normSq (eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ t)) /
        (eulerLogDerivSecond (coeffFun a) (strelitzLogPolarPath θ t)).re) t := by
  let z := strelitzLogPolarPath θ t
  let v := eulerLogDerivSecond (coeffFun a) z
  have hfz : coeffFun a z ≠ 0 := by
    apply coeffFun_ne_zero_of_strelitzLogPolarPath_mem_circleMaximumSet ha hn₀
    exact hmax.self_of_nhds
  have hfa : AnalyticAt ℂ (coeffFun a) z :=
    GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha z (by simp)
  have hu : DifferentiableAt ℂ (eulerLogDeriv (coeffFun a)) z := by
    exact (differentiableAt_id.mul hfa.deriv.differentiableAt).div
      hfa.differentiableAt hfz
  have hpath := hasDerivAt_strelitzLogPolarPath hθ
  have huPath := hu.hasDerivAt.comp t hpath
  have hvalue :
      deriv (eulerLogDeriv (coeffFun a)) z *
          (strelitzLogPolarPath θ t * (1 + Complex.I * (θ' : ℂ))) =
        v * (1 + Complex.I * (θ' : ℂ)) := by
    dsimp [z, v, eulerLogDerivSecond]
    ring
  have hrePath : HasDerivAt
      (fun s => (eulerLogDeriv (coeffFun a) (strelitzLogPolarPath θ s)).re)
      (v * (1 + Complex.I * (θ' : ℂ))).re t := by
    simpa [Function.comp_def, hvalue] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t huPath
  have him := im_eulerLogDerivSecond_mul_logPolarVelocity_eq_zero ha hn₀ hθ hmax
  convert hrePath using 1
  exact (re_mul_logPolarVelocity_eq_normSq_div_re hvpos him).symm

end

end GaloisForLFunctions.HTGeometry
