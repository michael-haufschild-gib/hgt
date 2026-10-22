import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma410

/-!
# Suzuki's normalization derivative (equation 4.17)

Suzuki defines
`m(a) = exp (∫₁ᵃ μ(b) db / b)` and then uses the exact logarithmic-derivative identity
`a m'(a) / m(a) = μ(a)`.  The earlier formalization supplied the literal normalization and
continuity at `a = 1`, but not this derivative identity.

The totalized coupling is zero below one.  Consequently its quotient by `a` has a removable
singularity at zero and is continuous on all of `ℝ`.  This closes the fundamental-theorem-of-
calculus step globally, strictly strengthening the paper's positive-half-line statement.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-- The totalized scalar coupling vanishes on the entire exterior half-line. -/
theorem suzukiHankelMuScalar_eq_zero_of_le_one
    {omega a : ℝ} (homega : 1 < omega) (ha : a ≤ 1) :
    suzukiHankelMuScalar omega homega a = 0 := by
  have hna : ¬ 1 < a := not_lt.mpr ha
  simp [suzukiHankelMuScalar, suzukiHankelMuReal,
    suzukiHankelBoundaryTraceReal, hna]

/-- The totalized scalar coupling is continuous on the whole real line, including the aperture
endpoint `a = 1`. -/
theorem continuous_suzukiHankelMuScalar
    {omega : ℝ} (homega : 1 < omega) :
    Continuous (suzukiHankelMuScalar omega homega) := by
  rw [continuous_iff_continuousAt]
  intro a
  rcases lt_trichotomy a 1 with hlt | rfl | hgt
  · exact continuousAt_suzukiHankelMuScalar_of_lt_one homega hlt
  · exact continuousAt_suzukiHankelMuScalar_one homega
  · exact continuousAt_suzukiHankelMuScalar_of_one_lt homega hgt

/-- The density `μ(a)/a` in equation (4.17) is globally continuous.  At zero this is a genuine
removable singularity because `μ` vanishes on a neighborhood of zero. -/
theorem continuous_suzukiHankelMuScalar_div
    {omega : ℝ} (homega : 1 < omega) :
    Continuous (fun a => suzukiHankelMuScalar omega homega a / a) := by
  rw [continuous_iff_continuousAt]
  intro a
  by_cases ha : a < 1
  · have heq : (fun b => suzukiHankelMuScalar omega homega b / b) =ᶠ[𝓝 a]
        fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ha] with b hb
      rw [suzukiHankelMuScalar_eq_zero_of_le_one homega (le_of_lt hb), zero_div]
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have ha0 : a ≠ 0 := by linarith
    exact (continuous_suzukiHankelMuScalar homega).continuousAt.div continuousAt_id ha0

/-- The equation-(4.17) density is interval-integrable for arbitrary real endpoints. -/
theorem intervalIntegrable_suzukiHankelMuScalar_div_all
    {omega a : ℝ} (homega : 1 < omega) :
    IntervalIntegrable (fun b => suzukiHankelMuScalar omega homega b / b)
      volume 1 a :=
  (continuous_suzukiHankelMuScalar_div homega).intervalIntegrable 1 a

/-- Suzuki's normalization has its stated exterior value `m(a)=1` for every `a≤1`; in
particular this proves the paper's convention on `0<a≤1`. -/
theorem suzukiHankelM_eq_one_of_le_one
    {omega a : ℝ} (homega : 1 < omega) (ha : a ≤ 1) :
    suzukiHankelM omega homega a = 1 := by
  have hz : (∫ b in (1 : ℝ)..a,
      suzukiHankelMuScalar omega homega b / b) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with b hb
    rcases Set.mem_uIoc.mp hb with hb | hb
    · exact False.elim (not_lt_of_ge ha (lt_of_lt_of_le hb.1 hb.2))
    · rw [suzukiHankelMuScalar_eq_zero_of_le_one homega hb.2, zero_div]
  rw [suzukiHankelM, hz, Real.exp_zero]

/-- Fundamental-theorem-of-calculus form of Suzuki's normalization derivative.  It holds on all
of `ℝ`; the printed theorem only uses it for `a>0`. -/
theorem hasDerivAt_suzukiHankelM
    {omega a : ℝ} (homega : 1 < omega) :
    HasDerivAt (suzukiHankelM omega homega)
      (suzukiHankelM omega homega a *
        (suzukiHankelMuScalar omega homega a / a)) a := by
  let f : ℝ → ℝ := fun b => suzukiHankelMuScalar omega homega b / b
  have hfcont : Continuous f := continuous_suzukiHankelMuScalar_div homega
  have hprim : HasDerivAt (fun x : ℝ => ∫ b in (1 : ℝ)..x, f b) (f a) a := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hfcont.intervalIntegrable 1 a)
      hfcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hfcont.continuousAt
  have hexp := (Real.hasDerivAt_exp
    (∫ b in (1 : ℝ)..a, f b)).comp a hprim
  change HasDerivAt
    (fun x : ℝ => Real.exp
      (∫ b in (1 : ℝ)..x, suzukiHankelMuScalar omega homega b / b))
    (Real.exp (∫ b in (1 : ℝ)..a,
      suzukiHankelMuScalar omega homega b / b) *
        (suzukiHankelMuScalar omega homega a / a)) a
  simpa only [f, Function.comp_def] using hexp

/-- Pointwise derivative form of the normalization identity. -/
theorem deriv_suzukiHankelM
    {omega a : ℝ} (homega : 1 < omega) :
    deriv (suzukiHankelM omega homega) a =
      suzukiHankelM omega homega a *
        (suzukiHankelMuScalar omega homega a / a) :=
  (hasDerivAt_suzukiHankelM homega).deriv

/-- Exact differential identity following equation (4.17):
`m(a)⁻¹ a ∂ₐm(a) = μ(a)`.  The formal result is global. -/
theorem suzuki_equation_417_logarithmic_derivative
    {omega a : ℝ} (homega : 1 < omega) :
    a * deriv (suzukiHankelM omega homega) a /
        suzukiHankelM omega homega a =
      suzukiHankelMuScalar omega homega a := by
  rw [deriv_suzukiHankelM homega]
  by_cases ha : a = 0
  · subst a
    rw [suzukiHankelMuScalar_eq_zero_of_le_one homega (by norm_num)]
    norm_num
  · field_simp [suzukiHankelM_ne_zero homega a, ha]

/-- Equivalent logarithmic-derivative form of equation (4.17). -/
theorem hasDerivAt_log_suzukiHankelM
    {omega a : ℝ} (homega : 1 < omega) :
    HasDerivAt (fun b => Real.log (suzukiHankelM omega homega b))
      (suzukiHankelMuScalar omega homega a / a) a := by
  have hlog := (hasDerivAt_suzukiHankelM homega).log
    (suzukiHankelM_ne_zero homega a)
  convert hlog using 1
  field_simp [suzukiHankelM_ne_zero homega a]

end RHTower
