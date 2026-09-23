import GaloisForLFunctions.RHTower.XiMassSpacelikeShellExpansion

/-!
# The leading term of the spacelike mass profile

Feeding the order-one Schläfli asymptotic into the Fourier–Bessel identity collapses the leading
term to a single monomial in the propagation radius:

`2 a τ / z · e^{-az} · (1/√2) · √(π/(az)) = √(2πa) · τ · e^{-az} / (z √z)`.

The constant `√(2πa)` is exactly the prefactor of the stationary-phase amplitude, and the whole
`z`-dependence sits in the single factor `z^{-3/2}`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The stationary-phase amplitude constant. -/
theorem sqrt_two_pi_mul_eq {a : ℝ} (ha : 0 < a) :
    (Real.sqrt 2)⁻¹ * (2 * a) * Real.sqrt (Real.pi / a) = Real.sqrt (2 * Real.pi * a) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hpa : (0 : ℝ) < Real.pi / a := by positivity
  have hpasq : Real.sqrt (Real.pi / a) ^ (2 : ℕ) = Real.pi / a := Real.sq_sqrt hpa.le
  have hnn : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ * (2 * a) * Real.sqrt (Real.pi / a) := by positivity
  have htarget : (0 : ℝ) ≤ 2 * Real.pi * a := by positivity
  have hval : a * (Real.pi / a) = Real.pi := by field_simp
  have hexp : ((Real.sqrt 2)⁻¹ * (2 * a) * Real.sqrt (Real.pi / a)) ^ (2 : ℕ)
      = (Real.sqrt 2 ^ (2 : ℕ))⁻¹ * (2 * a) ^ (2 : ℕ) * Real.sqrt (Real.pi / a) ^ (2 : ℕ) := by
    field_simp
  have hsq : ((Real.sqrt 2)⁻¹ * (2 * a) * Real.sqrt (Real.pi / a)) ^ (2 : ℕ) = 2 * Real.pi * a := by
    rw [hexp, h2sq, hpasq]
    field_simp
  rw [← hsq, Real.sqrt_sq hnn]

/-- **The collapsed leading term.**  The Schläfli leading term of the Fourier–Bessel identity is a
single `z^{-3/2}` monomial. -/
theorem besselLeading_collapse {a : ℝ} (ha : 0 < a) {τ z : ℂ} (hz : 0 < z.re) :
    2 * (a : ℂ) * τ / z
        * (Complex.exp (-((a : ℂ) * z)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * z)))
      = ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) * τ * Complex.exp (-((a : ℂ) * z))
        / (z * HTGeometry.csqrt z) := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have hane : ((a : ℂ)) ≠ 0 := by
    simpa using ne_of_gt ha
  have hinvre : 0 < (z⁻¹).re := HTGeometry.re_inv_pos hz
  have hpa : (0 : ℝ) < Real.pi / a := by positivity
  have hsplit : (Real.pi : ℂ) / ((a : ℂ) * z) = ((Real.pi / a : ℝ) : ℂ) * z⁻¹ := by
    push_cast
    field_simp
  have hroot : HTGeometry.csqrt ((Real.pi : ℂ) / ((a : ℂ) * z))
      = ((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * (HTGeometry.csqrt z)⁻¹ := by
    rw [hsplit, HTGeometry.csqrt_ofReal_mul hpa hinvre, HTGeometry.csqrt_inv hz]
  have hcsne : HTGeometry.csqrt z ≠ 0 := HTGeometry.csqrt_ne_zero hz
  have hconst : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (2 * (a : ℂ)) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ)
      = ((Real.sqrt (2 * Real.pi * a) : ℝ) : ℂ) := by
    rw [← sqrt_two_pi_mul_eq ha]
    push_cast
    ring
  have hrewrite : 2 * (a : ℂ) * τ / z
        * (Complex.exp (-((a : ℂ) * z)) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
          * (((Real.sqrt (Real.pi / a) : ℝ) : ℂ) * (HTGeometry.csqrt z)⁻¹))
      = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (2 * (a : ℂ)) * ((Real.sqrt (Real.pi / a) : ℝ) : ℂ))
        * τ * Complex.exp (-((a : ℂ) * z)) * (z * HTGeometry.csqrt z)⁻¹ := by
    field_simp
  rw [hroot, hrewrite, hconst, div_eq_mul_inv]

end

end RHTower
