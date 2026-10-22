import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticHermitianRadialLine
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialKahlerTrace

/-!
# The critical Hilbert measure of the Hermitian radial line

The Kähler area of the complex line is the imaginary wedge of the holomorphic coordinate with its
conjugate, and in polar coordinates it is `r dr ∧ dθ`, which the squared radius turns into
`½ dx ∧ dθ`.  Integrating a radial function against the area therefore gives `π` times its
integral against `dx` on the half line: the radial source metric is the critical weighted space
`L²(ℝ_{>0}, x d^×x) = L²(ℝ_{>0}, dx)`, not an arbitrary completion.

The squared radius and the half-density flow are forced: requiring the radius and the area to have
the same weight one fixes both exponents.

* `deningerKahlerForm_eq` : the Kähler form is the oriented area.
* `deningerPolarArea_radial`, `deningerPolarArea_squared` : `(10)`.
* `deningerCriticalMeasure` : `(11)`.
* `deningerMultiplicativeWeight` : `(12)`.
* `deningerLineHalfDensity_forced` : the exponents are forced.
-/

namespace RHTower

open MeasureTheory Set Real

section KahlerForm

/-- **The Kähler form is the oriented area.**  Evaluating `(i/2) dz ∧ dz̄` on two tangent vectors
gives the determinant of their real coordinates. -/
theorem deningerKahlerForm_eq (u v : ℂ) :
    (Complex.I / 2) * (u * (starRingEnd ℂ) v - v * (starRingEnd ℂ) u)
      = ((deningerHermitianLineArea (u.re, u.im) (v.re, v.im) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [deningerHermitianLineArea, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- The Hodge star sends the first coframe vector to the second. -/
theorem deningerHermitianLineHodge_fst :
    deningerHermitianLineHodge (1, 0) = (0, 1) := by
  simp [deningerHermitianLineHodge]

/-- The Hodge star sends the second coframe vector to minus the first. -/
theorem deningerHermitianLineHodge_snd :
    deningerHermitianLineHodge (0, 1) = (-1, 0) := by
  simp [deningerHermitianLineHodge]

end KahlerForm

section PolarArea

/-- The polar parametrization of the complex line. -/
noncomputable def deningerPolarPoint (r θ : ℝ) : ℝ × ℝ :=
  (r * Real.cos θ, r * Real.sin θ)

/-- The radial tangent vector of the polar parametrization. -/
theorem deningerPolarPoint_hasDerivAt_radial (r θ : ℝ) :
    HasDerivAt (fun s => deningerPolarPoint s θ) (Real.cos θ, Real.sin θ) r := by
  have h1 : HasDerivAt (fun s : ℝ => s * Real.cos θ) (Real.cos θ) r := by
    simpa using (hasDerivAt_id r).mul_const (Real.cos θ)
  have h2 : HasDerivAt (fun s : ℝ => s * Real.sin θ) (Real.sin θ) r := by
    simpa using (hasDerivAt_id r).mul_const (Real.sin θ)
  exact h1.prodMk h2

/-- The angular tangent vector of the polar parametrization. -/
theorem deningerPolarPoint_hasDerivAt_angular (r θ : ℝ) :
    HasDerivAt (fun t => deningerPolarPoint r t) (-(r * Real.sin θ), r * Real.cos θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ => r * Real.cos t) (-(r * Real.sin θ)) θ := by
    simpa using (Real.hasDerivAt_cos θ).const_mul r
  have h2 : HasDerivAt (fun t : ℝ => r * Real.sin t) (r * Real.cos θ) θ := by
    simpa using (Real.hasDerivAt_sin θ).const_mul r
  exact h1.prodMk h2

/-- **The area in polar coordinates is `r dr ∧ dθ`.** -/
theorem deningerPolarArea_radial (r θ : ℝ) :
    deningerHermitianLineArea (Real.cos θ, Real.sin θ)
        (-(r * Real.sin θ), r * Real.cos θ) = r := by
  have hpy := Real.sin_sq_add_cos_sq θ
  simp only [deningerHermitianLineArea]
  linear_combination r * hpy

/-- The radial tangent vector in the squared radius coordinate. -/
theorem deningerPolarPoint_hasDerivAt_squared {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    HasDerivAt (fun y => deningerPolarPoint (Real.sqrt y) θ)
      (Real.cos θ / (2 * Real.sqrt x), Real.sin θ / (2 * Real.sqrt x)) x := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have h1 : HasDerivAt (fun y : ℝ => Real.sqrt y * Real.cos θ)
      (Real.cos θ / (2 * Real.sqrt x)) x := by
    have := hsqrt.mul_const (Real.cos θ)
    rw [show 1 / (2 * Real.sqrt x) * Real.cos θ = Real.cos θ / (2 * Real.sqrt x) by ring] at this
    exact this
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt y * Real.sin θ)
      (Real.sin θ / (2 * Real.sqrt x)) x := by
    have := hsqrt.mul_const (Real.sin θ)
    rw [show 1 / (2 * Real.sqrt x) * Real.sin θ = Real.sin θ / (2 * Real.sqrt x) by ring] at this
    exact this
  exact h1.prodMk h2

/-- **The area in the squared radius coordinate is `½ dx ∧ dθ`.** -/
theorem deningerPolarArea_squared {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    deningerHermitianLineArea
        (Real.cos θ / (2 * Real.sqrt x), Real.sin θ / (2 * Real.sqrt x))
        (-(Real.sqrt x * Real.sin θ), Real.sqrt x * Real.cos θ) = 1 / 2 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hpy := Real.sin_sq_add_cos_sq θ
  simp only [deningerHermitianLineArea]
  field_simp
  nlinarith [hpy]

end PolarArea

section CriticalMeasure

/-- **The critical Hilbert measure.**  Integrating a radial function against the Kähler area is
`π` times its integral against `dx` on the half line.  This is the polar reduction of a radial
integral, read on the squared modulus. -/
theorem deningerCriticalMeasure (f : ℝ → ℂ) :
    (∫ z : ℂ, ‖f (‖z‖ ^ 2)‖ ^ 2) = π * ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  have h := deningerPolarTrace fun x : ℝ => ((‖f x‖ ^ 2 : ℝ) : ℂ)
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

end CriticalMeasure

section MultiplicativeWeight

/-- **The critical weight is the Lebesgue measure.**  Multiplying the multiplicative Haar density
`d^×x = dx / x` by the weight `x` returns the additive measure on the half line. -/
theorem deningerMultiplicativeWeight :
    (((volume.restrict (Ioi (0 : ℝ))).withDensity fun x => ENNReal.ofReal x⁻¹).withDensity
        fun x => ENNReal.ofReal x)
      = volume.restrict (Ioi (0 : ℝ)) := by
  have hf : Measurable fun x : ℝ => ENNReal.ofReal x⁻¹ :=
    ENNReal.measurable_ofReal.comp measurable_inv
  have hg : Measurable fun x : ℝ => ENNReal.ofReal x := ENNReal.measurable_ofReal
  have hae : ((fun x : ℝ => ENNReal.ofReal x⁻¹) * fun x : ℝ => ENNReal.ofReal x)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hx0)), inv_mul_cancel₀ (ne_of_gt hx0),
      ENNReal.ofReal_one]
  rw [← withDensity_mul _ hf hg, withDensity_congr_ae hae, withDensity_one]

end MultiplicativeWeight

section ForcedExponents

/-- The radius of exponent `δ`. -/
noncomputable def deningerRadiusPow (δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  (Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) ^ δ

/-- **The half-density scaling and the squared radius are forced.**  If the flow `z ↦ e^{ct} z`
gives both the radius of exponent `δ` and the Kähler area the weight one, then `c = 1/2` and
`δ = 2`. -/
theorem deningerLineHalfDensity_forced {c δ : ℝ}
    (harea : ∀ t : ℝ, ∀ z w : ℝ × ℝ,
      deningerHermitianLineArea (deningerHermitianLineScale (Real.exp (c * t)) z)
          (deningerHermitianLineScale (Real.exp (c * t)) w)
        = Real.exp t * deningerHermitianLineArea z w)
    (hradius : ∀ t : ℝ, ∀ z : ℝ × ℝ,
      deningerRadiusPow δ (deningerHermitianLineScale (Real.exp (c * t)) z)
        = Real.exp t * deningerRadiusPow δ z) :
    c = 1 / 2 ∧ δ = 2 := by
  have hc : c = 1 / 2 := by
    have h := harea 1 (1, 0) (0, 1)
    have hL : deningerHermitianLineArea
        (deningerHermitianLineScale (Real.exp (c * 1)) ((1 : ℝ), (0 : ℝ)))
        (deningerHermitianLineScale (Real.exp (c * 1)) ((0 : ℝ), (1 : ℝ)))
        = Real.exp (c * 1) * Real.exp (c * 1) := by
      simp only [deningerHermitianLineArea, deningerHermitianLineScale]
      ring
    have hR : deningerHermitianLineArea ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) = 1 := by
      simp only [deningerHermitianLineArea]
      ring
    rw [hL, hR, ← Real.exp_add] at h
    simp only [mul_one] at h
    rw [Real.exp_eq_exp] at h
    linarith
  refine ⟨hc, ?_⟩
  have h := hradius 1 (1, 0)
  have hscale : deningerHermitianLineScale (Real.exp (c * 1)) ((1 : ℝ), (0 : ℝ))
      = (Real.exp c, 0) := by
    simp [deningerHermitianLineScale]
  have hbase : deningerRadiusPow δ ((1 : ℝ), (0 : ℝ)) = 1 := by
    rw [deningerRadiusPow]
    norm_num
  rw [hscale, hbase, mul_one] at h
  have hsq : deningerRadiusPow δ (Real.exp c, 0) = Real.exp c ^ δ := by
    show (Real.sqrt ((Real.exp c) ^ 2 + (0 : ℝ) ^ 2)) ^ δ = Real.exp c ^ δ
    rw [show ((Real.exp c) ^ 2 + (0 : ℝ) ^ 2) = (Real.exp c) ^ 2 by ring,
      Real.sqrt_sq (le_of_lt (Real.exp_pos _))]
  rw [hsq, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.exp_eq_exp, hc] at h
  linarith

end ForcedExponents

section HalfDensityFlow

/-- The half-density flow `s_t z = e^{t/2} z`. -/
noncomputable def deningerLineHalfDensityFlow (t : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  deningerHermitianLineScale (Real.exp (t / 2)) z

/-- The square of the half density is the density. -/
theorem deningerLineHalfDensity_sq (t : ℝ) : (Real.exp (t / 2)) ^ 2 = Real.exp t := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- **The Poisson radius.**  The squared radius has weight one for the half-density flow. -/
theorem deningerLineHalfDensityFlow_radius (t : ℝ) (z : ℝ × ℝ) :
    deningerHermitianLineRadius (deningerLineHalfDensityFlow t z)
      = Real.exp t * deningerHermitianLineRadius z := by
  rw [deningerLineHalfDensityFlow, deningerHermitianLineRadius_scale, deningerLineHalfDensity_sq]

/-- **The radial pullback is dilation.**  At `t = log n` the flow pulls a radial test function back
to its dilate by `n`. -/
theorem deningerLineHalfDensityFlow_radialPullback (f : ℝ → ℂ) {n : ℝ} (hn : 0 < n) (z : ℝ × ℝ) :
    f (deningerHermitianLineRadius (deningerLineHalfDensityFlow (Real.log n) z))
      = f (n * deningerHermitianLineRadius z) := by
  rw [deningerLineHalfDensityFlow_radius, Real.exp_log hn]

/-- **The weight-one Kähler class.**  The area has the same weight as the radius. -/
theorem deningerLineHalfDensityFlow_area (t : ℝ) (z w : ℝ × ℝ) :
    deningerHermitianLineArea (deningerLineHalfDensityFlow t z) (deningerLineHalfDensityFlow t w)
      = Real.exp t * deningerHermitianLineArea z w := by
  rw [deningerLineHalfDensityFlow, deningerLineHalfDensityFlow, deningerHermitianLineArea_scale,
    deningerLineHalfDensity_sq]

/-- **Flow and Hodge compatibility.**  The same scalar multiplies both members of the oriented
orthonormal coframe. -/
theorem deningerLineHalfDensityFlow_hodge (t : ℝ) (z : ℝ × ℝ) :
    deningerHermitianLineHodge (deningerLineHalfDensityFlow t z)
      = deningerLineHalfDensityFlow t (deningerHermitianLineHodge z) := by
  rw [deningerLineHalfDensityFlow, deningerLineHalfDensityFlow, deningerHermitianLineHodge_scale]

end HalfDensityFlow

section UnitaryFrame

/-- A unitary change of frame of the Hermitian line, in real coordinates. -/
noncomputable def deningerFrameRotation (α : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * Real.cos α - z.2 * Real.sin α, z.1 * Real.sin α + z.2 * Real.cos α)

/-- **A unitary frame change preserves the radius.** -/
theorem deningerFrameRotation_radius (α : ℝ) (z : ℝ × ℝ) :
    deningerHermitianLineRadius (deningerFrameRotation α z)
      = deningerHermitianLineRadius z := by
  have hpy := Real.sin_sq_add_cos_sq α
  simp only [deningerHermitianLineRadius, deningerFrameRotation]
  linear_combination (z.1 ^ 2 + z.2 ^ 2) * hpy

/-- **A unitary frame change preserves the Kähler area.** -/
theorem deningerFrameRotation_area (α : ℝ) (z w : ℝ × ℝ) :
    deningerHermitianLineArea (deningerFrameRotation α z) (deningerFrameRotation α w)
      = deningerHermitianLineArea z w := by
  have hpy := Real.sin_sq_add_cos_sq α
  simp only [deningerHermitianLineArea, deningerFrameRotation]
  linear_combination (z.1 * w.2 - z.2 * w.1) * hpy

/-- **A unitary frame change commutes with the Hodge star.**  So the whole construction glues over
a Hermitian line bundle. -/
theorem deningerFrameRotation_hodge (α : ℝ) (z : ℝ × ℝ) :
    deningerHermitianLineHodge (deningerFrameRotation α z)
      = deningerFrameRotation α (deningerHermitianLineHodge z) := by
  refine Prod.ext ?_ ?_ <;>
    simp only [deningerHermitianLineHodge, deningerFrameRotation] <;>
    ring

end UnitaryFrame

end RHTower
