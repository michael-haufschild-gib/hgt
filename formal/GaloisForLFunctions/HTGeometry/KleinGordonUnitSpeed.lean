import GaloisForLFunctions.HTGeometry.KleinGordonRealProbe

/-!
# Unit propagation speed

The Fourier convention of mathlib puts a factor `(2π)⁻²` in front of the Laplacian, so the field
equation as proved has propagation speed `1/2π`. Measuring the spatial derivatives along the
*rescaled* basis `(2π)⁻¹eᵢ` removes it: a directional derivative scales quadratically, and
`(2π)⁻²·4π² = 1`.

The equation then reads

`∂ₜ²u = Δu - u + Vu`,

which is the wave operator of the corpus, with the signature `(-1, 1, …, 1)` and the potential
`V - 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] {N : ℕ}

variable (a : WienerFamily E N) (G₀ : E →ᵇ ℂ)

/-- **A second directional derivative scales quadratically in the direction.** -/
theorem deriv_deriv_kgFlowField_dir_smul (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (t : ℝ)
    (x v : E) (c : ℝ) :
    deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • (c • v))) 0
      = ((c : ℂ)) ^ 2 * deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • v)) 0 := by
  rw [deriv_deriv_kgFlowField_dir a G₀ hN t x (c • v),
    deriv_deriv_kgFlowField_dir a G₀ hN t x v, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (2 * Real.pi * Complex.I * ((⟪ξ, c • v⟫ : ℝ) : ℂ)) ^ 2 * kgChar x ξ
      * kgFlowDensity a G₀ t ξ
    = (c : ℂ) ^ 2 * ((2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ 2 * kgChar x ξ
      * kgFlowDensity a G₀ t ξ)
  rw [real_inner_smul_right, Complex.ofReal_mul]
  ring

/-- **The field equation with unit propagation speed.** -/
theorem kgFlowField_wave_equation_unit (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    deriv (deriv fun r : ℝ => kgFlowField a G₀ r x) t
      = ∑ i, deriv (deriv fun s : ℝ =>
            kgFlowField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0
        - kgFlowField a G₀ t x + kgPotential (a.density t) x * kgFlowField a G₀ t x := by
  have hmain := kgFlowField_wave_equation a G₀ hN b t x
  have hscale : ∀ i : ι, deriv (deriv fun s : ℝ =>
      kgFlowField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0
      = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) ^ 2
        * deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • b i)) 0 := fun i =>
    deriv_deriv_kgFlowField_dir_smul a G₀ hN t x (b i) ((2 * Real.pi)⁻¹)
  have hsum : (∑ i, deriv (deriv fun s : ℝ =>
      kgFlowField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0)
      = (((2 * Real.pi) ^ 2 : ℝ) : ℂ)⁻¹
        * ∑ i, deriv (deriv fun s : ℝ => kgFlowField a G₀ t (x + s • b i)) 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hscale i]
    congr 1
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    rw [Complex.ofReal_inv, Complex.ofReal_pow]
    field_simp
  rw [hsum]
  exact hmain

/-- **The real field equation with unit propagation speed.** -/
theorem kgRealField_wave_equation_unit (hN : (Module.finrank ℝ E : ℝ) + 2 < N)
    (hreal : IsRealFamily a) (b : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    deriv (deriv fun r : ℝ => kgRealField a G₀ r x) t
      = ∑ i, deriv (deriv fun s : ℝ =>
            kgRealField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0
        - kgRealField a G₀ t x
        + (kgPotential (a.density t) x).re * kgRealField a G₀ t x := by
  have hLHS : deriv (deriv fun r : ℝ => kgRealField a G₀ r x) t
      = (deriv (deriv fun r : ℝ => kgFlowField a G₀ r x) t).re :=
    deriv_deriv_re_eq (differentiableAt_kgFlowField_time a G₀ hN x)
      (differentiableAt_deriv_kgFlowField_time a G₀ hN x) t
  have hdir : ∀ i : ι, deriv (deriv fun s : ℝ =>
      kgRealField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0
      = (deriv (deriv fun s : ℝ =>
        kgFlowField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0).re := fun i =>
    deriv_deriv_re_eq
      (differentiableAt_kgFlowField_dir a G₀ hN t x ((2 * Real.pi)⁻¹ • b i))
      (differentiableAt_deriv_kgFlowField_dir a G₀ hN t x ((2 * Real.pi)⁻¹ • b i)) 0
  have hsum : (∑ i, deriv (deriv fun s : ℝ =>
      kgRealField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0)
      = (∑ i, deriv (deriv fun s : ℝ =>
        kgFlowField a G₀ t (x + s • ((2 * Real.pi)⁻¹ • b i))) 0).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => hdir i
  have him := kgPotential_im (hreal t) x
  rw [hLHS, kgFlowField_wave_equation_unit a G₀ hN b t x, hsum]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, him, zero_mul, sub_zero,
    kgRealField]

end GaloisForLFunctions.HTGeometry
