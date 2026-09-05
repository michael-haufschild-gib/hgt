import GaloisForLFunctions.HTGeometry.SpinTorsionCorrelator

/-!
# Exact finite-density radial blocks

After cancellation of the removable spherical-Bessel singularity, the two finite-density radial
blocks have elementary continuous integrands.  Their exact interval integrals give the sine-cosine
numerators used in the normalized spin-torsion correction.  The final theorem derives that
correction from the integrals and recovers its dimensionless closed form.
-/

open scoped Interval

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Regularized radial integrand corresponding to `p² j₀(pr)`. -/
def spinTorsionRadialI0Integrand (r p : ℝ) : ℝ := p * Real.sin (p * r) / r

/-- Elementary primitive of the regularized `j₀` radial integrand. -/
def spinTorsionRadialI0Primitive (r p : ℝ) : ℝ :=
  (Real.sin (p * r) - p * r * Real.cos (p * r)) / r ^ 3

/-- Exact derivative identity behind the first finite-density radial block. -/
theorem spinTorsionRadialI0Primitive_hasDerivAt (logR p : ℝ) :
    HasDerivAt (spinTorsionRadialI0Primitive (Real.exp logR))
      (spinTorsionRadialI0Integrand (Real.exp logR) p) p := by
  unfold spinTorsionRadialI0Primitive spinTorsionRadialI0Integrand
  let r := Real.exp logR
  have hr : r ≠ 0 := Real.exp_ne_zero logR
  have hpr : HasDerivAt (fun u : ℝ => u * r) r p := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id p).mul_const r
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (u * r))
      (Real.cos (p * r) * r) p := (Real.hasDerivAt_sin _).comp p hpr
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (u * r))
      (-Real.sin (p * r) * r) p := (Real.hasDerivAt_cos _).comp p hpr
  have h := (hsin.sub (hpr.mul hcos)).div_const (r ^ 3)
  have hvalue :
      (Real.cos (p * r) * r -
          (r * Real.cos (p * r) + p * r * (-Real.sin (p * r) * r))) / r ^ 3 =
        p * Real.sin (p * r) / r := by
    field_simp [hr]
    ring
  rw [hvalue] at h
  simpa [r] using h

/-- Exact first radial integral, with positive scales encoded logarithmically. -/
theorem spinTorsionRadialI0_integral (logMu logR : ℝ) :
    ∫ p in (0 : ℝ)..Real.exp logMu, spinTorsionRadialI0Integrand (Real.exp logR) p =
      spinTorsionRadialI0Primitive (Real.exp logR) (Real.exp logMu) := by
  have hderiv : ∀ p ∈ Set.uIcc (0 : ℝ) (Real.exp logMu),
      HasDerivAt (spinTorsionRadialI0Primitive (Real.exp logR))
        (spinTorsionRadialI0Integrand (Real.exp logR) p) p :=
    fun p _ => spinTorsionRadialI0Primitive_hasDerivAt logR p
  have hint : IntervalIntegrable (spinTorsionRadialI0Integrand (Real.exp logR))
      MeasureTheory.volume 0 (Real.exp logMu) := by
    apply Continuous.intervalIntegrable
    unfold spinTorsionRadialI0Integrand
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [spinTorsionRadialI0Primitive]

/-- Regularized radial integrand corresponding to `p² j₁(pr)`. -/
def spinTorsionRadialI1Integrand (r p : ℝ) : ℝ :=
  Real.sin (p * r) / r ^ 2 - p * Real.cos (p * r) / r

/-- Elementary primitive of the regularized `j₁` radial integrand. -/
def spinTorsionRadialI1Primitive (r p : ℝ) : ℝ :=
  (2 - 2 * Real.cos (p * r) - p * r * Real.sin (p * r)) / r ^ 3

/-- Exact derivative identity behind the second finite-density radial block. -/
theorem spinTorsionRadialI1Primitive_hasDerivAt (logR p : ℝ) :
    HasDerivAt (spinTorsionRadialI1Primitive (Real.exp logR))
      (spinTorsionRadialI1Integrand (Real.exp logR) p) p := by
  unfold spinTorsionRadialI1Primitive spinTorsionRadialI1Integrand
  let r := Real.exp logR
  have hr : r ≠ 0 := Real.exp_ne_zero logR
  have hpr : HasDerivAt (fun u : ℝ => u * r) r p := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id p).mul_const r
  have hsin : HasDerivAt (fun u : ℝ => Real.sin (u * r))
      (Real.cos (p * r) * r) p := (Real.hasDerivAt_sin _).comp p hpr
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (u * r))
      (-Real.sin (p * r) * r) p := (Real.hasDerivAt_cos _).comp p hpr
  have htwo : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 p := hasDerivAt_const p 2
  have h := ((htwo.sub (hcos.const_mul 2)).sub (hpr.mul hsin)).div_const (r ^ 3)
  have hvalue :
      (0 - 2 * (-Real.sin (p * r) * r) -
          (r * Real.sin (p * r) + p * r * (Real.cos (p * r) * r))) / r ^ 3 =
        Real.sin (p * r) / r ^ 2 - p * Real.cos (p * r) / r := by
    field_simp [hr]
    ring
  rw [hvalue] at h
  simpa [r] using h

/-- Exact second radial integral, with positive scales encoded logarithmically. -/
theorem spinTorsionRadialI1_integral (logMu logR : ℝ) :
    ∫ p in (0 : ℝ)..Real.exp logMu, spinTorsionRadialI1Integrand (Real.exp logR) p =
      spinTorsionRadialI1Primitive (Real.exp logR) (Real.exp logMu) := by
  have hderiv : ∀ p ∈ Set.uIcc (0 : ℝ) (Real.exp logMu),
      HasDerivAt (spinTorsionRadialI1Primitive (Real.exp logR))
        (spinTorsionRadialI1Integrand (Real.exp logR) p) p :=
    fun p _ => spinTorsionRadialI1Primitive_hasDerivAt logR p
  have hint : IntervalIntegrable (spinTorsionRadialI1Integrand (Real.exp logR))
      MeasureTheory.volume 0 (Real.exp logMu) := by
    apply Continuous.intervalIntegrable
    unfold spinTorsionRadialI1Integrand
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [spinTorsionRadialI1Primitive]

/-- First normalized finite-density radial block. -/
def finiteDensityRadialI0 (mu r : ℝ) : ℝ :=
  (∫ p in (0 : ℝ)..mu, spinTorsionRadialI0Integrand r p) / (2 * Real.pi ^ 2)

/-- Second normalized finite-density radial block. -/
def finiteDensityRadialI1 (mu r : ℝ) : ℝ :=
  (∫ p in (0 : ℝ)..mu, spinTorsionRadialI1Integrand r p) / (2 * Real.pi ^ 2)

/-- Closed form of the first normalized radial block. -/
theorem finiteDensityRadialI0_eq (logMu logR : ℝ) :
    finiteDensityRadialI0 (Real.exp logMu) (Real.exp logR) =
      (Real.sin (Real.exp logMu * Real.exp logR) -
          Real.exp logMu * Real.exp logR *
            Real.cos (Real.exp logMu * Real.exp logR)) /
        (2 * Real.pi ^ 2 * Real.exp logR ^ 3) := by
  rw [finiteDensityRadialI0, spinTorsionRadialI0_integral]
  unfold spinTorsionRadialI0Primitive
  field_simp [Real.exp_ne_zero, Real.pi_ne_zero]

/-- Closed form of the second normalized radial block. -/
theorem finiteDensityRadialI1_eq (logMu logR : ℝ) :
    finiteDensityRadialI1 (Real.exp logMu) (Real.exp logR) =
      (2 - 2 * Real.cos (Real.exp logMu * Real.exp logR) -
          Real.exp logMu * Real.exp logR *
            Real.sin (Real.exp logMu * Real.exp logR)) /
        (2 * Real.pi ^ 2 * Real.exp logR ^ 3) := by
  rw [finiteDensityRadialI1, spinTorsionRadialI1_integral]
  unfold spinTorsionRadialI1Primitive
  field_simp [Real.exp_ne_zero, Real.pi_ne_zero]

/-- Dimensionless correction reconstructed directly from the two radial integrals. -/
def finiteDensityRadialNormalizedCorrection (mu r : ℝ) : ℝ :=
  Real.pi ^ 4 * r ^ 6 *
    (finiteDensityRadialI0 mu r ^ 2 - finiteDensityRadialI1 mu r ^ 2)

/-- Exact radial-integral derivation of the finite-density correction formula. -/
theorem finiteDensityRadialNormalizedCorrection_eq (logMu logR : ℝ) :
    finiteDensityRadialNormalizedCorrection (Real.exp logMu) (Real.exp logR) =
      finiteDensityCorrectionShape (Real.exp logMu * Real.exp logR) := by
  rw [finiteDensityRadialNormalizedCorrection, finiteDensityRadialI0_eq,
    finiteDensityRadialI1_eq]
  unfold finiteDensityCorrectionShape
  field_simp [Real.exp_ne_zero, Real.pi_ne_zero]
  ring

end GaloisForLFunctions.HTGeometry
