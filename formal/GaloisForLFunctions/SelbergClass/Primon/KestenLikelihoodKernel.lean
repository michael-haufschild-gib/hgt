import GaloisForLFunctions.SelbergClass.Primon.KestenEntropyIntegrals
import GaloisForLFunctions.SelbergClass.Primon.ArithmeticAverage

/-!
# The likelihood covariance is a Cauchy kernel

A prime likelihood is the reflection average of the charged local factor
at inverse square-root prime fugacity. Arithmetic averaging consequently
evaluates every mixed likelihood expectation. Centering under the
semicircle law gives the exact covariance kernel `1/(pq-1)`.
-/

open MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Prime-to-semicircle likelihood ratio in the spectral coordinate. -/
def kestenLikelihood (p : Nat.Primes) (x : ℝ) : ℝ :=
  kestenBetaWeight p (heckeSquareCoordinate x)

/-- The positive clamped likelihood is continuous on the real line. -/
theorem continuous_kestenLikelihood (p : Nat.Primes) : Continuous (kestenLikelihood p) :=
  (continuous_kestenBetaWeight p).comp continuous_heckeSquareCoordinate

/-- Every likelihood is strictly positive, including off the spectral interval. -/
theorem kestenLikelihood_pos (p : Nat.Primes) (x : ℝ) : 0 < kestenLikelihood p x :=
  kestenBetaWeight_pos p _

/-- Every likelihood is integrable under every prime law. -/
theorem integrable_kestenLikelihood (p q : Nat.Primes) :
    Integrable (kestenLikelihood p) (kestenSpectralLaw q : Measure ℝ) :=
  integrable_kestenSpectralLaw_continuous q ⟨_, continuous_kestenLikelihood p⟩

/-- Every likelihood is integrable under the semicircle law. -/
theorem integrable_semicircleLikelihood (p : Nat.Primes) :
    Integrable (kestenLikelihood p) (semicircleSpectralLaw : Measure ℝ) :=
  integrable_semicircleSpectralLaw_continuous ⟨_, continuous_kestenLikelihood p⟩

/-- The charged local factor is continuous throughout the parameterized open disk. -/
theorem continuous_phaseLocalFactor (s : ℝ) : Continuous (phaseLocalFactor s) := by
  unfold phaseLocalFactor
  apply Continuous.inv₀ (by fun_prop)
  intro t
  exact (poissonKer_denom_pos (abs_cavityDiskCoordinate_lt_one s) _).ne'

/-- Reflection averaging the charged factor produces an even Poisson denominator. -/
theorem phaseLocalFactor_reflection_mean (s t : ℝ) :
    (phaseLocalFactor s t + phaseLocalFactor s (1 - t)) / 2 =
      (1 + cavityDiskCoordinate s ^ 2) /
        (1 - 2 * cavityDiskCoordinate s ^ 2 * Real.cos (2 * Real.pi * t) +
          (cavityDiskCoordinate s ^ 2) ^ 2) := by
  have hr := abs_cavityDiskCoordinate_lt_one s
  have ha := poissonKer_denom_pos hr (Real.pi * t)
  have hb := poissonKer_denom_pos hr (Real.pi * (1 - t))
  have hc : Real.cos (Real.pi * (1 - t)) = -Real.cos (Real.pi * t) := by
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.cos_pi_sub]
  rw [hc] at hb
  unfold phaseLocalFactor
  rw [hc, show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
  have he : (1 - 2 * cavityDiskCoordinate s * Real.cos (Real.pi * t) + cavityDiskCoordinate s ^ 2) *
      (1 - 2 * cavityDiskCoordinate s * -Real.cos (Real.pi * t) + cavityDiskCoordinate s ^ 2) =
        1 - 2 * cavityDiskCoordinate s ^ 2 * (2 * Real.cos (Real.pi * t) ^ 2 - 1) +
          (cavityDiskCoordinate s ^ 2) ^ 2 := by ring
  simp only [← one_div]
  rw [div_add_div 1 1 ha.ne' hb.ne', he]
  ring

/-- The prime likelihood is a reflection average at inverse square-root prime fugacity. -/
theorem kestenLikelihood_phase_local_factor (p : Nat.Primes) (t : ℝ) :
    kestenLikelihood p (2 * Real.cos (Real.pi * t)) =
      (phaseLocalFactor (primeSquareRootDiskParameter p) t +
        phaseLocalFactor (primeSquareRootDiskParameter p) (1 - t)) / 2 := by
  rw [phaseLocalFactor_reflection_mean, cavityDiskCoordinate_prime_sqrt_square]
  exact kestenBetaWeight_phase_rational p t

/-- Every mixed likelihood expectation is a geometric resolvent. -/
theorem integral_kestenLikelihood_cross (p q : Nat.Primes) :
    (∫ x, kestenLikelihood p x ∂(kestenSpectralLaw q : Measure ℝ)) =
      (1 - ((p : ℝ) * (q : ℝ))⁻¹)⁻¹ := by
  have h := integral_kestenSpectralLaw q ⟨_, continuous_kestenLikelihood p⟩
  change (∫ x, kestenLikelihood p x ∂(kestenSpectralLaw q : Measure ℝ)) =
    ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity q t *
      kestenLikelihood p (2 * Real.cos (Real.pi * t)) at h
  rw [h]
  have he (t : ℝ) : kestenMcKayDensity q t *
      kestenLikelihood p (2 * Real.cos (Real.pi * t)) =
      (kestenMcKayDensity q t * phaseLocalFactor (primeSquareRootDiskParameter p) t +
        kestenMcKayDensity q t * phaseLocalFactor (primeSquareRootDiskParameter p) (1 - t)) / 2 := by
    rw [kestenLikelihood_phase_local_factor]
    ring
  simp_rw [he]
  have hi : IntegrableOn (fun t => kestenMcKayDensity q t *
      phaseLocalFactor (primeSquareRootDiskParameter p) t) (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenMcKayDensity q).mul
      (continuous_phaseLocalFactor _)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hj : IntegrableOn (fun t => kestenMcKayDensity q t *
      phaseLocalFactor (primeSquareRootDiskParameter p) (1 - t)) (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenMcKayDensity q).mul
      ((continuous_phaseLocalFactor _).comp (by fun_prop))).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
  rw [integral_div, integral_add hi hj, integral_kesten_reflection, integral_kesten_local_factor,
    cavityDiskCoordinate_prime_sqrt_square]
  have heq : (p : ℝ)⁻¹ / (q : ℝ) = ((p : ℝ) * (q : ℝ))⁻¹ := by ring
  rw [heq]
  ring

/-- Multiplying a continuous observable by the likelihood changes semicircle to prime expectation. -/
theorem integral_semicircleLikelihood_mul (p : Nat.Primes) (f : C(ℝ, ℝ)) :
    (∫ x, kestenLikelihood p x * f x ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, f x ∂(kestenSpectralLaw p : Measure ℝ) := by
  have h := integral_semicircleSpectralLaw
    ⟨fun x => kestenLikelihood p x * f x, (continuous_kestenLikelihood p).mul f.continuous⟩
  change (∫ x, kestenLikelihood p x * f x ∂(semicircleSpectralLaw : Measure ℝ)) =
    ∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t *
      (kestenLikelihood p (2 * Real.cos (Real.pi * t)) * f (2 * Real.cos (Real.pi * t))) at h
  rw [h, integral_kestenSpectralLaw p f]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change semicirclePhaseDensity t *
      (kestenLikelihood p (2 * Real.cos (Real.pi * t)) * f (2 * Real.cos (Real.pi * t))) =
        kestenMcKayDensity p t * f (2 * Real.cos (Real.pi * t))
    rw [← mul_assoc]
    change (semicirclePhaseDensity t *
      kestenBetaWeight p (heckeSquareCoordinate (2 * Real.cos (Real.pi * t)))) * _ = _
    rw [kestenBetaWeight_phase]

/-- Every prime likelihood has semicircle mean one. -/
theorem integral_semicircleLikelihood (p : Nat.Primes) :
    (∫ x, kestenLikelihood p x ∂(semicircleSpectralLaw : Measure ℝ)) = 1 := by
  have h := integral_semicircleLikelihood_mul p ⟨fun _ => 1, continuous_const⟩
  simpa using h

/-- The uncentered likelihood Gram kernel is the geometric resolvent. -/
theorem integral_semicircleLikelihood_mul_likelihood (p q : Nat.Primes) :
    (∫ x, kestenLikelihood p x * kestenLikelihood q x ∂(semicircleSpectralLaw : Measure ℝ)) =
      (1 - ((p : ℝ) * (q : ℝ))⁻¹)⁻¹ := by
  have h := integral_semicircleLikelihood_mul p ⟨_, continuous_kestenLikelihood q⟩
  change (∫ x, kestenLikelihood p x * kestenLikelihood q x
    ∂(semicircleSpectralLaw : Measure ℝ)) =
      ∫ x, kestenLikelihood q x ∂(kestenSpectralLaw p : Measure ℝ) at h
  rw [h, integral_kestenLikelihood_cross, mul_comm (q : ℝ) (p : ℝ)]

/-- Centered likelihood covariance is exactly the multiplicative Cauchy kernel. -/
theorem integral_semicircleLikelihood_centered_mul (p q : Nat.Primes) :
    (∫ x, (kestenLikelihood p x - 1) * (kestenLikelihood q x - 1)
      ∂(semicircleSpectralLaw : Measure ℝ)) = ((p : ℝ) * (q : ℝ) - 1)⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hq : 1 < (q : ℝ) := by exact_mod_cast q.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hp])
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (by linarith only [hq])
  have hd : (p : ℝ) * (q : ℝ) - 1 ≠ 0 := by
    have h := mul_lt_mul_of_pos_left hq (show 0 < (p : ℝ) by linarith only [hp])
    nlinarith only [h, hp]
  have hi := integrable_semicircleLikelihood p
  have hj := integrable_semicircleLikelihood q
  have hij : Integrable (fun x => kestenLikelihood p x * kestenLikelihood q x)
      (semicircleSpectralLaw : Measure ℝ) := integrable_semicircleSpectralLaw_continuous
    ⟨fun x => kestenLikelihood p x * kestenLikelihood q x,
      (continuous_kestenLikelihood p).mul (continuous_kestenLikelihood q)⟩
  have he (x : ℝ) : (kestenLikelihood p x - 1) * (kestenLikelihood q x - 1) =
      (kestenLikelihood p x * kestenLikelihood q x - kestenLikelihood p x) -
        kestenLikelihood q x + 1 := by ring
  simp_rw [he]
  rw [integral_add
      (f := fun x => kestenLikelihood p x * kestenLikelihood q x - kestenLikelihood p x - kestenLikelihood q x)
      (g := fun _ => 1) ((hij.sub hi).sub hj) (integrable_const 1),
    integral_sub (f := fun x => kestenLikelihood p x * kestenLikelihood q x - kestenLikelihood p x)
      (g := kestenLikelihood q) (hij.sub hi) hj, integral_sub hij hi,
    integral_semicircleLikelihood_mul_likelihood, integral_semicircleLikelihood,
    integral_semicircleLikelihood]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp [hp0, hq0, hd]
  ring

/-- The squared likelihood distance to semicircle is the diagonal Cauchy kernel. -/
theorem integral_semicircleLikelihood_centered_sq (p : Nat.Primes) :
    (∫ x, (kestenLikelihood p x - 1) ^ 2 ∂(semicircleSpectralLaw : Measure ℝ)) =
      ((p : ℝ) ^ 2 - 1)⁻¹ := by
  simpa only [pow_two] using integral_semicircleLikelihood_centered_mul p p

end
end GaloisForLFunctions.SelbergClass.Primon
