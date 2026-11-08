import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodHardy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


/-!
# Chebyshev characters in the semicircle Hilbert space

The second-kind characters `Uₙ(x/2)` are orthonormal for the actual
semicircle law. Their prime expectations are `p⁻ᵐ` in degree `2m` and zero
in odd degree. Multiplying by the likelihood turns these expectations into
exact Hilbert coefficients of each prime density.
-/

open MeasureTheory Set
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Second-kind Chebyshev character in the normalized spectral coordinate. -/
def spectralCharacter (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x => (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / 2), by fun_prop⟩

/-- The spectral character agrees with its phase realization. -/
theorem spectralCharacter_phase (n : ℕ) (t : ℝ) :
    spectralCharacter n (2 * Real.cos (Real.pi * t)) = phaseCharacter n t := by
  change (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval ((2 * Real.cos (Real.pi * t)) / 2) = _
  rw [show (2 * Real.cos (Real.pi * t)) / 2 = Real.cos (Real.pi * t) by ring]
  rfl

/-- Integer-frequency cosines have zero mean unless their frequency vanishes. -/
private theorem integral_phase_integer_cos (n : ℤ) :
    (∫ t in Ioo (0 : ℝ) 1, Real.cos ((n : ℝ) * Real.pi * t)) =
      if n = 0 then 1 else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, intervalIntegral.integral_comp_mul_left _
      (mul_ne_zero (Int.cast_ne_zero.mpr hn) Real.pi_ne_zero)]
    simp only [mul_zero, mul_one, integral_cos,
      Real.sin_int_mul_pi, Real.sin_zero, sub_self, smul_zero]

/-- The character times the Weyl sine factor is a single sine mode. -/
private theorem phaseCharacter_sine (n : ℕ) (t : ℝ) :
    phaseCharacter n t * Real.sin (Real.pi * t) =
      Real.sin (((n : ℝ) + 1) * (Real.pi * t)) := by
  simpa only [phaseCharacter, Int.cast_natCast] using
    Polynomial.Chebyshev.U_real_cos (Real.pi * t) (n : ℤ)

/-- The semicircle weight converts a character product to two cosine modes. -/
private theorem phaseCharacter_weighted_product (n m : ℕ) (t : ℝ) :
    semicirclePhaseDensity t * (phaseCharacter n t * phaseCharacter m t) =
      Real.cos ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * Real.pi * t) -
      Real.cos ((((n : ℤ) + (m : ℤ) + 2 : ℤ) : ℝ) * Real.pi * t) := by
  calc
    _ = 2 * (phaseCharacter n t * Real.sin (Real.pi * t)) *
        (phaseCharacter m t * Real.sin (Real.pi * t)) := by
      unfold semicirclePhaseDensity
      ring
    _ = 2 * Real.sin (((n : ℝ) + 1) * (Real.pi * t)) *
        Real.sin (((m : ℝ) + 1) * (Real.pi * t)) := by
      rw [phaseCharacter_sine, phaseCharacter_sine]
    _ = _ := by
      have hs : ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * Real.pi * t) =
          ((n : ℝ) + 1) * (Real.pi * t) - ((m : ℝ) + 1) * (Real.pi * t) := by
        push_cast
        ring
      have ha : ((((n : ℤ) + (m : ℤ) + 2 : ℤ) : ℝ) * Real.pi * t) =
          ((n : ℝ) + 1) * (Real.pi * t) + ((m : ℝ) + 1) * (Real.pi * t) := by
        push_cast
        ring
      rw [hs, ha, Real.cos_sub, Real.cos_add]
      ring

/-- Exact orthogonality of second-kind characters under the actual semicircle law. -/
theorem integral_spectralCharacter_mul (n m : ℕ) :
    (∫ x, spectralCharacter n x * spectralCharacter m x
      ∂(semicircleSpectralLaw : Measure ℝ)) = if n = m then 1 else 0 := by
  have h := integral_semicircleSpectralLaw (spectralCharacter n * spectralCharacter m)
  change (∫ x, spectralCharacter n x * spectralCharacter m x
      ∂(semicircleSpectralLaw : Measure ℝ)) =
    ∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t *
      (spectralCharacter n (2 * Real.cos (Real.pi * t)) *
       spectralCharacter m (2 * Real.cos (Real.pi * t))) at h
  rw [h]
  simp_rw [spectralCharacter_phase, phaseCharacter_weighted_product]
  have hi (k : ℤ) : IntegrableOn
      (fun t : ℝ => Real.cos ((k : ℝ) * Real.pi * t)) (Ioo 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k : ℝ) * Real.pi * t))).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [integral_sub (hi _) (hi _), integral_phase_integer_cos, integral_phase_integer_cos,
    if_neg (by omega : (n : ℤ) + (m : ℤ) + 2 ≠ 0), sub_zero]
  have hnm : (n : ℤ) - (m : ℤ) = 0 ↔ n = m := by omega
  simp only [hnm]

/-- Every even character has the geometric prime expectation. -/
theorem integral_kesten_spectralCharacter_even (p : Nat.Primes) (n : ℕ) :
    (∫ x, spectralCharacter (2 * n) x ∂(kestenSpectralLaw p : Measure ℝ)) =
      (p : ℝ)⁻¹ ^ n := by
  rw [integral_kestenSpectralLaw]
  simp_rw [spectralCharacter_phase]
  exact phaseCharacterAverage_even p n

/-- Every odd character has zero prime expectation. -/
theorem integral_kesten_spectralCharacter_odd (p : Nat.Primes) (n : ℕ) :
    (∫ x, spectralCharacter (2 * n + 1) x ∂(kestenSpectralLaw p : Measure ℝ)) = 0 := by
  rw [integral_kestenSpectralLaw]
  simp_rw [spectralCharacter_phase]
  exact phaseCharacterAverage_odd p n

/-- The continuous character represented in semicircle `L²`. -/
def spectralCharacterVector (n : ℕ) : SemicircleL2 :=
  semicircleL2Observable (spectralCharacter n)

/-- The character vectors have the identity Gram matrix. -/
theorem inner_spectralCharacterVector (n m : ℕ) :
    inner ℝ (spectralCharacterVector n) (spectralCharacterVector m) =
      if n = m then 1 else 0 := by
  rw [spectralCharacterVector, spectralCharacterVector, inner_semicircleL2Observable,
    integral_spectralCharacter_mul]

/-- All spectral characters form an orthonormal family. -/
theorem orthonormal_spectralCharacterVector : Orthonormal ℝ spectralCharacterVector :=
  orthonormal_iff_ite.mpr inner_spectralCharacterVector

/-- The even Hilbert coefficients of the prime likelihood are reciprocal-prime powers. -/
theorem inner_likelihood_spectralCharacter_even (p : Nat.Primes) (n : ℕ) :
    inner ℝ (kestenLikelihoodVector p) (spectralCharacterVector (2 * n)) =
      (p : ℝ)⁻¹ ^ n := by
  rw [kestenLikelihoodVector, spectralCharacterVector, inner_semicircleL2Observable]
  change (∫ x, kestenLikelihood p x * spectralCharacter (2 * n) x
    ∂(semicircleSpectralLaw : Measure ℝ)) = _
  rw [integral_semicircleLikelihood_mul, integral_kesten_spectralCharacter_even]

/-- The prime likelihood has no odd Hilbert coefficients. -/
theorem inner_likelihood_spectralCharacter_odd (p : Nat.Primes) (n : ℕ) :
    inner ℝ (kestenLikelihoodVector p) (spectralCharacterVector (2 * n + 1)) = 0 := by
  rw [kestenLikelihoodVector, spectralCharacterVector, inner_semicircleL2Observable]
  change (∫ x, kestenLikelihood p x * spectralCharacter (2 * n + 1) x
    ∂(semicircleSpectralLaw : Measure ℝ)) = _
  rw [integral_semicircleLikelihood_mul, integral_kesten_spectralCharacter_odd]

end
end GaloisForLFunctions.SelbergClass.Primon

