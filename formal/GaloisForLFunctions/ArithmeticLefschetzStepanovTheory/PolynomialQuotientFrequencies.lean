import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialUnitOrbit
import GaloisForLFunctions.HTGeometry.BohrProductSpectrum

/-!
# Frequencies of polynomial quotients

Bohr coefficients recover every polynomial coefficient on the prime orbit.
A character represented as a polynomial quotient therefore has a frequency
in the signed prime-frequency lattice.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
variable {P : Finset Nat.Primes}

/-- Prime-orbit evaluation respects polynomial multiplication. -/
theorem complexOrbitValue_mul (F G : MvPolynomial P ℂ) (t : ℝ) :
    complexOrbitValue (F * G) t = complexOrbitValue F t * complexOrbitValue G t :=
  map_mul (MvPolynomial.eval (orbitPoint P t)) F G

/-- A polynomial coefficient is recovered by averaging its prime character. -/
theorem bohrCoefficient_complexOrbitValue (F : MvPolynomial P ℂ) (α : P →₀ ℕ) :
    bohrCoefficient (complexOrbitValue F) (-frequency α) = F.coeff α := by
  classical
  have hfun : complexOrbitValue F =
      fun t => ∑ β ∈ F.support, F.coeff β * expChar (-frequency β) t :=
    funext (complexOrbitValue_eq_wave F)
  rw [hfun, bohrCoefficient_sum_expChar]
  simp only [neg_inj, frequency_injective.eq_iff, sum_ite_eq']
  by_cases hα : F.coeff α = 0 <;> simp [MvPolynomial.mem_support_iff, hα]

/-- Restriction to the prime orbit loses no polynomial information. -/
theorem complexOrbitValue_injective : Function.Injective (complexOrbitValue (P := P)) := by
  intro F G h
  ext α
  have hcoef := congrArg (fun f : ℝ → ℂ => bohrCoefficient f (-frequency α)) h
  simpa only [bohrCoefficient_complexOrbitValue] using hcoef

/-- A character which is a polynomial quotient has a frequency in the
signed prime-frequency lattice. -/
theorem polynomial_quotient_character_frequency
    (N D : MvPolynomial P ℂ) (c : ℂ) (γ : ℝ) (hc : c ≠ 0)
    (hD : D ≠ 0)
    (h : ∀ t, complexOrbitValue N t = c * expChar γ t * complexOrbitValue D t) :
    ∃ α β : P →₀ ℕ, γ = frequency α - frequency β := by
  classical
  have hDs : D.support.Nonempty := by
    by_contra he
    have hs : D.support = ∅ := not_nonempty_iff_eq_empty.mp he
    apply hD
    conv_lhs => rw [MvPolynomial.as_sum D]
    rw [hs, sum_empty]
  obtain ⟨α, hα⟩ := hDs
  have hcα : c * D.coeff α ≠ 0 := mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hα)
  have hfun : complexOrbitValue N =
      fun t => complexOrbitValue (MvPolynomial.C c * D) t * expChar γ t := by
    funext t
    rw [h t]
    simp only [complexOrbitValue, map_mul, MvPolynomial.eval_C]
    ring
  have hcoef : bohrCoefficient (complexOrbitValue N) (γ - frequency α) =
      c * D.coeff α := by
    rw [hfun, bohrCoefficient_mul_expChar,
      show γ - frequency α - γ = -frequency α by ring,
      bohrCoefficient_complexOrbitValue, MvPolynomial.coeff_C_mul]
  have hNfun : complexOrbitValue N =
      fun t => ∑ β ∈ N.support, N.coeff β * expChar (-frequency β) t :=
    funext (complexOrbitValue_eq_wave N)
  rw [hNfun, bohrCoefficient_sum_expChar] at hcoef
  have hβ : ∃ β ∈ N.support, -frequency β = γ - frequency α := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ β ∈ N.support,
        if -frequency β = γ - frequency α then N.coeff β else 0) = 0 := by
      apply sum_eq_zero
      intro β hβ
      exact if_neg (hnone β hβ)
    rw [hz] at hcoef
    exact hcα hcoef.symm
  obtain ⟨β, _, hβ⟩ := hβ
  exact ⟨α, β, by linarith⟩

#print axioms polynomial_quotient_character_frequency
end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
