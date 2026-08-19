import GaloisForLFunctions.HTGeometry.ComplexShiftJetFieldDatum
import GaloisForLFunctions.HTGeometry.GammaShiftTubeDatumAlgebra

/-!
# The boundary datum of a quotient in the complex-shifted polygamma field

An element of the field generated over `ℂ(s)` by digamma jets at pairwise incongruent complex shifts
is a quotient of two nonzero jet polynomials with polynomial coefficients, and tube data divide.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- **The boundary datum of a nonzero element of the complex-shifted polygamma field.** -/
theorem exists_hasShiftTubeDatum_jetFieldQuotientC (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {Mm : ℕ} (idx : Fin Mm → Fin r × ℕ) (hinj : Function.Injective idx)
    {P Q : MvPolynomial (Fin Mm) (Polynomial ℂ)} (hP : P ≠ 0) (hQ : Q ≠ 0) {M : ℝ} (hM : 0 < M) :
    ∃ (a b : ℤ) (c : ℂ), c ≠ 0 ∧
      HasShiftTubeDatum M 0
        (fun σ t => jetFieldPolyFunC lam idx P ((σ : ℂ) + (t : ℂ) * Complex.I)
          / jetFieldPolyFunC lam idx Q ((σ : ℂ) + (t : ℂ) * Complex.I)) 0 ((a : ℝ)) b c := by
  obtain ⟨a₁, b₁, c₁, hc₁, hd₁⟩ :=
    exists_hasShiftTubeDatum_jetFieldPolyFunC lam hincong idx hinj hP hM
  obtain ⟨a₂, b₂, c₂, hc₂, hd₂⟩ :=
    exists_hasShiftTubeDatum_jetFieldPolyFunC lam hincong idx hinj hQ hM
  refine ⟨a₁ - a₂, b₁ - b₂, c₁ / c₂, div_ne_zero hc₁ hc₂, ?_⟩
  have hdiv := hd₁.div (le_refl (0 : ℝ)) hd₂
  have hcast : ((a₁ - a₂ : ℤ) : ℝ) = (a₁ : ℝ) - (a₂ : ℝ) := by push_cast; ring
  rw [hcast]
  simpa using hdiv

end

end GaloisForLFunctions.HTGeometry
