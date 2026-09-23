import GaloisForLFunctions.HTGeometry.GomesPolynomialGaugeRigidity
import GaloisForLFunctions.HTGeometry.FieldOneArchimedeanWeylMultiplier

/-!
# The archimedean Weyl character has no polynomial coordinates

Gomes, arXiv:2607.24901v1, Proposition 2, separates smooth charged characters
from algebraic additive-group characters. The corpus's archimedean Weyl
character gives an existing nontrivial smooth unitary example. Its real and
imaginary parts cannot both be real polynomials. The proof uses the complete
polynomial-circle rigidity theorem, unit modulus, and the existing proof of
nontriviality.
-/

namespace GaloisForLFunctions.HTGeometry.FieldOneCore

/-- No polynomial real coordinates realize the existing archimedean character. -/
theorem fieldOneArchimedeanCharacter_no_polynomial_coordinates :
    ¬ ∃ p q : Polynomial ℝ, ∀ t : ℝ,
      fieldOneArchimedeanCharacter t =
        ((p.eval t : ℝ) : ℂ) + Complex.I * ((q.eval t : ℝ) : ℂ) := by
  rintro ⟨p, q, he⟩
  have hs : ∀ t : ℝ, (p.eval t)^(2 : ℕ) + (q.eval t)^(2 : ℕ) = 1 := by
    intro t
    have hn : Complex.normSq (fieldOneArchimedeanCharacter t) = 1 := by
      change Complex.normSq (fieldOneArchimedeanPhase 1 t) = 1
      rw [Complex.normSq_eq_norm_sq, norm_fieldOneArchimedeanPhase, one_pow]
    rw [he t] at hn
    simpa [Complex.normSq_apply, pow_two] using hn
  obtain ⟨hp, hq, _⟩ := (polynomial_circle_coordinates_iff p q).mp hs
  apply fieldOneArchimedeanCharacter_ne_one
  apply DFunLike.ext
  intro t
  have hc : fieldOneArchimedeanCharacter t = fieldOneArchimedeanCharacter 0 := by
    rw [he t, he 0, hp, hq]
    simp only [Polynomial.eval_C]
  simpa using hc

end GaloisForLFunctions.HTGeometry.FieldOneCore
