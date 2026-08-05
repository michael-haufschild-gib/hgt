import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartGlobalIncidenceRing
import GaloisForLFunctions.HTGeometry.ProjectiveChartPrimeIdealWitness

/-!
# Prime ideals of the chart coefficient ring

The base-change layer carries a prime-ideal instance on the chart **coefficient ring**, the same
polynomial ring under its own name.  The generic point and every closed point of the chart give one:
the ring is a domain, so its zero ideal is prime, and the kernel of an evaluation is prime because
its values lie in a field.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The zero ideal of the chart coefficient ring is prime. -/
theorem bot_isPrime_projectiveChartCoefficientRing {I : Type} (j : I) :
    (⊥ : Ideal (projectiveChartCoefficientRing j)).IsPrime :=
  Ideal.isPrime_bot

/-- Every point of the chart gives a prime ideal of the coefficient ring. -/
theorem isPrime_ker_eval_projectiveChartCoefficientRing {I : Type} (j : I)
    (z : projectiveChartVar j → ℂ) :
    (RingHom.ker (eval z : projectiveChartCoefficientRing j →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

/-- Hence the prime-ideal premise of the base-change layer is realized. -/
theorem exists_isPrime_projectiveChartCoefficientRing {I : Type} (j : I) :
    ∃ p : Ideal (projectiveChartCoefficientRing j), p.IsPrime :=
  ⟨⊥, bot_isPrime_projectiveChartCoefficientRing j⟩

/-- And realized by a point ideal, not only by the generic one. -/
theorem exists_isPrime_ker_eval_projectiveChartCoefficientRing {I : Type} (j : I)
    (z : projectiveChartVar j → ℂ) :
    ∃ p : Ideal (projectiveChartCoefficientRing j), p.IsPrime ∧
      p = RingHom.ker (eval z : projectiveChartCoefficientRing j →+* ℂ) :=
  ⟨_, isPrime_ker_eval_projectiveChartCoefficientRing j z, rfl⟩

end GaloisForLFunctions.HTGeometry
