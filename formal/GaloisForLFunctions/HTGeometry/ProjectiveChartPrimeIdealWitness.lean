import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartIncidenceDimension

/-!
# Prime ideals of the projective chart ring

The chart incidence and base-change theorems carry a prime-ideal instance on the chart coefficient
ring — the largest premise class of the area after the half-plane — and no producer was recorded,
so the layer had no exhibited ideal to run on.

Two are supplied.  The chart ring is a polynomial ring over a field, hence a domain, so the zero
ideal is prime: the generic point.  And every point of the affine chart gives one, as the kernel of
its evaluation map, since the values live in a field.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The zero ideal of the chart ring is prime: the chart ring is a domain. -/
theorem bot_isPrime_projectiveChart {I : Type} (j : I) :
    (⊥ : Ideal (MvPolynomial (projectiveChartVar j) ℂ)).IsPrime :=
  Ideal.isPrime_bot

/-- Every point of the affine chart gives a prime ideal, the kernel of its evaluation map. -/
theorem isPrime_ker_eval_projectiveChart {I : Type} (j : I)
    (z : projectiveChartVar j → ℂ) :
    (RingHom.ker (eval z : MvPolynomial (projectiveChartVar j) ℂ →+* ℂ)).IsPrime :=
  RingHom.ker_isPrime _

/-- Hence the prime-ideal premise of the chart layer is realized. -/
theorem exists_isPrime_projectiveChart {I : Type} (j : I) :
    ∃ p : Ideal (MvPolynomial (projectiveChartVar j) ℂ), p.IsPrime :=
  ⟨⊥, bot_isPrime_projectiveChart j⟩

/-- And realized by a point ideal, not only by the generic one. -/
theorem exists_isPrime_ker_eval_projectiveChart {I : Type} (j : I)
    (z : projectiveChartVar j → ℂ) :
    ∃ p : Ideal (MvPolynomial (projectiveChartVar j) ℂ), p.IsPrime ∧
      p = RingHom.ker (eval z : MvPolynomial (projectiveChartVar j) ℂ →+* ℂ) :=
  ⟨_, isPrime_ker_eval_projectiveChart j z, rfl⟩

end GaloisForLFunctions.HTGeometry
