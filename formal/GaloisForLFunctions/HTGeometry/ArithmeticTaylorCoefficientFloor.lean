import GaloisForLFunctions.HTGeometry.PopkenCoefficientLowerBound
import GaloisForLFunctions.HTGeometry.IntegerEulerADE

/-!
# Popken's floor for the coefficients of a differentially algebraic series

Mahler's integer normalization, the Euler conversion and Popken's estimate combine: a formal power
series with algebraic coefficients satisfying a nonzero algebraic differential relation has every
nonzero coefficient of modulus at least `exp(-K n (log n)^2)`.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- **Popken's floor.**  Nonzero algebraic Taylor coefficients of a differentially algebraic formal
series are not smaller than `exp(-K n (log n)^2)`. -/
theorem exists_popken_floor_of_formalRelation
    {F : PowerSeries ℂ} (hFalg : ∀ n, IsAlgebraic ℚ (PowerSeries.coeff n F))
    {r : ℕ} {P : MvPolynomial (Fin (r + 2)) ℂ} (hP0 : P ≠ 0)
    (hrel : MvPolynomial.aeval (GaloisForLFunctions.formalJets r F) P = 0) :
    ∃ Kp : ℝ, 0 < Kp ∧ ∀ n : ℕ, 2 ≤ n → PowerSeries.coeff n F ≠ 0 →
      Real.exp (-(Kp * ((n : ℝ) * (Real.log n) ^ 2))) ≤ ‖PowerSeries.coeff n F‖ := by
  classical
  obtain ⟨m, Q, hQ0, hQint, hQsol⟩ :=
    GaloisForLFunctions.exists_integer_jet_relation_of_formalRelation hP0 hrel
  obtain ⟨PZ, hPZ0, hPZan, hPZsol, hPZnd⟩ := exists_integer_euler_ade Q hQ0 hQint hQsol
  obtain ⟨K, ⟨hKfin⟩, hKmem⟩ :=
    coefficientsConfinedToNumberField_of_formalRelation hFalg hP0 hrel
  exact exists_popken_lower_bound PZ hPZ0 hPZan hPZsol hPZnd hKfin hKmem

end GaloisForLFunctions.HTGeometry
