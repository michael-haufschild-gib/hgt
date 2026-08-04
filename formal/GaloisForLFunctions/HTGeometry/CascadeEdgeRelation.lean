import GaloisForLFunctions.HTGeometry.FirstOrderDerivativeDegree

/-!
# The edge relation of a cascade

Each constituent's first-order equation, read in the derivative and evaluated at the previous state,
becomes a polynomial relation between two consecutive states and their derivatives.  The relation is
genuinely of positive degree in the new state's derivative, and its top coefficient is a nonzero
two-variable polynomial.

This is the algebraic content of one edge of the cascade: no reference to the constituent survives,
only the two states and their first derivatives.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open MvPolynomial

/-- **The edge relation.**  For a transcendental entire constituent with a first-order equation, the
two consecutive states satisfy

`∑_{c ≤ e} B_c(F_k, F_{k+1}) (F_{k+1}')^c (F_k')^{e-c} = 0`

wherever `F_k'` does not vanish, with `e ≥ 1` and `B_e` a nonzero two-variable polynomial. -/
theorem exists_cascade_edge_relation {f : ℕ → ℂ → ℂ} {k : ℕ}
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hft : TranscendentalEntire (f k))
    (h1 : DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∃ (e : ℕ) (B : ℕ → MvPolynomial (Fin 2) ℂ), 1 ≤ e ∧ B e ≠ 0 ∧
      ∀ z : ℂ, deriv (entireCascade f k) z ≠ 0 →
        ∑ c ∈ Finset.range (e + 1),
          MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] (B c)
            * (deriv (entireCascade f (k + 1)) z) ^ c
            * (deriv (entireCascade f k) z) ^ (e - c) = 0 := by
  obtain ⟨e, B, he, hBe, hrel⟩ := exists_deriv_top_relation_of_order_one hft h1
  refine ⟨e, B, he, hBe, ?_⟩
  intro z hz
  refine cascade_relation_cleared
    (A := fun c => MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] (B c))
    hfan hz ?_
  exact hrel (entireCascade f k z)

end GaloisForLFunctions.HTGeometry
