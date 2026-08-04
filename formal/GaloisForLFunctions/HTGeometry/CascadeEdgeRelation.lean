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

/-! ## The edge relation without a nonvanishing hypothesis

Clearing the chain-rule denominator does not in fact need the previous state's derivative to be
nonzero.  Each term of the cleared sum equals the corresponding term of the grouped sum times
`(F_k')^e`, by the chain rule alone — the division is only apparent. -/

/-- **Clearing without division.**  A vanishing polynomial in `u` yields a vanishing homogenised
polynomial in `u t` and `t`, for every `t`. -/
theorem sum_mul_pow_chain {A : ℕ → ℂ} {d : ℕ} {u t : ℂ}
    (h : ∑ c ∈ Finset.range (d + 1), A c * u ^ c = 0) :
    ∑ c ∈ Finset.range (d + 1), A c * (u * t) ^ c * t ^ (d - c) = 0 := by
  have hterm : ∀ c ∈ Finset.range (d + 1),
      A c * (u * t) ^ c * t ^ (d - c) = (A c * u ^ c) * t ^ d := by
    intro c hc
    have hcd : c ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    have hsplit : t ^ d = t ^ c * t ^ (d - c) := by
      rw [← pow_add]
      congr 1
      omega
    rw [mul_pow, hsplit]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, h, zero_mul]

/-- **The cleared cascade relation, unconditionally.** -/
theorem cascade_relation_cleared_of_forall {f : ℕ → ℂ → ℂ} {A : ℕ → ℂ} {d n : ℕ} {z : ℂ}
    (hf : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (h : ∑ c ∈ Finset.range (d + 1), A c * (deriv (f n) (entireCascade f n z)) ^ c = 0) :
    ∑ c ∈ Finset.range (d + 1),
        A c * (deriv (entireCascade f (n + 1)) z) ^ c
          * (deriv (entireCascade f n) z) ^ (d - c) = 0 := by
  rw [deriv_entireCascade_succ hf n z]
  exact sum_mul_pow_chain h

/-- **The edge relation, valid at every point.**  No hypothesis on the previous state's derivative
is needed. -/
theorem exists_cascade_edge_relation_of_forall {f : ℕ → ℂ → ℂ} {k : ℕ}
    (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hft : TranscendentalEntire (f k))
    (h1 : DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∃ (e : ℕ) (B : ℕ → MvPolynomial (Fin 2) ℂ), 1 ≤ e ∧ B e ≠ 0 ∧
      ∀ z : ℂ,
        ∑ c ∈ Finset.range (e + 1),
          MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] (B c)
            * (deriv (entireCascade f (k + 1)) z) ^ c
            * (deriv (entireCascade f k) z) ^ (e - c) = 0 := by
  obtain ⟨e, B, he, hBe, hrel⟩ := exists_deriv_top_relation_of_order_one hft h1
  refine ⟨e, B, he, hBe, ?_⟩
  intro z
  refine cascade_relation_cleared_of_forall
    (A := fun c => MvPolynomial.eval ![entireCascade f k z, entireCascade f (k + 1) z] (B c))
    hfan ?_
  exact hrel (entireCascade f k z)

end GaloisForLFunctions.HTGeometry
