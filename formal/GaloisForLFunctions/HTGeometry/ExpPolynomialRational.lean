import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# The exponential of a polynomial is rational only when it is constant

If `G · exp(T) = Q` holds identically for polynomials `G ≠ 0`, `Q ≠ 0` and `T`, then `T` is
constant.  The proof is purely algebraic: differentiating the identity and clearing the
exponential leaves the polynomial identity

`(G' + G T') · Q = G · Q'`,

whose two sides have incompatible degrees unless `T' = 0`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex Polynomial

/-- The polynomial identity obtained by eliminating the exponential. -/
theorem expPolynomial_ratio_identity {G Q T : Polynomial ℂ}
    (h : ∀ z : ℂ, G.eval z * Complex.exp (T.eval z) = Q.eval z) :
    (derivative G + G * derivative T) * Q = G * derivative Q := by
  refine Polynomial.funext (fun z => ?_)
  have hT : HasDerivAt (fun x => T.eval x) ((derivative T).eval z) z := T.hasDerivAt z
  have hG : HasDerivAt (fun x => G.eval x) ((derivative G).eval z) z := G.hasDerivAt z
  have hQ : HasDerivAt (fun x => Q.eval x) ((derivative Q).eval z) z := Q.hasDerivAt z
  have hexp : HasDerivAt (fun x => Complex.exp (T.eval x))
      (Complex.exp (T.eval z) * (derivative T).eval z) z := hT.cexp
  have hLHS : HasDerivAt (fun x => G.eval x * Complex.exp (T.eval x))
      ((derivative G).eval z * Complex.exp (T.eval z)
        + G.eval z * (Complex.exp (T.eval z) * (derivative T).eval z)) z := hG.mul hexp
  rw [funext h] at hLHS
  have hder := hLHS.unique hQ
  have hbase := h z
  simp only [Polynomial.eval_mul, Polynomial.eval_add]
  linear_combination G.eval z * hder
    - ((derivative G).eval z + G.eval z * (derivative T).eval z) * hbase

/-- **A rational exponential is constant.**  If `G · exp T = Q` identically with `G` and `Q`
nonzero polynomials, then the polynomial exponent `T` is constant. -/
theorem derivative_eq_zero_of_expPolynomial_eq_ratio {G Q T : Polynomial ℂ}
    (hG : G ≠ 0) (hQ : Q ≠ 0)
    (h : ∀ z : ℂ, G.eval z * Complex.exp (T.eval z) = Q.eval z) :
    derivative T = 0 := by
  by_contra hT
  have hid := expPolynomial_ratio_identity h
  set N : Polynomial ℂ := derivative G + G * derivative T with hN
  -- the degree of `N`
  have hGT : (G * derivative T).natDegree = G.natDegree + (derivative T).natDegree :=
    Polynomial.natDegree_mul hG hT
  have hGTne : G * derivative T ≠ 0 := mul_ne_zero hG hT
  have hmain : N.natDegree = G.natDegree + (derivative T).natDegree ∧ N ≠ 0 := by
    by_cases hdG : derivative G = 0
    · have hNeq : N = G * derivative T := by rw [hN, hdG, zero_add]
      exact ⟨by rw [hNeq, hGT], by rw [hNeq]; exact hGTne⟩
    · have hGpos : 0 < G.natDegree := by
        rcases Nat.eq_zero_or_pos G.natDegree with h0 | h0
        · rw [Polynomial.natDegree_eq_zero] at h0
          obtain ⟨c, rfl⟩ := h0
          exact absurd Polynomial.derivative_C hdG
        · exact h0
      have hlt : (derivative G).natDegree < (G * derivative T).natDegree := by
        have := Polynomial.natDegree_derivative_lt (p := G) (by omega)
        omega
      refine ⟨?_, ?_⟩
      · rw [hN, Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt, hGT]
      · intro h0
        rw [hN] at h0
        have hneg : G * derivative T = -derivative G := by linear_combination h0
        rw [hneg, Polynomial.natDegree_neg] at hlt
        omega
  obtain ⟨hNdeg, hNne⟩ := hmain
  -- compare degrees on the two sides of the identity
  have hleft : (N * Q).natDegree = G.natDegree + (derivative T).natDegree + Q.natDegree := by
    rw [Polynomial.natDegree_mul hNne hQ, hNdeg]
  by_cases hdQ : derivative Q = 0
  · rw [hdQ, mul_zero] at hid
    exact (mul_ne_zero hNne hQ) hid
  · have hright : (G * derivative Q).natDegree = G.natDegree + (derivative Q).natDegree :=
      Polynomial.natDegree_mul hG hdQ
    have hQdeg : Q.natDegree ≠ 0 := by
      intro h0
      rw [Polynomial.natDegree_eq_zero] at h0
      obtain ⟨c, rfl⟩ := h0
      exact hdQ (Polynomial.derivative_C)
    have hlt : (derivative Q).natDegree < Q.natDegree :=
      Polynomial.natDegree_derivative_lt hQdeg
    rw [hid, hright] at hleft
    omega

end GaloisForLFunctions.HTGeometry
