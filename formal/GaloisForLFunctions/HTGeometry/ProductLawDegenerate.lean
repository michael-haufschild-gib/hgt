import GaloisForLFunctions.HTGeometry.ProductLawBorderedRows
import GaloisForLFunctions.HTGeometry.ScaledLogWronskian

/-!
# The degenerate locus: powers of the terminal factor

On the locus where each factor is a constant times a power of its terminal factor,
`Q_j = K_j·v_j^(e_j)`, the terminal factor cancels out of the logarithmic sum:

`(Q_j'/Q_j)(X_j)·δX_j = e_j·v_j'(X_j)·∏_(i<j)Q_i(X_i)`,

free of the `j`-th coordinate.  That is exactly the cancellation the exponential tower enjoys — there
`Q = v = X` and `e = 1` — and it removes every denominator from the logarithmic sum, so on this locus
the whole model is polynomial again.

The locus is not small: it is where the cascade's maps are `d + c·exp(A(w))` with `A' = K(w − d)^(e−1)`,
and it contains the tower.  Off it the scaled logarithmic derivative is nonconstant, which is the
second-order regime.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- **The cancellation on the degenerate locus.**  A pure power of the terminal factor contributes to
the logarithmic sum a term free of its own coordinate. -/
theorem logFactor_mul_prodJet_of_pow {K : ℂ} (hK : K ≠ 0) {e j : ℕ}
    (hvj : v j ≠ 0) (hQj : Q j = Polynomial.C K * (v j) ^ (e + 1)) :
    logFactor (Q j) j * prodJet Q v j
      = fact (Polynomial.C ((e : ℂ) + 1) * (v j).derivative) j * prodHead Q j := by
  have hfv : fact (v j) j ≠ 0 := fact_ne_zero hvj j
  have hfK : fact (Polynomial.C K) j = algebraMap ℂ CascadeField K := fact_C K j
  have hKne : (algebraMap ℂ CascadeField K) ≠ 0 := by
    simpa using hK
  have hder : (Q j).derivative
      = Polynomial.C K * (Polynomial.C ((e : ℂ) + 1) * (v j) ^ e * (v j).derivative) := by
    rw [hQj, Polynomial.derivative_C_mul, Polynomial.derivative_pow]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [logFactor, prodJet_eq, hder, hQj]
  simp only [fact_mul, fact_pow, fact_C]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
