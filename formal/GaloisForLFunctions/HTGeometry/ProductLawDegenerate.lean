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

/-- A factor at another coordinate is killed. -/
theorem fpderiv_fact_of_ne {p : Polynomial ℂ} {j k : ℕ} (h : j ≠ k) :
    fpderiv k (fact p j) = 0 := by
  rw [derivation_fact, fpderiv_fx_of_ne h, mul_zero]

/-- The head product below a coordinate is killed by that coordinate's derivation. -/
theorem fpderiv_prodHead_of_le : ∀ {j k : ℕ}, j ≤ k → fpderiv k (prodHead Q j) = 0 := by
  intro j
  induction j with
  | zero =>
      intro k _
      rw [prodHead_zero]
      exact (fpderiv k).map_one_eq_zero
  | succ j ih =>
      intro k hk
      rw [prodHead_succ, Derivation.leibniz, ih (by omega : j ≤ k),
        fpderiv_fact_of_ne (by omega : j ≠ k)]
      simp

/-- **The logarithmic sum on the degenerate locus.**  Every denominator cancels. -/
theorem logSum_of_pow {K : ℕ → ℂ} {e : ℕ → ℕ}
    (hK : ∀ j, K j ≠ 0) (hv : ∀ j, v j ≠ 0)
    (hQ : ∀ j, Q j = Polynomial.C (K j) * (v j) ^ (e j + 1)) (k : ℕ) :
    logSum Q v k
      = ∑ j ∈ Finset.range k,
          fact (Polynomial.C ((e j : ℂ) + 1) * (v j).derivative) j * prodHead Q j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  exact logFactor_mul_prodJet_of_pow Q v (hK j) (hv j) (hQ j)

/-- **The logarithmic sum avoids the newest coordinate on the degenerate locus.**  Each term involves
only coordinates strictly below its index, because the terminal factor cancelled and the remaining
derivative is a constant. -/
theorem fpderiv_logSum_of_pow {K : ℕ → ℂ} {e : ℕ → ℕ}
    (hK : ∀ j, K j ≠ 0) (hv : ∀ j, v j ≠ 0)
    (hQ : ∀ j, Q j = Polynomial.C (K j) * (v j) ^ (e j + 1))
    (hlin : ∀ j, (v j).derivative.natDegree = 0) (k : ℕ) :
    fpderiv k (logSum Q v (k + 1)) = 0 := by
  rw [logSum_of_pow Q v hK hv hQ, map_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j < k + 1 := Finset.mem_range.mp hj
  rw [Derivation.leibniz, fpderiv_prodHead_of_le Q (by omega : j ≤ k)]
  by_cases hjeq : j = k
  · have hconst : fact (Polynomial.C ((e j : ℂ) + 1) * (v j).derivative) j
        = algebraMap ℂ CascadeField (((e j : ℂ) + 1) * (v j).derivative.coeff 0) := by
      have hd : (v j).derivative = Polynomial.C ((v j).derivative.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero (hlin j)
      conv_lhs => rw [hd]
      rw [← Polynomial.C_mul, fact_C]
    rw [hconst, (fpderiv k).map_algebraMap]
    simp
  · rw [fpderiv_fact_of_ne hjeq]
    simp

end GaloisForLFunctions.HTGeometry
