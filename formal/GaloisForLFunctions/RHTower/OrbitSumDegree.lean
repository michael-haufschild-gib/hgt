import Mathlib

/-!
# Degree bound for the symmetric orbit sum

In the non-monic Lindemann–Weierstrass finish the symmetric orbit sum
`Φ = ∑_S (aeval (∑_{j∈S} X_j) gp)` is evaluated at the (non-integer) conjugates `θ`, and its value is
cleared to an integer by multiplying by `ℓ^{Φ.totalDegree}` (non-monic symmetric integrality).  For
the analytic estimate to converge, that `ℓ`-power must not grow faster than a fixed base to the
`p`-th power, i.e. `Φ.totalDegree` must be linear in `p`.

`orbitSum_totalDegree_le` supplies the needed bound `Φ.totalDegree ≤ gp.natDegree`: substituting the
degree-`≤1` linear form `∑_{j∈S} X_j` into a univariate polynomial `gp` raises the total degree by at
most `gp.natDegree`, and summing over subsets keeps the supremum.  Since `exp_polynomial_approx`
bounds `gp.natDegree ≤ p·(deg f) − 1`, this makes `ℓ^{Φ.totalDegree} ≤ |ℓ|^{p·deg f}`, so the
estimate is `(|ℓ|^{deg f}·B)^p / (p−1)! → 0`.
-/

open MvPolynomial Polynomial Finset

namespace GaloisForLFunctions
namespace RHTower

/-- **Degree bound for the symmetric subset-sum orbit polynomial.**  The orbit sum
`∑_S aeval (∑_{j∈S} X_j) gp` over all subsets `S` has total degree at most `gp.natDegree`:
substituting the degree-`≤1` linear form `∑_{j∈S} X_j` into `gp` raises the total degree by at most
`gp.natDegree`, and the subset sum keeps the supremum. -/
theorem orbitSum_totalDegree_le {d : ℕ} (gp : ℤ[X]) :
    (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        Polynomial.aeval (∑ j ∈ S, MvPolynomial.X (R := ℤ) j) gp).totalDegree ≤ gp.natDegree := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le ?_)
  intro S _
  rw [Polynomial.aeval_eq_sum_range]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le ?_)
  intro i hi
  have hx : (∑ j ∈ S, MvPolynomial.X (R := ℤ) j).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le ?_)
    intro j _; rw [MvPolynomial.totalDegree_X]
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _)
    (le_trans (MvPolynomial.totalDegree_pow _ _) ?_)
  calc i * (∑ j ∈ S, MvPolynomial.X (R := ℤ) j).totalDegree
      ≤ i * 1 := by gcongr
    _ = i := mul_one i
    _ ≤ gp.natDegree := by rw [Finset.mem_range] at hi; omega

end RHTower
end GaloisForLFunctions
