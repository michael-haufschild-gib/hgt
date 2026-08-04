import GaloisForLFunctions.HTGeometry.ProductLawHeadReduction
import GaloisForLFunctions.HTGeometry.ProductLawDegenerate

/-!
# The head determinant is the Jacobian of a logarithm

The gradient of the head product is the product times the vector of logarithmic derivatives,
`∂_j(∏_k Q_k(X_k)) = (∏_k Q_k(X_k))·(Q_j'/Q_j)(X_j)`, so one row scaling removes the product from the
bordered determinant entirely.

What is left is the Jacobian of the family `(L, δL, δ²L, …)` for `L = ∑_k log Q_k(X_k)`: the border row
is the gradient of `L`, and the remaining rows are the gradients of its jets, because the multiplier of
the head product is exactly `δL`.  The open determinant is therefore the observability of a *single*
function — a sum of one-variable logarithms — rather than of a product.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q : ℕ → Polynomial ℂ)

/-- **The gradient of the head product is logarithmic.** -/
theorem fpderiv_prodHead_eq {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) :
    ∀ {k j : ℕ}, j < k →
      fpderiv j (prodHead Q k) = prodHead Q k * logFactor (Q j) j := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
      intro j hj
      rw [prodHead_succ, Derivation.leibniz]
      rcases Nat.lt_or_ge j k with hjk | hjk
      · rw [ih hjk, fpderiv_fact_of_ne (by omega : k ≠ j)]
        simp only [smul_eq_mul, mul_zero]
        ring
      · have hjeq : j = k := by omega
        subst hjeq
        rw [fpderiv_prodHead_of_le Q (le_refl j), derivation_fact, fpderiv_fx_self, logFactor]
        have hne : fact (Q j) j ≠ 0 := fact_ne_zero (hQ j) j
        simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
        field_simp

/-- The vector of logarithmic derivatives: the gradient of `∑_k log Q_k(X_k)`. -/
noncomputable def logGradient (n : ℕ) : Fin (n + 1) → CascadeField :=
  fun j => logFactor (Q ((j : ℕ) + 1)) ((j : ℕ) + 1)

theorem headGradient_eq {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ) :
    headGradient Q n
      = fun j : Fin (n + 1) => prodHead Q (n + 2) * logGradient Q n j := by
  funext j
  rw [headGradient, logGradient, fpderiv_prodHead_eq hQ (by omega : (j : ℕ) + 1 < n + 2)]

/-- **The head product scales out of the bordered determinant.** -/
theorem uniformBordered_headGradient_det {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (n : ℕ)
    (L : Fin n → Fin (n + 1) → CascadeField) :
    (uniformBordered (headGradient Q n) L).det
      = prodHead Q (n + 2) * (uniformBordered (logGradient Q n) L).det := by
  classical
  have hrow : uniformBordered (headGradient Q n) L
      = Matrix.of fun i j => (Fin.cases (prodHead Q (n + 2)) (fun _ => (1 : CascadeField)) i)
        * (uniformBordered (logGradient Q n) L) i j := by
    funext i j
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [uniformBordered, Matrix.of_apply, Fin.cases_zero]
      rw [headGradient_eq hQ n]
    · simp [uniformBordered]
  rw [hrow, Matrix.det_mul_column]
  congr 1
  rw [Fin.prod_univ_succ]
  simp

end GaloisForLFunctions.HTGeometry
