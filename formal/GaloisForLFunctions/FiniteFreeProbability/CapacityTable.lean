import GaloisForLFunctions.FiniteFreeProbability.ShiftRegimeGaussianCapacity
import GaloisForLFunctions.HTGeometry.SignAlternationHyperbolicity

/-!
# The Gaussian capacity table of shifted Jensen polynomials

For a coefficient sequence `a`, the shifted Jensen polynomials `J^{d,n}(X) = Σ_j C(d,j) a(n+j) X^j`
form a derivative ladder `(J^{d+1,n})' = (d+1) J^{d,n+1}`, and the heat operators commute with
differentiation. Hence real-rootedness of the backward heat flow `e^{sD²}` moves along
anti-diagonals: if `e^{sD²}J^{d+1,n}` is real-rooted, so is `e^{sD²}J^{d,n+1}`.

So the Gaussian capacity `κ(d,n) = sup{s : e^{sD²}J^{d,n} real-rooted}` satisfies
`κ(d, n+1) ≥ κ(d+1, n)`, and the whole table is bounded below by its degree row:
`κ(d, m) ≥ κ(d+m, 0)`. For `Ξ` the degree row is critical (`o(d^{-2})`, the finite free
de Bruijn–Newman law) and the shift columns approach the full Hermite capacity.
-/

open Polynomial
open GaloisForLFunctions.SignAlternation

namespace FiniteFreeProbability

noncomputable section

/-- Heat commutes with differentiation. -/
theorem derivative_heatOp {s : ℝ} {d : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ d + 1) :
    derivative (heatOp s (d + 1) p) = heatOp s d (derivative p) := by
  rw [heatOp_eq_sum, heatOp_eq_sum, derivative_sum, Finset.sum_range_succ]
  have hlast : derivative (C (s ^ (d + 1) / ((d + 1).factorial : ℝ)) *
      derivative^[2 * (d + 1)] p) = 0 := by
    rw [iterate_derivative_eq_zero (by omega)]; simp
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul, ← Function.iterate_succ_apply' derivative, ← Function.iterate_succ_apply]

/-- **Anti-diagonal monotonicity.** Real-rootedness of `e^{sD²}J^{d+1,n}` implies that of
`e^{sD²}J^{d,n+1}`. -/
theorem splits_heatOp_jensenPoly_succ_shift (a : ℕ → ℝ) {s : ℝ} {d n : ℕ}
    (h : (heatOp s (d + 1) (jensenPoly a (d + 1) n)).Splits) :
    (heatOp s d (jensenPoly a d (n + 1))).Splits := by
  have hder : (derivative (heatOp s (d + 1) (jensenPoly a (d + 1) n))).Splits := by
    have := GaloisForLFunctions.HTGeometry.splits_laguerreShift h 0
    simpa [GaloisForLFunctions.HTGeometry.laguerreShift] using this
  rw [derivative_heatOp (natDegree_jensenPoly_le a (d + 1) n), derivative_jensenPoly,
    heatOp_C_mul] at hder
  exact (splits_mul_iff_right (C_ne_zero.2 (by positivity)) (Polynomial.Splits.C _)).1 hder

/-- **The degree row controls the table.** Real-rootedness of `e^{sD²}J^{d+m,n}` implies that of
`e^{sD²}J^{d,n+m}`. -/
theorem splits_heatOp_jensenPoly_shift (a : ℕ → ℝ) {s : ℝ} (d : ℕ) :
    ∀ m n, (heatOp s (d + m) (jensenPoly a (d + m) n)).Splits →
      (heatOp s d (jensenPoly a d (n + m))).Splits := by
  intro m
  induction m with
  | zero => intro n h; simpa using h
  | succ m ih =>
    intro n h
    have h1 := splits_heatOp_jensenPoly_succ_shift a
      (d := d + m) (n := n) (by rwa [show d + m + 1 = d + (m + 1) by ring])
    have := ih (n + 1) h1
    rwa [show n + 1 + m = n + (m + 1) by ring] at this

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.splits_heatOp_jensenPoly_shift
