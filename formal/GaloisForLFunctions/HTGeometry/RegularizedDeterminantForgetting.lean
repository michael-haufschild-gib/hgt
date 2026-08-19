/-
# What a regularized determinant of order `g+1` forgets

The exponent of the order-`g+1` regularized determinant is the trace series with its first `g`
terms removed, so it factors as `z^{g+1}` times an analytic remainder: the determinant is flat to
order `g` at the origin, and the coordinates `Tr(M), …, Tr(M^g)` do not appear in it at all.

Consequently two matrices whose power traces agree from order `g+1` onwards have the *same*
regularized determinant of order `g+1`.  That is the exact sense in which the completion forgets
the first `g` power traces, and it is what makes those traces the fibre coordinates of the
completion.

Main results:
* `traceSeries_eq_pow_mul` — the exponent factors through `z^{g+1}`.
* `finiteDetOrder_neg_eq_of_traceTail_eq` — **the determinant forgets the first `g` traces**.
-/
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminantOrder

namespace GaloisForLFunctions.HTGeometry

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The exponent of the order-`g+1` determinant vanishes to order `g+1`.**  It is `z^{g+1}` times
a series in `z`, so no power below `g+1` -- and hence no trace below order `g+1` -- occurs. -/
theorem traceSeries_eq_pow_mul (g : ℕ) (M : Matrix m m ℂ) (z : ℂ) :
    (∑' k : ℕ, z ^ (k + (g + 1)) / ((k + (g + 1) : ℕ) : ℂ) * (M ^ (k + (g + 1))).trace)
      = z ^ (g + 1) *
        ∑' k : ℕ, z ^ k * ((M ^ (k + (g + 1))).trace / ((k + (g + 1) : ℕ) : ℂ)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [pow_add]
  ring

/-- **The order-`g+1` determinant forgets the first `g` power traces.**  Two matrices whose power
traces agree from order `g+1` onwards have the same regularized determinant of that order. -/
theorem finiteDetOrder_neg_eq_of_traceTail_eq (g : ℕ) {M N : Matrix m m ℂ}
    (htail : ∀ k : ℕ, (M ^ (k + (g + 1))).trace = (N ^ (k + (g + 1))).trace)
    {z : ℂ} (hM : ‖z‖ * Real.sqrt (matHSNormSq M) < 1)
    (hN : ‖z‖ * Real.sqrt (matHSNormSq N) < 1) :
    finiteDetOrder g (-M) z = finiteDetOrder g (-N) z := by
  rw [← exp_neg_traceSeries_eq_finiteDetOrder_neg g M hM,
    ← exp_neg_traceSeries_eq_finiteDetOrder_neg g N hN]
  congr 2
  exact tsum_congr fun k => by rw [htail k]

end GaloisForLFunctions.HTGeometry
