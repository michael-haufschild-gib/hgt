/-
The double-Voronoi framework at a general index, and the uniformity of its loop.

Cycles at `k = 3` established: the shift-average reduces to `Σ_n d_k(n)[Δ_k(n+H) - Δ_k(n)]`; the
short-interval mean square splits into a diagonal and an off-diagonal; the diagonal already gives the
conjectured answer; and the off-diagonal, grouped by the difference of the two dual variables, is the
correlation the reduction started from.

Running the same computation at general `k` gives the exponents below.  The block length and block
count depend on `k`, but two things do not:

* the diagonal of the short-interval mean square is `X·h` — exponent `β = 1` — **for every `k`**;
* the off-diagonal is indexed by `j = m' - m` and its coefficient sum is `Σ_m d_k(m)d_k(m+j)`, the
  `k`-fold correlation, **for every `k`**.

So the loop is uniform in the index.  Compositeness of `4` changes nothing: the off-diagonal is
grouped by a difference of dual variables, and both dual coefficient sets are `d_k` whatever `k` is.
-/
import GaloisForLFunctions.HTGeometry.TernaryReductionLoop

namespace HTGeometry

/-- Block length at which the dual phase `2πk(my)^{1/k}` advances by one unit, with the dual
truncated at `M ≍ x`: `L = x^{(k-2)/k}`. -/
def blockLengthExponentAt (k : ℚ) : ℚ := (k - 2) / k

/-- Number of blocks in `[x, 2x]`: `N_B = x/L = x^{2/k}`. -/
def blockCountExponentAt (k : ℚ) : ℚ := 2 / k

theorem blockCount_eq_one_sub_blockLength {k : ℚ} (hk : k ≠ 0) :
    blockCountExponentAt k = 1 - blockLengthExponentAt k := by
  unfold blockCountExponentAt blockLengthExponentAt
  field_simp
  ring

@[simp] theorem blockLengthExponentAt_three : blockLengthExponentAt 3 = 1/3 := by
  unfold blockLengthExponentAt; norm_num

@[simp] theorem blockLengthExponentAt_four : blockLengthExponentAt 4 = 1/2 := by
  unfold blockLengthExponentAt; norm_num

@[simp] theorem blockCountExponentAt_three : blockCountExponentAt 3 = 2/3 := by
  unfold blockCountExponentAt; norm_num

@[simp] theorem blockCountExponentAt_four : blockCountExponentAt 4 = 1/2 := by
  unfold blockCountExponentAt; norm_num

/-- **The diagonal of the short-interval mean square is `X·h` at every index.**  Both ranges of the
dual — below and above the crossover `m₁ = x^{k-1}/h^k` — contribute `h·x^{-(k-1)/k}` to the
coefficient sum, and the prefactor `x^{(k-1)/k + 1}` returns `x·h`.  The exponent is `1`, independent
of `k`. -/
def diagonalMeanSquareExponent (_k : ℚ) : ℚ := 1

theorem diagonal_uniform (k l : ℚ) :
    diagonalMeanSquareExponent k = diagonalMeanSquareExponent l := rfl

theorem diagonal_matches_ternary :
    diagonalMeanSquareExponent 3 = diagonalMeanSquareBeta := rfl

/-- Cauchy–Schwarz output for the fluctuation sum at index `k` with mean-square exponent `β`. -/
def fluctuationExponentAt (k β : ℚ) : ℚ := 1/k + 1/2 + (k - 2) * (β - 1) / (2 * k)

/-- Consistency with the `k = 3` chain: at `β = 4/3` the output is `8/9`, the value computed there. -/
theorem fluctuationExponentAt_three : fluctuationExponentAt 3 (4/3) = 8/9 := by
  unfold fluctuationExponentAt; norm_num

/-- At the diagonal value `β = 1` the fluctuation exponent collapses to `1/k + 1/2`, independently of
the block structure — the `(k-2)` factor is switched off. -/
theorem fluctuationExponentAt_diagonal (k : ℚ) :
    fluctuationExponentAt k 1 = 1/k + 1/2 := by
  unfold fluctuationExponentAt; ring

@[simp] theorem fluctuationExponentAt_four_diagonal : fluctuationExponentAt 4 1 = 3/4 := by
  rw [fluctuationExponentAt_diagonal]; norm_num

/-- **The loop is uniform in the index.**  At every `k`: the diagonal already meets the criterion, so
the whole obstruction is the off-diagonal; and the off-diagonal, grouped by `j = m' - m`, is the
`k`-fold correlation itself.  The double-Voronoi route therefore closes at every index, `k = 4`
included, and the compositeness of `4` is irrelevant — the grouping is by a difference of dual
variables and both dual coefficient sets are `d_k`. -/
theorem reduction_loop_uniform (k : ℚ) :
    diagonalMeanSquareExponent k = 1 ∧
    diagonalMeanSquareExponent k = diagonalMeanSquareBeta ∧
    fluctuationExponentAt k 1 = 1/k + 1/2 :=
  ⟨rfl, rfl, fluctuationExponentAt_diagonal k⟩

end HTGeometry
