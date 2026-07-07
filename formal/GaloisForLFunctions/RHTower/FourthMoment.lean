/-
The fourth moment: the Montgomery–Vaughan mean value for the divisor-coefficient Dirichlet polynomial.

The fourth moment of ζ is the second moment of `ζ²`, and `ζ(s)² = ∑ d(n) n^{-s}` has the divisor
function `d(n) = #{divisors of n}` as its Dirichlet coefficients.  Feeding `a n = d(n) · n^{-σ}` to the
Montgomery–Vaughan diagonal (`SecondMoment.secondMoment_upper_bound`) gives the mean value of the
fourth-moment carrier over a window `[T, T+U]`:

  ∫_T^{T+U} ‖∑_{n≤N} d(n) n^{-σ-it}‖² dt ≤ U · ∑_{n≤N} d(n)² n^{-2σ}  +  (off-diagonal),

the diagonal `U · ∑ d(n)² n^{-2σ}` being the main term (`fourthMoment_meanValue`).  The diagonal
coefficient sum `∑ d(n)² n^{-2σ}` is `ζ(2σ)⁴/ζ(4σ)`; for `σ > 1/2` it converges to a finite constant,
so the fourth moment is `O(U)` — a *bounded* mean value on every vertical line right of the critical
line.  That boundedness is exactly the input Carlson's density theorem consumes: fed through
Littlewood's lemma for ξ (`LittlewoodXi`), a bounded fourth moment yields the sublinear zero count
`N(σ, T) = o(T)`.

`fourthMoment_dpoly_le` is the mean-value upper bound, `fourthMoment_meanValue` its diagonal-plus-
remainder identity, and `divisorCoeff_sq` the coefficient-square simplification `((d n) n^{-σ})² =
(d n)² n^{-2σ}`.  The uniform-in-`N` constant bound on the diagonal for `1/2 < σ` is the divisor
estimate `d(n) ≪_ε n^ε` (classical, the remaining number-theoretic kernel); the crude bound
`d(n) ≤ n` gives convergence for `σ > 1` here.
-/
import GaloisForLFunctions.RHTower.SecondMoment

open Real Finset MeasureTheory

namespace RHTower

/-- The fourth-moment (divisor) coefficients `a n = d(n) · n^{-σ}`, where `d(n) = #divisors n`. -/
noncomputable def divisorCoeff (σ : ℝ) (n : ℕ) : ℝ := (n.divisors.card : ℝ) * (n : ℝ) ^ (-σ)

/-- The square of a divisor coefficient: `(d(n) · n^{-σ})² = d(n)² · n^{-2σ}`. -/
theorem divisorCoeff_sq (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (divisorCoeff σ n) ^ 2 = (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [divisorCoeff, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-σ)) 2, ← Real.rpow_mul hpos.le]
  congr 2
  push_cast; ring

/-- **The fourth-moment mean-value bound.**  The window mass of the divisor-coefficient Dirichlet
polynomial `∑_{n≤N} d(n) n^{-σ-it}` is at most the diagonal `U · ∑_{n≤N} d(n)² n^{-2σ}` plus the
explicit off-diagonal remainder.  This is `SecondMoment.secondMoment_upper_bound` at the fourth-moment
carrier — the fourth moment of ζ expressed through its `ζ²` Dirichlet polynomial. -/
theorem fourthMoment_dpoly_le (N : ℕ) (σ T U : ℝ) :
    (∫ t in T..(T + U), ‖dpoly (divisorCoeff σ) (Finset.Icc 1 N) t‖ ^ 2)
      ≤ U * (∑ m ∈ Finset.Icc 1 N, (divisorCoeff σ m) ^ 2)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |divisorCoeff σ m * divisorCoeff σ n| / |Real.log n - Real.log m| :=
  secondMoment_upper_bound (divisorCoeff σ) (Finset.Icc 1 N) T U
    (fun _n hn => (Finset.mem_Icc.mp hn).1)

/-- **The fourth-moment diagonal main term.**  The window mass equals the diagonal
`U · ∑_{n≤N} d(n)² n^{-2σ}` plus the off-diagonal oscillatory remainder — the exact
Montgomery–Vaughan mean value for the divisor carrier. -/
theorem fourthMoment_meanValue (N : ℕ) (σ T U : ℝ) :
    (∫ t in T..(T + U), ‖dpoly (divisorCoeff σ) (Finset.Icc 1 N) t‖ ^ 2)
      = U * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ))
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            (divisorCoeff σ m) * (divisorCoeff σ n)
              * cosInt (Real.log n - Real.log m) T U := by
  rw [secondMoment_meanValue]
  have hdiag : ∑ m ∈ Finset.Icc 1 N, (divisorCoeff σ m) ^ 2
      = ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) :=
    Finset.sum_congr rfl (fun n hn => divisorCoeff_sq σ (Finset.mem_Icc.mp hn).1)
  rw [hdiag]

/-- **Diagonal convergence, crude range.**  The diagonal coefficient sum
`∑_{n≤N} d(n)² n^{-2σ}` is bounded by `∑_{n≤N} n^{2-2σ}` via `d(n) ≤ n`; for `σ > 3/2` (so the
exponent `2 − 2σ < −1`) this is uniformly bounded in `N`.  The sharp range `σ > 1/2` needs the
divisor bound `d(n) ≪_ε n^ε`. -/
theorem fourthMoment_diagonal_crude_le (N : ℕ) (σ : ℝ) :
    ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ)
      ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (2 - 2 * σ) := by
  apply Finset.sum_le_sum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
  have hdle : (n.divisors.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self n
  have hdnn : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
  calc (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ)
      ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ (-2 * σ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hpos.le _)
        nlinarith [hdle, hdnn, hpos.le]
    _ = (n : ℝ) ^ (2 - 2 * σ) := by
        rw [← Real.rpow_natCast ((n : ℝ)) 2, ← Real.rpow_add hpos]
        congr 1; push_cast; ring

end RHTower
