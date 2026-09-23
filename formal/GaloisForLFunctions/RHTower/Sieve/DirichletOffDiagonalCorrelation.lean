import GaloisForLFunctions.RHTower.Sieve.DirichletDiagonal
import GaloisForLFunctions.RHTower.Sieve.DirichletPolyAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.PrimitiveRatioDecomposition

/-!
# The off-diagonal of the mean square, in primitive-ratio form

`DirichletDiagonal.integral_normSq_dirPoly_sub_diag` is the exact off-diagonal identity

`∫_0^T |F|² − T ∑_n |a_n|² = ∑_{m ≠ n} a_m conj(a_n) ∫_0^T e^{it(log m − log n)} dt`.

Its kernel depends on the pair only through the *ratio* `m/n`, so writing `d = gcd(m, n)` and using
`PrimitiveRatioDecomposition.sum_fin_offDiag_eq_sum_ratio` collapses the `d`-sum onto a single kernel
value.  The result is the identity

`∫_0^T |F|² − T ∑_n |a_n|² = ∑_{(m,n) coprime, m ≠ n} C(m,n) · K_T(m,n)`,

where `K_T(m,n) = ∫_0^T e^{it(log m − log n)} dt` and

`C(m,n) = ∑_{d : dm ≤ N, dn ≤ N} a_{dm} conj(a_{dn})`

is the *multiplicative correlation of the coefficients along the ratio `m/n`*.

This is exactly the reduction the route triage of `coefficient-free-cap-law.md` asks for.  In the raw
off-diagonal the coefficients appear pairwise, and every term-by-term majorisation replaces
`a_m conj(a_n)` by `‖a_m‖‖a_n‖` — which lands in the coefficient-free family capped by
`CoefficientFreeCap.le_of_coefficientFree_bound`.  After this identity the coefficients appear only
inside `C(m,n)`, an *inner* sum over a long arithmetic progression of indices, where cancellation in the
coefficient signs is available before any modulus is taken.  The two lemmas below record the identity
and the fact that it is never weaker than the classical bound (`norm_le_sum_norm_correlation_mul`, whose
term-by-term majorisation reproduces the mean value theorem with one term per coprime pair instead of one
per pair).
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- The phase kernel of the mean square, as a function of a pair of positive integers. -/
noncomputable def ratioKernel (T : ℝ) (m n : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- **The kernel sees only the ratio.**  Scaling both arguments by `d` does not change it. -/
theorem ratioKernel_mul_left (T : ℝ) {d m n : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ratioKernel T (d * m) (d * n) = ratioKernel T m n := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log ((d * m : ℕ) : ℝ) - Real.log ((d * n : ℕ) : ℝ)
      = Real.log (m : ℝ) - Real.log (n : ℝ) := by
    push_cast
    rw [Real.log_mul (ne_of_gt hd0) (ne_of_gt hm0), Real.log_mul (ne_of_gt hd0) (ne_of_gt hn0)]
    ring
  rw [ratioKernel, ratioKernel, hlog]

/-- The kernel bound `2/|log(m/n)|`, transported to positive-integer arguments. -/
theorem norm_ratioKernel_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) (T : ℝ) :
    ‖ratioKernel T m n‖ ≤ 2 / |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have h1 : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub hm]; norm_num
    rw [this]; ring
  have h2 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]; norm_num
    rw [this]; ring
  have hne : m - 1 ≠ n - 1 := by omega
  have := norm_integral_dirPhase_off hne T
  rw [h1, h2] at this
  exact this

/-- **The multiplicative correlation of the coefficients along the ratio `m/n`.** -/
noncomputable def dirCorrelation {N : ℕ} (a : Fin N → ℂ) (m n : ℕ) : ℂ :=
  ∑ d ∈ ratioScales N m n, dirSeq a (d * m) * (starRingEnd ℂ) (dirSeq a (d * n))

/-- **The mean square minus its diagonal, in primitive-ratio form.**  The coefficients enter only
through their correlations along coprime ratios, and each ratio carries a single kernel value. -/
theorem integral_normSq_dirPoly_sub_diag_ratio (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ q ∈ primitiveRatioPairs N, dirCorrelation a q.1 q.2 * ratioKernel T q.1 q.2 := by
  classical
  rw [integral_normSq_dirPoly_sub_diag]
  have hterm : ∀ m n : Fin N,
      (a m * (starRingEnd ℂ) (a n))
          * (∫ t in (0 : ℝ)..T, Complex.exp (((t * (Real.log (((m : ℕ) : ℝ) + 1)
              - Real.log (((n : ℕ) : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
        = dirSeq a ((m : ℕ) + 1) * (starRingEnd ℂ) (dirSeq a ((n : ℕ) + 1))
            * ratioKernel T ((m : ℕ) + 1) ((n : ℕ) + 1) := by
    intro m n
    rw [dirSeq_succ, dirSeq_succ, ratioKernel]
    push_cast
    rfl
  rw [Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => hterm m n))]
  rw [sum_fin_offDiag_eq_sum_ratio (N := N)
    (f := fun x y => dirSeq a x * (starRingEnd ℂ) (dirSeq a y) * ratioKernel T x y)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [primitiveRatioPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hm1, _⟩, hn1, _⟩, _, _⟩ := hq
  rw [dirCorrelation, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [ratioScales, Finset.mem_filter, Finset.mem_Icc] at hd
  rw [ratioKernel_mul_left T hd.1.1 hm1 hn1]

/-- The primitive-ratio form is never weaker: majorising it term by term reproduces the mean value
theorem, with one term per *coprime* pair. -/
theorem norm_le_sum_norm_correlation_mul (N : ℕ) (a : Fin N → ℂ) (T : ℝ) :
    ‖(∫ t in (0 : ℝ)..T, ((‖dirPoly N a t‖ ^ (2 : ℕ) : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖a m‖ ^ (2 : ℕ) : ℝ) : ℂ)‖
      ≤ ∑ q ∈ primitiveRatioPairs N,
          ‖dirCorrelation a q.1 q.2‖ * (2 / |Real.log (q.1 : ℝ) - Real.log (q.2 : ℝ)|) := by
  classical
  rw [integral_normSq_dirPoly_sub_diag_ratio]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q hq => ?_)
  rw [primitiveRatioPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hm1, _⟩, hn1, _⟩, _, hne⟩ := hq
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_ratioKernel_le hm1 hn1 hne T) (norm_nonneg _)

end RHTower.Sieve
