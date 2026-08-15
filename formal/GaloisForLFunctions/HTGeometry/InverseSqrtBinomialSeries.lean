import GaloisForLFunctions.HTGeometry.CentralBinomialConvolutionAsymptotic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The inverse square root as a binomial series, and its grade-one tail

The scalar expansion `(1−s)^{-1/2} = Σ_k binom(2k,k) 4^{-k} s^k` has all coefficients in `(0,1]`,
so in any Banach algebra the series converges for `‖S‖ < 1` and its tail past the constant term
obeys the *linear* bound

`‖Σ_{k ≥ 1} binom(2k,k) 4^{-k} S^k‖ ≤ ‖S‖ / (1 − ‖S‖)`.

Applied to `S = T/(2L)` with `L ≥ ‖T‖` this is the grade-one estimate: the deviation of
`(I − T/2L)^{-1/2}` from the identity is `O(1/L)`, with the explicit constant `‖T‖`.  Because the
constant term is exactly the identity, projecting away the grade-zero coordinate leaves only the
tail — the mechanism by which an exterior root trace makes every strict-interior descendant start
at grade one.

Nothing here uses a functional calculus: the series *is* the definition, which is what the
all-grade expansion of the card asserts.
-/

open scoped NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The tail of the inverse-square-root binomial series, past the constant term. -/
def invSqrtTail (S : A) : A := ∑' k : ℕ, normalizedCentralBinom (k + 1) • S ^ (k + 1)

omit [CompleteSpace A] in
theorem norm_invSqrtTail_term_le (S : A) (k : ℕ) :
    ‖normalizedCentralBinom (k + 1) • S ^ (k + 1)‖ ≤ ‖S‖ ^ (k + 1) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (normalizedCentralBinom_nonneg _)]
  calc normalizedCentralBinom (k + 1) * ‖S ^ (k + 1)‖
      ≤ 1 * ‖S ^ (k + 1)‖ :=
        mul_le_mul_of_nonneg_right (normalizedCentralBinom_le_one _) (norm_nonneg _)
    _ = ‖S ^ (k + 1)‖ := one_mul _
    _ ≤ ‖S‖ ^ (k + 1) := norm_pow_le' S (Nat.succ_pos k)

theorem summable_invSqrtTail {S : A} (hS : ‖S‖ < 1) :
    Summable fun k : ℕ => normalizedCentralBinom (k + 1) • S ^ (k + 1) := by
  have hgeo : Summable fun k : ℕ => ‖S‖ ^ (k + 1) := by
    refine ((summable_geometric_of_lt_one (norm_nonneg S) hS).mul_left ‖S‖).congr fun k => ?_
    rw [pow_succ]
    ring
  exact Summable.of_norm_bounded hgeo (fun k => norm_invSqrtTail_term_le S k)

omit [CompleteSpace A] in
/-- **The linear tail bound.**  Past the constant term the inverse-square-root series is bounded by
`‖S‖/(1−‖S‖)`. -/
theorem norm_invSqrtTail_le {S : A} (hS : ‖S‖ < 1) :
    ‖invSqrtTail S‖ ≤ ‖S‖ / (1 - ‖S‖) := by
  have hpos : (0 : ℝ) < 1 - ‖S‖ := by linarith
  have hgeo : Summable fun k : ℕ => ‖S‖ ^ (k + 1) := by
    refine ((summable_geometric_of_lt_one (norm_nonneg S) hS).mul_left ‖S‖).congr fun k => ?_
    rw [pow_succ]
    ring
  have hval : (∑' k : ℕ, ‖S‖ ^ (k + 1)) = ‖S‖ / (1 - ‖S‖) := by
    have hcongr : (fun k : ℕ => ‖S‖ ^ (k + 1)) = fun k : ℕ => ‖S‖ * ‖S‖ ^ k := by
      funext k
      rw [pow_succ]
      ring
    rw [hcongr, tsum_mul_left, tsum_geometric_of_lt_one (norm_nonneg S) hS]
    ring
  have hnormsum : Summable fun k : ℕ => ‖normalizedCentralBinom (k + 1) • S ^ (k + 1)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_invSqrtTail_term_le S k) hgeo
  calc ‖invSqrtTail S‖
      ≤ ∑' k : ℕ, ‖normalizedCentralBinom (k + 1) • S ^ (k + 1)‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k : ℕ, ‖S‖ ^ (k + 1) :=
        Summable.tsum_mono hnormsum hgeo (fun k => norm_invSqrtTail_term_le S k)
    _ = ‖S‖ / (1 - ‖S‖) := hval

/-! ## The grade-one estimate -/

omit [CompleteSpace A] in
/-- **The grade-one estimate.**  On the terminal ray `L ≥ ‖T‖` the deviation of the inverse square
root from the identity is at most `‖T‖/L`. -/
theorem norm_invSqrtTail_scaled_le {T : A} {L : ℝ} (hL : 0 < L) (hT : ‖T‖ ≤ L) :
    ‖invSqrtTail ((1 / (2 * L)) • T)‖ ≤ ‖T‖ / L := by
  set S : A := (1 / (2 * L)) • T with hSdef
  have hnormS : ‖S‖ = ‖T‖ / (2 * L) := by
    rw [hSdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * L))]
    field_simp
  have hhalf : ‖S‖ ≤ 1 / 2 := by
    rw [hnormS, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hS1 : ‖S‖ < 1 := by linarith
  have hpos : (0 : ℝ) < 1 - ‖S‖ := by linarith
  have hxnn : (0 : ℝ) ≤ ‖S‖ := norm_nonneg S
  have hstep : ‖S‖ / (1 - ‖S‖) ≤ 2 * ‖S‖ := by
    rw [div_le_iff₀ hpos]
    nlinarith [hxnn, hhalf]
  refine le_trans (norm_invSqrtTail_le hS1) (hstep.trans (le_of_eq ?_))
  rw [hnormS]
  field_simp

/-! ## The all-grade expansion -/

omit [CompleteSpace A] in
/-- **The all-grade expansion.**  Scaling the series argument by `1/(2L)` produces the coefficients
`binom(2k,k) 8^{-k} L^{-k}`. -/
theorem invSqrtTail_scaled_eq (T : A) {L : ℝ} (hL : 0 < L) :
    invSqrtTail ((1 / (2 * L)) • T)
      = ∑' k : ℕ, (normalizedCentralBinom (k + 1) / (2 * L) ^ (k + 1)) • T ^ (k + 1) := by
  rw [invSqrtTail]
  refine tsum_congr fun k => ?_
  rw [smul_pow, smul_smul]
  congr 1
  rw [div_pow, one_pow]
  field_simp

end GaloisForLFunctions.HTGeometry
