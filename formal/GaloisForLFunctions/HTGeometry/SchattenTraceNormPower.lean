/-
# The trace norm of a power of a Schatten operator

Iterating Hölder would cost a constant growing like `2^{k²}`, which no power series can absorb.  The
approximation numbers give the sharp shape directly: a `k`-th power is approximated `k` times
faster, so its trace norm is at most `k` times the `k`-th energy of the original, and that energy is
the Schatten `p`-energy times the operator norm to the excess power.  The constant is *linear* in
`k`, which is what a series in `k` needs.

Main results:
* `tsum_rpow_approxNumber_le` — the `k`-th energy is the `p`-energy times an operator-norm factor.
* `traceNorm_pow_le` — **the trace norm of a power**: `‖Tᵏ‖₁ ≤ k·M^{k−p}·‖T‖_p^p`.
-/
import GaloisForLFunctions.HTGeometry.SchattenNorm

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Above the Schatten exponent, the `s`-energy is the `p`-energy times an operator-norm factor. -/
theorem rpow_approxNumber_le {p s : ℝ} (hp : 0 < p) (T : H →L[ℂ] H) (hps : p ≤ s) (n : ℕ) :
    approxNumber T n ^ s ≤ (max ‖T‖ 1) ^ (s - p) * approxNumber T n ^ p := by
  have hM1 : (1 : ℝ) ≤ max ‖T‖ 1 := le_max_right _ _
  have hM0 : (0 : ℝ) < max ‖T‖ 1 := lt_of_lt_of_le zero_lt_one hM1
  have hle : approxNumber T n ≤ max ‖T‖ 1 :=
    le_trans (approxNumber_le_norm T n) (le_max_left _ _)
  rcases eq_or_lt_of_le (approxNumber_nonneg T n) with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by linarith), Real.zero_rpow hp.ne', mul_zero]
  · have hsplit : approxNumber T n ^ s
        = approxNumber T n ^ p * approxNumber T n ^ (s - p) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rw [hsplit, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (approxNumber_nonneg T n) p)
    exact Real.rpow_le_rpow (approxNumber_nonneg T n) hle (by linarith)

omit [CompleteSpace H] in
/-- The `s`-energy of the approximation numbers above the Schatten exponent. -/
theorem tsum_rpow_approxNumber_le {p s : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) (hps : p ≤ s) :
    (∑' n, approxNumber T n ^ s)
      ≤ (max ‖T‖ 1) ^ (s - p) * ∑' n, approxNumber T n ^ p := by
  have hM0 : (0 : ℝ) < max ‖T‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdom : Summable fun n => (max ‖T‖ 1) ^ (s - p) * approxNumber T n ^ p := hT.mul_left _
  have hsum : Summable fun n => approxNumber T n ^ s :=
    Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (approxNumber_nonneg T n) s)
      (fun n => rpow_approxNumber_le hp T hps n) hdom
  refine le_trans (hsum.tsum_le_tsum (fun n => rpow_approxNumber_le hp T hps n) hdom) ?_
  rw [tsum_mul_left]

omit [CompleteSpace H] in
/-- **The trace norm of a power of a Schatten operator.** -/
theorem traceNorm_pow_le {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H} (hT : MemSchattenClass p T)
    {k : ℕ} (hk : 0 < k) (hpk : p ≤ (k : ℝ)) :
    traceNorm H (T ^ k)
      ≤ (k : ℝ) * ((max ‖T‖ 1) ^ ((k : ℝ) - p) * ∑' n, approxNumber T n ^ p) := by
  have hone : MemSchattenClass 1 (T ^ k) := memSchattenClass_one_pow hp hT hk hpk
  have hsum1 : Summable fun n => approxNumber (T ^ k) n := by
    refine hone.congr fun n => ?_
    exact Real.rpow_one _
  have hkenergy : Summable fun m : ℕ => approxNumber T m ^ (k : ℝ) := by
    have hdom : Summable fun n => (max ‖T‖ 1) ^ ((k : ℝ) - p) * approxNumber T n ^ p :=
      hT.mul_left _
    exact Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (approxNumber_nonneg T n) _)
      (fun n => rpow_approxNumber_le hp T hpk n) hdom
  have hnat : ∀ m : ℕ, approxNumber T m ^ k = approxNumber T m ^ (k : ℝ) := by
    intro m
    rw [Real.rpow_natCast]
  have hrep : Summable fun m : ℕ => approxNumber T (m / k) ^ (k : ℝ) :=
    summable_comp_nat_div (fun n => Real.rpow_nonneg (approxNumber_nonneg T n) _) hkenergy hk
  have hpt : ∀ n : ℕ, approxNumber (T ^ k) n ≤ approxNumber T (n / k) ^ (k : ℝ) := by
    intro n
    rw [← hnat]
    exact approxNumber_pow_le_div T hk n
  have hstep1 : traceNorm H (T ^ k) ≤ ∑' n, approxNumber T (n / k) ^ (k : ℝ) := by
    rw [traceNorm]
    exact hsum1.tsum_le_tsum hpt hrep
  have hstep2 : (∑' n, approxNumber T (n / k) ^ (k : ℝ))
      ≤ (k : ℝ) * ∑' m, approxNumber T m ^ (k : ℝ) :=
    tsum_comp_nat_div_le (fun n => Real.rpow_nonneg (approxNumber_nonneg T n) _) hkenergy hk
  have hstep3 : (∑' m, approxNumber T m ^ (k : ℝ))
      ≤ (max ‖T‖ 1) ^ ((k : ℝ) - p) * ∑' n, approxNumber T n ^ p :=
    tsum_rpow_approxNumber_le hp hT hpk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  calc traceNorm H (T ^ k) ≤ ∑' n, approxNumber T (n / k) ^ (k : ℝ) := hstep1
    _ ≤ (k : ℝ) * ∑' m, approxNumber T m ^ (k : ℝ) := hstep2
    _ ≤ (k : ℝ) * ((max ‖T‖ 1) ^ ((k : ℝ) - p) * ∑' n, approxNumber T n ^ p) :=
        mul_le_mul_of_nonneg_left hstep3 hk0

end

end GaloisForLFunctions.HTGeometry
