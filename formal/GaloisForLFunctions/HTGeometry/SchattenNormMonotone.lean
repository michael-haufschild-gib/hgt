/-
# The Schatten norms decrease with the exponent

For `s ≤ 1` the `ℓ^s` norm dominates the `ℓ^1` norm: normalising by the `ℓ^s` norm makes every entry
at most one, and on `[0,1]` a smaller exponent gives a larger power.  So the trace norm of a
Schatten-`s` operator is at most its Schatten-`s` norm, which is what converts a product estimate
stated at the exponent `p/n` into one for the trace norm.

Main results:
* `tsum_le_rpow_tsum_rpow` — **the `ℓ^s ⊆ ℓ^1` norm inequality** for `0 < s ≤ 1`.
* `traceNorm_le_schattenNorm` — **the trace norm is at most the Schatten-`s` norm**.
-/
import GaloisForLFunctions.HTGeometry.SchattenNorm

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- **The `ℓ^s ⊆ ℓ^1` norm inequality** for `0 < s ≤ 1`. -/
theorem tsum_le_rpow_tsum_rpow {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hsum : Summable fun n => a n ^ s) :
    ∑' n, a n ≤ (∑' n, a n ^ s) ^ (1 / s) := by
  set E : ℝ := ∑' n, a n ^ s with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun n => Real.rpow_nonneg (ha n) s
  set M : ℝ := E ^ (1 / s) with hMdef
  have hM0 : 0 ≤ M := Real.rpow_nonneg hE0 _
  rcases eq_or_lt_of_le hM0 with hMzero | hMpos
  · -- the `ℓ^s` norm vanishes, hence every entry does
    have hEzero : E = 0 := by
      by_contra hEne
      have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEne)
      have : 0 < M := by
        rw [hMdef]
        exact Real.rpow_pos_of_pos hEpos _
      linarith
    have hzero : ∀ n, a n = 0 := by
      intro n
      have hterm : a n ^ s = 0 := by
        refine le_antisymm ?_ (Real.rpow_nonneg (ha n) s)
        rw [← hEzero]
        exact hsum.le_tsum n fun m _ => Real.rpow_nonneg (ha m) s
      by_contra hne
      have hapos : 0 < a n := lt_of_le_of_ne (ha n) (Ne.symm hne)
      exact absurd hterm (ne_of_gt (Real.rpow_pos_of_pos hapos s))
    rw [tsum_congr hzero, tsum_zero]
    exact hM0
  · have hEpos : 0 < E := by
      by_contra hcon
      have hEz : E = 0 := le_antisymm (not_lt.mp hcon) hE0
      rw [hMdef, hEz, Real.zero_rpow (by positivity)] at hMpos
      exact absurd rfl (ne_of_gt hMpos)
    have hMs : M ^ s = E := by
      rw [hMdef, ← Real.rpow_mul hE0]
      rw [one_div, inv_mul_cancel₀ hs0.ne', Real.rpow_one]
    have hle : ∀ n, a n / M ≤ (a n / M) ^ s := by
      intro n
      have hterm : a n ^ s ≤ E :=
        hsum.le_tsum n fun m _ => Real.rpow_nonneg (ha m) s
      have haM : a n ≤ M := by
        by_contra hcon
        have hMlt : M < a n := not_le.mp hcon
        have : M ^ s < a n ^ s := Real.rpow_lt_rpow hM0 hMlt hs0
        rw [hMs] at this
        linarith
      have hdiv0 : 0 ≤ a n / M := div_nonneg (ha n) hM0
      have hdiv1 : a n / M ≤ 1 := (div_le_one hMpos).mpr haM
      rcases eq_or_lt_of_le hdiv0 with hz | hpos
      · rw [← hz, Real.zero_rpow hs0.ne']
      · calc a n / M = (a n / M) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (a n / M) ^ s := Real.rpow_le_rpow_of_exponent_ge hpos hdiv1 hs1
    have hdivsum : Summable fun n => (a n / M) ^ s := by
      have hrw : ∀ n, (a n / M) ^ s = (M ^ s)⁻¹ * a n ^ s := by
        intro n
        rw [Real.div_rpow (ha n) hM0]
        ring
      exact (hsum.mul_left ((M ^ s)⁻¹)).congr fun n => (hrw n).symm
    have hasum : Summable fun n => a n / M :=
      Summable.of_nonneg_of_le (fun n => div_nonneg (ha n) hM0) hle hdivsum
    have hbound : (∑' n, a n / M) ≤ 1 := by
      refine le_trans (hasum.tsum_le_tsum hle hdivsum) ?_
      have hrw : (∑' n, (a n / M) ^ s) = (M ^ s)⁻¹ * ∑' n, a n ^ s := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [Real.div_rpow (ha n) hM0]
        ring
      rw [hrw, hMs, inv_mul_cancel₀ hEpos.ne']
    have hsplit : (∑' n, a n / M) = (∑' n, a n) / M := by
      rw [← tsum_div_const]
    rw [hsplit, div_le_one hMpos] at hbound
    exact hbound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The trace norm is at most the Schatten-`s` norm**, for `0 < s ≤ 1`. -/
theorem traceNorm_le_schattenNorm {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {T : H →L[ℂ] H}
    (hT : MemSchattenClass s T) : traceNorm H T ≤ schattenNorm s T := by
  rw [traceNorm, schattenNorm]
  exact tsum_le_rpow_tsum_rpow (fun n => approxNumber_nonneg T n) hs0 hs1 hT

end

end GaloisForLFunctions.HTGeometry
