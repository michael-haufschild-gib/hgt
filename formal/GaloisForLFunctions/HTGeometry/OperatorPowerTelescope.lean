import Mathlib

/-!
# Telescoping a difference of operator powers on one vector

For bounded operators `X`, `Y` and a vector `v`,

`X^r v - Y^r v = ∑_{i < r} Y^{r-1-i} ((X - Y) (X^i v))`,

so the error of replacing `X` by a model `Y` on `v` is controlled by the *one-step* errors of `X`
evaluated on the iterates `X^i v`, weighted by powers of `‖Y‖` only.

The direction matters.  The other telescope, `∑ X^{r-1-i} ((X-Y)(Y^i v))`, weights the one-step
errors by powers of `‖X‖`; when `X` is a normalized operator whose norm grows with a parameter,
that form is useless while this one is not — provided the class of vectors carrying the one-step
estimate is invariant under `X` rather than under `Y`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **The one-vector telescope of a difference of operator powers.** -/
theorem operator_pow_sub_eq_sum (X Y : E →L[𝕜] E) (r : ℕ) (v : E) :
    (X ^ r) v - (Y ^ r) v
      = ∑ i ∈ Finset.range r, (Y ^ (r - 1 - i)) ((X - Y) ((X ^ i) v)) := by
  induction r generalizing v with
  | zero => simp
  | succ r ih =>
      have hsplit : ∑ i ∈ Finset.range (r + 1),
          (Y ^ (r + 1 - 1 - i)) ((X - Y) ((X ^ i) v))
          = (∑ i ∈ Finset.range r, (Y ^ (r - 1 - i)) ((X - Y) ((X ^ i) (X v))))
            + (Y ^ r) ((X - Y) v) := by
        rw [Finset.sum_range_succ']
        congr 1
        · refine Finset.sum_congr rfl fun i _ => ?_
          have hexp : r + 1 - 1 - (i + 1) = r - 1 - i := by omega
          have hX : (X ^ (i + 1)) v = (X ^ i) (X v) := by
            rw [pow_succ]
            rfl
          rw [hexp, hX]
      rw [hsplit, ← ih (X v)]
      have hXv : (X ^ r) (X v) = (X ^ (r + 1)) v := by
        rw [pow_succ]
        rfl
      have hYv : (Y ^ r) (Y v) = (Y ^ (r + 1)) v := by
        rw [pow_succ]
        rfl
      have hsub : (X - Y) v = X v - Y v := rfl
      rw [hsub, map_sub, hXv, hYv]
      abel

/-- **Quantitative one-vector telescope.**  The model powers contribute only powers of `‖Y‖`;
the one-step defect is evaluated on iterates of `X`. -/
theorem norm_pow_apply_sub_pow_apply_le (X Y : E →L[𝕜] E) (v : E) (r : ℕ) :
    ‖(X ^ r) v - (Y ^ r) v‖
      ≤ ∑ i ∈ Finset.range r,
          ‖Y‖ ^ (r - 1 - i) * ‖(X - Y) ((X ^ i) v)‖ := by
  rw [operator_pow_sub_eq_sum X Y r v]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  by_cases hpow : r - 1 - i = 0
  · simp [hpow]
  · refine le_trans ((Y ^ (r - 1 - i)).le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_right
      (norm_pow_le' Y (Nat.pos_of_ne_zero hpow)) (norm_nonneg _)

/-- A contraction stays a contraction on every power. -/
theorem norm_pow_apply_le_of_norm_le_one {Y : E →L[𝕜] E} (hY : ‖Y‖ ≤ 1) (k : ℕ) (w : E) :
    ‖(Y ^ k) w‖ ≤ ‖w‖ := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
      have hstep : (Y ^ (k + 1)) w = (Y ^ k) (Y w) := by
        rw [pow_succ]
        rfl
      rw [hstep]
      refine le_trans (ih (Y w)) ?_
      refine le_trans (Y.le_opNorm w) ?_
      exact mul_le_of_le_one_left (norm_nonneg _) hY

/-- **The telescope bound for a contraction model.**  Only the one-step errors on the iterates of
`X` appear; no power of `‖X‖` enters. -/
theorem norm_operator_pow_sub_le_of_norm_le_one (X : E →L[𝕜] E) {Y : E →L[𝕜] E} (hY : ‖Y‖ ≤ 1)
    (r : ℕ) (v : E) :
    ‖(X ^ r) v - (Y ^ r) v‖ ≤ ∑ i ∈ Finset.range r, ‖(X - Y) ((X ^ i) v)‖ := by
  rw [operator_pow_sub_eq_sum X Y r v]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  exact norm_pow_apply_le_of_norm_le_one hY _ _

open Filter Topology in
/-- **The telescope, in limit form.**  If every one-step error along the iterates of a family of
operators vanishes, so does the `m`-step error against a family of contraction models. -/
theorem tendsto_norm_operator_pow_sub_zero {X Y : ℕ → (E →L[𝕜] E)} (hY : ∀ n, ‖Y n‖ ≤ 1)
    (v : ℕ → E) (m : ℕ)
    (h : ∀ i < m, Tendsto (fun n : ℕ => ‖(X n - Y n) (((X n) ^ i) (v n))‖) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => ‖((X n) ^ m) (v n) - ((Y n) ^ m) (v n)‖) atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range m, ‖(X n - Y n) (((X n) ^ i) (v n))‖) atTop (nhds 0) := by
    have h0 : Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range m, ‖(X n - Y n) (((X n) ^ i) (v n))‖) atTop
        (nhds (∑ i ∈ Finset.range m, (0 : ℝ))) :=
      tendsto_finsetSum _ fun i hi => h i (Finset.mem_range.mp hi)
    simpa using h0
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
  exact norm_operator_pow_sub_le_of_norm_le_one (X n) (hY n) m (v n)

end GaloisForLFunctions.HTGeometry
