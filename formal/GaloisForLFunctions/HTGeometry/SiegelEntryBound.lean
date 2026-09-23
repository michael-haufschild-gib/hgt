import GaloisForLFunctions.HTGeometry.SiegelGreedyPrimitive

/-!
# The Siegel entry bound

If a form and one of its congruates both lie in a Siegel set, the entries of the conjugating matrix
are constrained: the `i`-th diagonal entry of the congruate is the value of the original form at the
`i`-th column, so quasi-diagonality bounds every `dₖ γₖᵢ²` by it, while the Siegel bounds on the
congruate bound it in turn by a multiple of `d'ᵢ`.

This is the whole analytic content of Siegel's finiteness property.  What it leaves is arithmetic:
the entries of `γ` are integers, so a nonzero one has absolute value at least one, and the resulting
constraints on the ratios `d'ᵢ / dₖ` must be turned into a bound on the entries themselves.

* `congr_diag_eq_quadForm_col` : the diagonal of a congruate is the form at a column.
* `JacobiData.form_diag_le_pow` : on a Siegel set, `A_ii ≤ (1 + n tⁿ / 4) dᵢ`.
* `siegel_entry_bound` : **the entry bound.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The `i`-th diagonal entry of a congruate is the value of the form at the `i`-th column. -/
theorem congr_diag_eq_quadForm_col (A γ : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (γᵀ * A * γ) i i = (fun m => γ m i) ⬝ᵥ (A *ᵥ fun m => γ m i) := by
  classical
  show (γᵀ * A * γ) i i = ∑ m, γ m i * ∑ p, A m p * γ p i
  rw [Matrix.mul_apply]
  have hstep : ∀ p : Fin n, (γᵀ * A) i p = ∑ m, γ m i * A m p := by
    intro p
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [Matrix.transpose_apply]
  calc (∑ p, (γᵀ * A) i p * γ p i) = ∑ p, ∑ m, γ m i * A m p * γ p i := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hstep p, Finset.sum_mul]
    _ = ∑ m, ∑ p, γ m i * A m p * γ p i := Finset.sum_comm
    _ = ∑ m, γ m i * ∑ p, A m p * γ p i := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring

/-- **On a Siegel set the diagonal entries are bounded by the corresponding Jacobi entry.** -/
theorem JacobiData.form_diag_le_pow (J : JacobiData n) {t u : ℝ} (ht : 1 ≤ t)
    (hS : J.IsSiegel t u) (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2) (i : Fin n) :
    J.form i i ≤ (1 + (n : ℝ) / 4 * t ^ n) * J.d i := by
  classical
  refine le_trans (J.form_diag_le hred i) ?_
  have hbound : ∀ m ∈ Finset.univ.filter (fun m : Fin n => m < i), J.d m ≤ t ^ n * J.d i := by
    intro m hm
    rw [Finset.mem_filter] at hm
    exact J.d_le_pow_n ht hS (le_of_lt (Fin.lt_def.1 hm.2))
  have hsum : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m < i), J.d m)
      ≤ (n : ℝ) * (t ^ n * J.d i) := by
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (pow_nonneg (le_trans zero_le_one ht) n) (J.pos i).le)
    have hcard : (Finset.univ.filter (fun m : Fin n => m < i)).card ≤ n := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
    exact_mod_cast hcard
  have htn : (0 : ℝ) < t ^ n := pow_pos (lt_of_lt_of_le zero_lt_one ht) n
  nlinarith [hsum, J.pos i, htn]

/-- **The Siegel entry bound.**  If a form and its congruate by `γ` both lie in a Siegel set, then
every `dₖ γₖᵢ²` is bounded by a fixed multiple of `d'ᵢ`. -/
theorem siegel_entry_bound {J J' : JacobiData n} {t u c : ℝ} (ht : 1 ≤ t) (hc : 0 < c)
    (hS' : J'.IsSiegel t u) (hred' : ∀ a b : Fin n, a < b → |J'.U a b| ≤ 1 / 2)
    {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : J'.form = γᵀ * J.form * γ)
    (hquasi : ∀ v : Fin n → ℝ, c * (∑ m, J.d m * (v m) ^ (2 : ℕ)) ≤ v ⬝ᵥ (J.form *ᵥ v))
    (k i : Fin n) :
    c * (J.d k * (γ k i) ^ (2 : ℕ)) ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := by
  classical
  set v : Fin n → ℝ := fun m => γ m i with hv
  have hcol : J'.form i i = v ⬝ᵥ (J.form *ᵥ v) := by
    rw [hγ]
    exact congr_diag_eq_quadForm_col _ _ i
  have hlow : c * (J.d k * (v k) ^ (2 : ℕ)) ≤ c * (∑ m, J.d m * (v m) ^ (2 : ℕ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    exact Finset.single_le_sum (f := fun m => J.d m * (v m) ^ (2 : ℕ))
      (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg _)) (Finset.mem_univ k)
  calc c * (J.d k * (γ k i) ^ (2 : ℕ)) = c * (J.d k * (v k) ^ (2 : ℕ)) := rfl
    _ ≤ c * (∑ m, J.d m * (v m) ^ (2 : ℕ)) := hlow
    _ ≤ v ⬝ᵥ (J.form *ᵥ v) := hquasi v
    _ = J'.form i i := hcol.symm
    _ ≤ (1 + (n : ℝ) / 4 * t ^ n) * J'.d i := J'.form_diag_le_pow ht hS' hred' i

end GaloisForLFunctions.HTGeometry
