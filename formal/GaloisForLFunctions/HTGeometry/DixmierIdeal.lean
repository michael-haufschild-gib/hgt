import GaloisForLFunctions.HTGeometry.SingularValues

/-!
# The Dixmier ideal `L^{1,∞}` and its decay criterion

The weak-Schatten (Dixmier–Macaev) ideal `L^{1,∞}` consists of the compact operators whose
singular-value partial sums `σ_N(T) = ∑_{n<N} s_n(T)` grow at most logarithmically.  This is the
ideal on which the Dixmier trace lives, and membership in it is the recurring "critical order"
hypothesis of the quasi-inner residue theorems: an operator built from a Hardy Hankel block whose
symbol decays like `1/√·` has singular values `s_n ~ 1/n`, hence `σ_N = O(log N)`.

Built here on top of the tree's singular-value stack (`ContinuousLinearMap.singVal`):

* `sum_inv_succ_le_one_add_log` — the harmonic bound `∑_{n<N} 1/(n+1) ≤ 1 + log N`, from the
  concavity estimate `1/(a+1) ≤ log(a+1) − log a`.
* `dixmierPartialSum`, `IsDixmier` — the logarithmic partial sum and the `L^{1,∞}` predicate.
* `isDixmier_of_singVal_decay` — **the decay criterion**: singular values `≤ C/(n+1)` force
  `L^{1,∞}` membership with `σ_N ≤ C(1 + log N)`.
-/

open Finset

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The one-step logarithmic lower bound `1/(a+1) ≤ log(a+1) − log a`, from `log x ≤ x − 1` applied
to `x = a/(a+1)`. -/
theorem log_succ_lower (a : ℝ) (ha : 0 < a) :
    (1:ℝ) / (a + 1) ≤ Real.log (a + 1) - Real.log a := by
  have ha1 : (0:ℝ) < a + 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < a / (a + 1) from div_pos ha ha1)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt ha1)] at hlog
  have ha1' : a + 1 ≠ 0 := ne_of_gt ha1
  have hrhs : a / (a + 1) - 1 = -(1 / (a + 1)) := by field_simp; ring
  rw [hrhs] at hlog
  linarith

/-- **Harmonic bound.**  `∑_{n<N} 1/(n+1) ≤ 1 + log N` for `N ≥ 1`, by induction telescoping the
one-step estimate `log_succ_lower`. -/
theorem sum_inv_succ_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, (1:ℝ) / ((n:ℝ) + 1) ≤ 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_range_succ]
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hterm := log_succ_lower (N:ℝ) hNpos
    have hcast : ((N:ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    have hstep : Real.log ((N:ℝ)) ≤ Real.log ((N+1:ℕ):ℝ) - (1 / ((N:ℝ)+1)) := by
      rw [← hcast]; linarith
    linarith [ih]

/-- The `N`-th logarithmic partial sum of the singular values of `T`. -/
noncomputable def dixmierPartialSum (T : H →L[ℂ] H) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, singVal T n

/-- **Weak-Schatten `L^{1,∞}` (Dixmier ideal) membership.**  `T` lies in the Dixmier ideal when its
singular-value partial sums grow at most logarithmically. -/
def IsDixmier (T : H →L[ℂ] H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → dixmierPartialSum T N ≤ C * (1 + Real.log N)

/-- **The decay criterion.**  A compact operator whose singular values decay like `C/(n+1)` lies in
the Dixmier ideal `L^{1,∞}`: the harmonic partial sums are `≤ C(1 + log N)`. -/
theorem isDixmier_of_singVal_decay {T : H →L[ℂ] H} {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ n, singVal T n ≤ C / ((n:ℝ) + 1)) : IsDixmier T := by
  refine ⟨C, hC, fun N hN => ?_⟩
  have h1 : dixmierPartialSum T N ≤ ∑ n ∈ Finset.range N, C / ((n:ℝ) + 1) :=
    Finset.sum_le_sum (fun n _ => hdecay n)
  have h2 : ∑ n ∈ Finset.range N, C / ((n:ℝ) + 1)
      = C * ∑ n ∈ Finset.range N, (1:ℝ) / ((n:ℝ) + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by rw [mul_one_div])
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (sum_inv_succ_le_one_add_log N hN) hC)

end ContinuousLinearMap
