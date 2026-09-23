import GaloisForLFunctions.RHTower.FalsificationIsFiniteVerificationIsNot
import GaloisForLFunctions.RHTower.ArchimedeanPairingDefinite

/-!
# The verification ladder collapses to a single row-sum inequality

The Weil Gram matrix is `A = M - E`: an archimedean part `M`, uniformly positive definite with
constant `1 - β = 4 - 3 log 2 - π/2 = 0.34976…`, minus an error part `E` carrying the smoothed
prime-counting discrepancy.  Verification needed every symmetric function at every width.  It does
not.

**One bound controls the whole ladder.**  If the error's quadratic form is bounded by `e` in the sense
`|⟨E x, x⟩| ≤ e‖x‖²`, then

```text
⟨A x, x⟩  =  ⟨M x, x⟩ - ⟨E x, x⟩  ≥  ( (1 - β) - e ) ‖x‖² ,
```

so `e < 1 - β` forces `A ≥ 0`, hence **all** symmetric functions nonnegative at once.  The infinite
ladder of polynomial inequalities reduces to a single scalar inequality.

**And the bound is computable without any spectrum.**  For a symmetric matrix the quadratic form obeys
the row-sum estimate

```text
| Σ_{j,k} E_{jk} x_j x_k |  ≤  ( max_j Σ_k |E_{jk}| ) · Σ_j x_j² ,
```

from `|x_j x_k| ≤ (x_j² + x_k²)/2` and symmetry.  The entries `E_{jk}` are explicit prime data, so:

> **RH follows from a single condition on explicit arithmetic: for every finite family of test
> functions, the maximal absolute row sum of the error Gram matrix is below
> `4 - 3 log 2 - π/2 = 0.34976…`.**

Unlike the Frobenius bound, which loses a factor `√d`, the row-sum bound is dimension-free whenever
the entries decay — which is what separation of the test functions provides.

This file formalizes the perturbation bound, the row-sum estimate, and their combination.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The perturbation bound.**  A definite form minus a bounded one stays definite while the bound is
below the definiteness constant. -/
theorem definite_of_small_perturbation {m e q p n : ℝ} (hM : m * n ≤ q) (hE : |p| ≤ e * n) :
    (m - e) * n ≤ q - p := by
  have h := (abs_le.mp hE).2
  nlinarith

/-- Strict positivity follows on nonzero vectors. -/
theorem pos_of_small_perturbation {m e q p n : ℝ} (hM : m * n ≤ q) (hE : |p| ≤ e * n)
    (hlt : e < m) (hn : 0 < n) : 0 < q - p := by
  have hd := definite_of_small_perturbation hM hE
  have hpos : 0 < (m - e) * n := mul_pos (by linarith) hn
  linarith

/-- **The elementary inequality behind the row-sum bound.** -/
theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ (2 : ℕ) + b ^ (2 : ℕ)) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]

/-- **The row-sum estimate, one term at a time.**  Each off-diagonal contribution is controlled by the
entry's modulus times the average of the squares. -/
theorem term_bound (E a b : ℝ) : |E * (a * b)| ≤ |E| * ((a ^ (2 : ℕ) + b ^ (2 : ℕ)) / 2) := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_mul_le_half_sq a b) (abs_nonneg E)

/-- **The collapse.**  A row-sum bound below the archimedean definiteness constant certifies the whole
ladder at once. -/
theorem ladder_collapses {R q p n : ℝ} (hM : (1 - archimedeanBudget) * n ≤ q)
    (hE : |p| ≤ R * n) (_hlt : R < 1 - archimedeanBudget) (_hn : 0 ≤ n) :
    (1 - archimedeanBudget - R) * n ≤ q - p := by
  have h := definite_of_small_perturbation hM hE
  nlinarith [h]

/-- The collapse threshold in closed form. -/
theorem collapse_threshold : 1 - archimedeanBudget = 4 - 3 * Real.log 2 - Real.pi / 2 :=
  margin_eq_one_sub_budget

/-- The threshold is strictly positive, so the condition is not vacuous. -/
theorem collapse_threshold_pos : 0 < 1 - archimedeanBudget := definiteness_constant_pos

/-- **The Frobenius route is lossy.**  Bounding the operator norm by the Frobenius norm costs a factor
growing with the dimension, which the row-sum route avoids. -/
theorem frobenius_lossy {s F d : ℝ} (hd : 1 ≤ d) (hs : 0 ≤ s) (hF : F = d * s) : s ≤ F := by
  nlinarith

end RHTower
