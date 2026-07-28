import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLadder

/-!
# The heat-Hankel conditions are nested

`riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg` states RH as nonnegativity of every
`xiHeatHankelForm N a t`.  That family is **decreasing in `N`**: nonnegativity at order `N` implies
it at every lower order, because a coefficient vector supported on the first `M` indices may be
extended by zero without changing the value of the form.

Two consequences.

*RH is the limit of a nested sequence of finite conditions.*  Order `N` is a condition on the
`(N×N)` Hankel matrix of the Gaussian-damped moments; the conditions tighten as `N` grows and RH is
their conjunction.  The corpus's `xiHeatTuranDefect` is the order-two rung.

*A single finite violation disproves RH.*  Contrapositively, if any `xiHeatHankelForm N a t` is
negative for some `N`, `a`, `t > 0`, then RH is false — and by nesting the same violation persists at
every higher order.  This is the disproof direction of the ladder, and it is finite at each rung.
-/

open Finset

namespace RHTower

/-- Truncation of a coefficient vector to its first `M` entries. -/
noncomputable def truncCoeff (M : ℕ) (a : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j < M then a j else 0

/-- **The form only sees the truncated coefficients.**  For `M ≤ N`, evaluating the order-`N` form
on a vector truncated at `M` gives the order-`M` form on the original vector. -/
theorem xiHeatHankelForm_truncCoeff {M N : ℕ} (hMN : M ≤ N) (a : ℕ → ℝ) (t : ℝ) :
    xiHeatHankelForm N (truncCoeff M a) t = xiHeatHankelForm M a t := by
  classical
  unfold xiHeatHankelForm
  have hsub : Finset.range M ⊆ Finset.range N := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hMN)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjM : j < M := Finset.mem_range.mp hj
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkM : k < M := Finset.mem_range.mp hk
      simp [truncCoeff, hjM, hkM]
    · intro k _ hk
      have hkM : ¬ k < M := fun h => hk (Finset.mem_range.mpr h)
      simp [truncCoeff, hkM]
  · intro j _ hj
    have hjM : ¬ j < M := fun h => hj (Finset.mem_range.mpr h)
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [truncCoeff, hjM]

/-- **Nesting.**  Nonnegativity of the order-`N` form for every coefficient vector implies it at
every order `M ≤ N`. -/
theorem xiHeatHankelForm_nonneg_of_le {M N : ℕ} (hMN : M ≤ N) {t : ℝ}
    (h : ∀ a : ℕ → ℝ, 0 ≤ xiHeatHankelForm N a t) (a : ℕ → ℝ) :
    0 ≤ xiHeatHankelForm M a t := by
  rw [← xiHeatHankelForm_truncCoeff hMN a t]
  exact h (truncCoeff M a)

/-- **A finite violation propagates upward.**  If the order-`M` form is negative at some vector,
then so is the order-`N` form for every `N ≥ M`, at the truncated vector. -/
theorem exists_neg_of_le_of_neg {M N : ℕ} (hMN : M ≤ N) {t : ℝ} {a : ℕ → ℝ}
    (hneg : xiHeatHankelForm M a t < 0) :
    ∃ b : ℕ → ℝ, xiHeatHankelForm N b t < 0 :=
  ⟨truncCoeff M a, by rw [xiHeatHankelForm_truncCoeff hMN a t]; exact hneg⟩

/-- **A single finite violation disproves RH.**  If any heat-Hankel form of any order is negative at
a positive time, the Riemann Hypothesis is false.  Each rung is a finite condition on an `N×N`
matrix of Gaussian-damped moments, so this is the ladder's disproof direction. -/
theorem not_riemannHypothesis_of_xiHeatHankelForm_neg {N : ℕ} {a : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hneg : xiHeatHankelForm N a t < 0) : ¬ RiemannHypothesis := by
  intro hRH
  have hall := (riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg).mp hRH
  exact absurd (hall N a t ht) (not_le.mpr hneg)

/-- **RH as a decreasing family.**  Nonnegativity at every order is equivalent to nonnegativity at
every order past any fixed starting point — the conditions are nested, so no initial segment carries
information the tail does not. -/
theorem riemannHypothesis_iff_forall_ge {N₀ : ℕ} :
    RiemannHypothesis ↔
      ∀ N : ℕ, N₀ ≤ N → ∀ (a : ℕ → ℝ) (t : ℝ), 0 < t → 0 ≤ xiHeatHankelForm N a t := by
  rw [riemannHypothesis_iff_forall_xiHeatHankelForm_nonneg]
  constructor
  · intro h N _ a t ht
    exact h N a t ht
  · intro h N a t ht
    exact xiHeatHankelForm_nonneg_of_le (le_max_left N N₀)
      (fun b => h (max N N₀) (le_max_right N N₀) b t ht) a

end RHTower
