import GaloisForLFunctions.RHTower.HurwitzZetaRightAsymptotics
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Periodic Dirichlet series far to the right of the critical strip

For a periodic coefficient function the Dirichlet series `∑_{n ≥ 1} Θ(n) n^{-w}`
is dominated by its first non-vanishing term.  If `Θ(n) = 0` for `1 ≤ n < n₀`,
normalising by `n₀^{w}` turns the series into `∑_{n ≥ n₀} Θ(n) (n₀/n)^{w}`, whose
leading term is `Θ(n₀)` and whose tail is bounded by a fixed constant times
`(n₀/(n₀+1))^{Re w}`.

So `n₀^{w} L(Θ,w) → Θ(n₀)` as `Re w → ∞`: the series grows exactly like the
geometric factor `n₀^{-Re w}`, and `n₀` is the first exponent of the underlying
Dirichlet series.
-/

open Complex Filter Topology

namespace RHTower

section PeriodicRight

variable {N : ℕ} [NeZero N]

theorem exists_bound_zmod (Θ : ZMod N → ℂ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ‖Θ j‖ ≤ M := by
  obtain ⟨M, hM⟩ := (Set.finite_range (fun j => ‖Θ j‖)).bddAbove
  exact ⟨max M 0, le_max_right _ _, fun j => le_trans (hM ⟨j, rfl⟩) (le_max_left _ _)⟩

theorem norm_natCast_cpow {n : ℕ} (hn : 0 < n) (w : ℂ) :
    ‖(n : ℂ) ^ w‖ = (n : ℝ) ^ w.re := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]

theorem norm_scaled_term (Θ : ZMod N → ℂ) {M : ℝ} (hM : ∀ j, ‖Θ j‖ ≤ M)
    {n₀ m : ℕ} (hn₀ : 0 < n₀) (hm : 0 < m) (w : ℂ) :
    ‖(n₀ : ℂ) ^ w * LSeries.term (fun n : ℕ => Θ (n : ZMod N)) w m‖
      ≤ M * (((n₀ : ℝ)) / ((m : ℝ))) ^ w.re := by
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [LSeries.term_of_ne_zero hm.ne' , norm_mul, norm_div,
    norm_natCast_cpow hn₀ w, norm_natCast_cpow hm w, Real.div_rpow hn₀R.le hmR.le]
  have hpow : (0 : ℝ) < ((m : ℝ)) ^ w.re := Real.rpow_pos_of_pos hmR _
  have hn₀pow : (0 : ℝ) < ((n₀ : ℝ)) ^ w.re := Real.rpow_pos_of_pos hn₀R _
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm ((n₀ : ℝ) ^ w.re)]
  refine mul_le_mul_of_nonneg_right (le_trans ?_ (le_of_eq rfl)) (le_of_lt hn₀pow) |>.trans ?_
  · exact le_of_eq rfl
  · rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hn₀pow) |>.trans (le_of_eq ?_)
    · exact le_of_eq rfl
    · ring

end PeriodicRight

end RHTower
