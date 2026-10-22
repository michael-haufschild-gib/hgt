import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The ultranull packet: moment cancellation and its coefficient cost

Three ingredients build the packet.  A linear map from a space of dimension `n` into one of smaller
dimension has a nonzero kernel, so a unit coefficient vector annihilating the first `n-1` moments
of the ordinate offsets always exists.  Cauchy–Schwarz against the constant one turns a uniform
per-term remainder bound into the aggregate bound `√n ε`, which is the shape of the Taylor estimate.
And the multiplicity-collapsed coefficients cost at most the maximal multiplicity, so the packet
norm is bounded below by its reciprocal.

Together these are the abstract content of the construction: the packet's unregularized energy can
be pushed below any prescribed ridge scale, because the factorial in the remainder beats the
multiplicity factor.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(439)`: the moment kernel is nonzero -/

/-- **`(439)`: fewer constraints than unknowns leaves a nonzero solution.** -/
theorem exists_ne_zero_mem_ker {n m : ℕ} (h : m < n) (f : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ f v = 0 := by
  have hninj : ¬ Function.Injective f := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective (f := f) hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at hle
    omega
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro hcon
    exact hninj (LinearMap.ker_eq_bot.mp hcon)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, hv⟩

/-! ## `(440)`: the aggregate remainder -/

/-- **`(440)`: a uniform per-term remainder bound aggregates with the factor `√n`.** -/
theorem norm_sum_le_sqrt_card_mul {n : ℕ} (d R : Fin n → ℂ) {ε : ℝ}
    (hd : ∑ k, ‖d k‖ ^ (2 : ℕ) = 1) (hR : ∀ k, ‖R k‖ ≤ ε) (hε : 0 ≤ ε) :
    ‖∑ k, d k * R k‖ ≤ Real.sqrt n * ε := by
  have hterm : ∀ k : Fin n, ‖d k * R k‖ ≤ ‖d k‖ * ε := by
    intro k
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hR k) (norm_nonneg _)
  have hsum : ‖∑ k, d k * R k‖ ≤ ∑ k, ‖d k‖ * ε := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun k _ => hterm k
  have hcs : (∑ k : Fin n, ‖d k‖) ^ (2 : ℕ) ≤ (n : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k : Fin n => ‖d k‖)
      (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    rw [hd, one_mul] at h
    exact h
  have hnn : (0 : ℝ) ≤ ∑ k : Fin n, ‖d k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hle : (∑ k : Fin n, ‖d k‖) ≤ Real.sqrt n := by
    rw [show (Real.sqrt n : ℝ) = Real.sqrt ((n : ℝ)) from rfl]
    calc (∑ k : Fin n, ‖d k‖) = Real.sqrt ((∑ k : Fin n, ‖d k‖) ^ (2 : ℕ)) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hcs
  calc ‖∑ k, d k * R k‖ ≤ ∑ k, ‖d k‖ * ε := hsum
    _ = (∑ k : Fin n, ‖d k‖) * ε := by rw [← Finset.sum_mul]
    _ ≤ Real.sqrt n * ε := mul_le_mul_of_nonneg_right hle hε

/-! ## `(441)`: the multiplicity cost -/

/-- **`(441)`: collapsing by the multiplicities costs at most the maximal multiplicity.** -/
theorem coefficient_norm_sq_ge_inv {n : ℕ} (d : Fin n → ℂ) (m : Fin n → ℝ) {M : ℝ}
    (hm : ∀ k, 0 < m k) (hmM : ∀ k, m k ≤ M) (hd : ∑ k, ‖d k‖ ^ (2 : ℕ) = 1) :
    1 / M ≤ ∑ k, ‖d k‖ ^ (2 : ℕ) / m k := by
  have hterm : ∀ k : Fin n, ‖d k‖ ^ (2 : ℕ) / M ≤ ‖d k‖ ^ (2 : ℕ) / m k := by
    intro k
    exact div_le_div_of_nonneg_left (by positivity) (hm k) (hmM k)
  calc 1 / M = (∑ k : Fin n, ‖d k‖ ^ (2 : ℕ)) / M := by rw [hd]
    _ = ∑ k : Fin n, ‖d k‖ ^ (2 : ℕ) / M := by rw [Finset.sum_div]
    _ ≤ ∑ k : Fin n, ‖d k‖ ^ (2 : ℕ) / m k := Finset.sum_le_sum fun k _ => hterm k

end GaloisForLFunctions.RHTower
