import Mathlib

/-!
# The zero set of a nonzero polynomial is nowhere dense

A nonempty open subset of `σ → ℂ`, for a finite `σ`, contains a box of balls, and every complex ball
is infinite; a polynomial vanishing on a box with infinite sides is zero.  So the zero set of a
nonzero polynomial has empty interior, and countably many such sets cannot cover a nonempty open set.
-/

open Metric Set MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every complex ball of positive radius is infinite. -/
theorem infinite_ball_complex (c : ℂ) {r : ℝ} (hr : 0 < r) : (Metric.ball c r).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => c + ((r / ((n : ℝ) + 2) : ℝ) : ℂ)) ?_ ?_
  · intro m n hmn
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h : (r / ((m : ℝ) + 2)) = (r / ((n : ℝ) + 2)) := by
      have hsub := congrArg (fun z : ℂ => z - c) hmn
      simp only [add_sub_cancel_left] at hsub
      exact_mod_cast hsub
    have h2 : r * ((n : ℝ) + 2) = r * ((m : ℝ) + 2) := (div_eq_div_iff hm.ne' hn.ne').mp h
    have h3 : ((n : ℝ) + 2) = ((m : ℝ) + 2) := mul_left_cancel₀ hr.ne' h2
    have h4 : (m : ℝ) = (n : ℝ) := by linarith
    exact_mod_cast h4
  · intro n
    have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [Metric.mem_ball, dist_eq_norm]
    have hval : ‖c + ((r / ((n : ℝ) + 2) : ℝ) : ℂ) - c‖ = r / ((n : ℝ) + 2) := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hval]
    exact div_lt_self hr hn2

/-- **A nonzero polynomial does not vanish on a nonempty open set.** -/
theorem exists_eval_ne_zero_of_isOpen {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ≠ 0) {U : Set (σ → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, MvPolynomial.eval x p ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  refine hp ?_
  refine MvPolynomial.funext_set (p := p) (q := 0)
    (fun i => Metric.ball (x₀ i) r) (fun i => infinite_ball_complex (x₀ i) hr) ?_
  intro x hx
  have hxU : x ∈ U := hball (by rw [ball_pi x₀ hr]; exact hx)
  rw [map_zero]
  exact hcon x hxU

/-- **The zero set of a nonzero polynomial has empty interior.** -/
theorem interior_zeroSet_eq_empty {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ} (hp : p ≠ 0) :
    interior {x : σ → ℂ | MvPolynomial.eval x p = 0} = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨y, hyU, hy⟩ := exists_eval_ne_zero_of_isOpen hp isOpen_interior ⟨x, hx⟩
  have hmem : y ∈ {x : σ → ℂ | MvPolynomial.eval x p = 0} := interior_subset hyU
  exact hy hmem

/-- The zero set of a polynomial is closed. -/
theorem isClosed_zeroSet {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) :
    IsClosed {x : σ → ℂ | MvPolynomial.eval x p = 0} := by
  have hcont : Continuous fun x : σ → ℂ => MvPolynomial.eval x p :=
    MvPolynomial.continuous_eval p
  simpa using isClosed_eq hcont continuous_const

/-- **The non-vanishing locus of a nonzero polynomial is dense.** -/
theorem zeroSet_dense_compl {σ : Type*} [Fintype σ] {p : MvPolynomial σ ℂ} (hp : p ≠ 0) :
    Dense {x : σ → ℂ | MvPolynomial.eval x p ≠ 0} := by
  have hset : {x : σ → ℂ | MvPolynomial.eval x p ≠ 0} =
      {x : σ → ℂ | MvPolynomial.eval x p = 0}ᶜ := rfl
  rw [hset, ← interior_eq_empty_iff_dense_compl]
  exact interior_zeroSet_eq_empty hp

/-- **The non-vanishing locus of a nonzero polynomial is dense and open.** -/
theorem isOpen_nonvanishing {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) :
    IsOpen {x : σ → ℂ | MvPolynomial.eval x p ≠ 0} := by
  have hset : {x : σ → ℂ | MvPolynomial.eval x p ≠ 0} =
      {x : σ → ℂ | MvPolynomial.eval x p = 0}ᶜ := rfl
  rw [hset]
  exact (isClosed_zeroSet p).isOpen_compl

end

end GaloisForLFunctions.HTGeometry
