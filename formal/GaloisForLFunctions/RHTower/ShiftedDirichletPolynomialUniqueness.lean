import Mathlib
import GaloisForLFunctions.RHTower.GeneralizedDirichletSeriesInjectivity

/-!
# Uniqueness for shifted Dirichlet polynomials

For `α > 0`, a finite sum `Σ_{n<N} c_n (n+α)^{-z}` that vanishes on a neighbourhood of one point has all
coefficients zero: it is entire, hence identically zero, and on the real axis it is a generalized
Dirichlet series with the strictly increasing frequencies `log(n+α) - log α + 1 > 0`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The shifted Dirichlet polynomial `Σ_{n<N} c_n (n+α)^{-z}`. -/
def shiftedDirichletPoly (α : ℝ) (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, c n * (((n : ℝ) + α : ℝ) : ℂ) ^ (-z)

theorem differentiable_shiftedDirichletPoly {α : ℝ} (hα : 0 < α) (N : ℕ) (c : ℕ → ℂ) :
    Differentiable ℂ (shiftedDirichletPoly α N c) := by
  intro z
  unfold shiftedDirichletPoly
  refine DifferentiableAt.fun_sum fun n _ => (differentiableAt_const _).mul ?_
  have hne : (((n : ℝ) + α : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + α := by positivity
    exact_mod_cast this.ne'
  exact (differentiableAt_id.neg).const_cpow (Or.inl hne)

/-- **Uniqueness.** -/
theorem shiftedDirichletPoly_coeff_eq_zero {α : ℝ} (hα : 0 < α) {N : ℕ} {c : ℕ → ℂ} {z₀ : ℂ}
    (h : shiftedDirichletPoly α N c =ᶠ[𝓝 z₀] 0) : ∀ n < N, c n = 0 := by
  have hG := differentiable_shiftedDirichletPoly hα N c
  have hzero : ∀ z, shiftedDirichletPoly α N c z = 0 := by
    have hA : AnalyticOnNhd ℂ (shiftedDirichletPoly α N c) Set.univ :=
      hG.differentiableOn.analyticOnNhd isOpen_univ
    intro z
    exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z₀) h
      (Set.mem_univ z)
  set mu : ℕ → ℝ := fun n => Real.log ((n : ℝ) + α) - Real.log α + 1 with hmu
  have hmono : StrictMono mu := by
    intro m n hmn
    simp only [hmu]
    have : Real.log ((m : ℝ) + α) < Real.log ((n : ℝ) + α) :=
      Real.log_lt_log (by positivity) (by
        have : (m : ℝ) < n := by exact_mod_cast hmn
        linarith)
    linarith
  have hmu0 : 0 < mu 0 := by simp [hmu]
  set a : ℕ → ℂ := fun n => if n < N then c n else 0 with ha
  have hsum : Summable fun n => ‖a n‖ := by
    refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
    simp only [ha, Finset.mem_range] at hn ⊢
    simp [hn]
  have hser : ∀ x : ℝ, GaloisForLFunctions.RHTower.generalizedDirichletSeries mu a x =
      Complex.exp (((Real.log α - 1 : ℝ) : ℂ) * x) * shiftedDirichletPoly α N c x := by
    intro x
    unfold GaloisForLFunctions.RHTower.generalizedDirichletSeries shiftedDirichletPoly
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [ha, Finset.mem_range] at hn ⊢; simp [hn]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    simp only [ha, hn, if_true]
    have hpos : (0 : ℝ) < (n : ℝ) + α := by positivity
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [hmu]; push_cast; ring
  have hzeroSer : (fun x : ℝ => GaloisForLFunctions.RHTower.generalizedDirichletSeries mu a x) =ᶠ[atTop] 0 :=
    Filter.Eventually.of_forall fun x => by
      show GaloisForLFunctions.RHTower.generalizedDirichletSeries mu a x = 0
      rw [hser, hzero, mul_zero]
  have hall := GaloisForLFunctions.RHTower.generalizedDirichletSeries_coeff_eq_zero_of_eventuallyEq_zero hmono hmu0 hsum hzeroSer
  intro n hn
  have := hall n
  simpa [ha, hn] using this

end

end RHTower
