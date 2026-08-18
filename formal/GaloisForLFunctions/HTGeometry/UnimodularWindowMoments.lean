import GaloisForLFunctions.HTGeometry.BlockRayleighLowerBound
import GaloisForLFunctions.HTGeometry.UnimodularMomentApproximation

/-!
# Prescribed moments from unimodular weights on a window

Combining the two halves of Andersson's argument at a single window:

* the Hankel system with a Rayleigh floor produces *disc* coefficients — the values of a polynomial
  bounded by one on the node interval — whose weighted moments hit any small enough target;
* rounding replaces those coefficients by *unimodular* ones at the cost of `J` times the size of a
  single moment vector.

The composite says: on a window carrying enough weighted nodes, unimodular coefficients realize any
prescribed moment vector up to an additive error `J · C`, where `C` bounds a single weight.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The Hankel image of a coefficient vector is the weighted nodal moment of its polynomial. -/
theorem mulVec_atomicHankel_apply {N J : ℕ} (w x : Fin N → ℝ) (c : Fin J → ℝ) (j : Fin J) :
    (atomicHankel w x J).mulVec c j
      = ∑ r : Fin N, w r * Polynomial.eval (x r) (Polynomial.ofFn J c) * x r ^ (j : ℕ) := by
  have hev : ∀ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J c)
      = ∑ i : Fin J, c i * x r ^ (i : ℕ) := by
    intro r
    rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_monomial]
  simp only [Matrix.mulVec, dotProduct, atomicHankel_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hev r, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add]
  ring

/-- **Unimodular realization of prescribed window moments.** -/
theorem exists_unimodular_window_moments {N J : ℕ} (hJ : 0 < J) {lam : ℝ} (hlam : 0 < lam)
    (x w : Fin N → ℝ) (hx : ∀ r, x r ∈ Set.Icc (0:ℝ) 1) {C : ℝ} (hC : ∀ r, |w r| ≤ C)
    (hC0 : 0 ≤ C)
    (hquad : ∀ a : Fin J → ℝ, lam * (∑ i, a i ^ 2) ≤ a ⬝ᵥ (atomicHankel w x J).mulVec a)
    (ξ : Fin J → ℝ) (hξ : (J : ℝ) * (∑ k, ξ k ^ 2) ≤ lam ^ 2) :
    ∃ b : Fin N → ℂ, (∀ r, ‖b r‖ = 1) ∧
      ∀ j : Fin J, ‖(∑ r : Fin N, b r * ((w r * x r ^ (j : ℕ) : ℝ) : ℂ)) - (ξ j : ℂ)‖
        ≤ (J : ℝ) * C := by
  classical
  obtain ⟨c, hc, hcbound⟩ := exists_unit_polynomial_solution hJ hlam x w hquad ξ hξ
  set a : Fin N → ℂ := fun r => ((Polynomial.eval (x r) (Polynomial.ofFn J c) : ℝ) : ℂ) with ha_def
  set v : Fin N → Fin J → ℂ := fun r j => ((w r * x r ^ (j : ℕ) : ℝ) : ℂ) with hv_def
  have ha : ∀ r, ‖a r‖ ≤ 1 := by
    intro r
    rw [ha_def]
    simpa using hcbound (x r) (hx r)
  have hvC : ∀ r j, ‖v r j‖ ≤ C := by
    intro r j
    rw [hv_def]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_mul, abs_pow]
    have hxr := hx r
    have hpow : |x r| ^ (j : ℕ) ≤ 1 := by
      rw [abs_of_nonneg hxr.1]
      exact pow_le_one₀ hxr.1 hxr.2
    calc |w r| * |x r| ^ (j : ℕ) ≤ |w r| * 1 :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = |w r| := by ring
      _ ≤ C := hC r
  obtain ⟨b, hb1, hb2⟩ := exists_unimodular_moment_approx v a ha hvC hC0
  refine ⟨b, hb1, fun j => ?_⟩
  have hmoment : (∑ r : Fin N, a r * v r j) = (ξ j : ℂ) := by
    have hreal : ∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J c) * (w r * x r ^ (j : ℕ))
        = ξ j := by
      rw [← congrFun hc j, mulVec_atomicHankel_apply]
      exact Finset.sum_congr rfl fun r _ => by ring
    calc (∑ r : Fin N, a r * v r j)
        = ∑ r : Fin N, ((Polynomial.eval (x r) (Polynomial.ofFn J c)
            * (w r * x r ^ (j : ℕ)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [ha_def, hv_def]
          push_cast
          ring
      _ = ((∑ r : Fin N, Polynomial.eval (x r) (Polynomial.ofFn J c)
            * (w r * x r ^ (j : ℕ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
      _ = (ξ j : ℂ) := by rw [hreal]
  have := hb2 j
  rwa [hmoment] at this

end GaloisForLFunctions.HTGeometry

end
