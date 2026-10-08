import GaloisForLFunctions.RHTower.WeilPaperMixtureRealification

/-!
# Positive cubes of finite Weil mixtures

A common positive background and finitely many positive endpoint pairs provide
independent convex parameters. Linear observations and differences admit exact
finite-sum formulas, so null constraints can be imposed before normalization.
-/

open scoped BigOperators
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A positive background plus independently interpolated endpoint pairs. -/
def paperMixtureCube {n : ℕ} (u : WeilTestFn →₀ ℝ)
    (p q : Fin n → WeilTestFn →₀ ℝ) (t : Fin n → Set.Icc (0 : ℝ) 1) :
    WeilTestFn →₀ ℝ :=
  u + ∑ i, ((1 - (t i).1) • q i + (t i).1 • p i)

/-- Linear observations retain the exact affine dependence on every coordinate. -/
theorem paperMixtureCube_observe {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] E) (u : WeilTestFn →₀ ℝ)
    (p q : Fin n → WeilTestFn →₀ ℝ) (t : Fin n → Set.Icc (0 : ℝ) 1) :
    T (paperMixtureCube u p q t) =
      T u + ∑ i, ((1 - (t i).1) • T (q i) + (t i).1 • T (p i)) := by
  simp only [paperMixtureCube, map_add, map_sum, map_smul]

/-- Agreement of every endpoint pair makes the whole observation vector constant. -/
theorem paperMixtureCube_observe_eq {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] E) (u : WeilTestFn →₀ ℝ)
    (p q : Fin n → WeilTestFn →₀ ℝ) (h : ∀ i, T (p i) = T (q i))
    (t : Fin n → Set.Icc (0 : ℝ) 1) :
    T (paperMixtureCube u p q t) = T u + ∑ i, T (q i) := by
  simp only [paperMixtureCube_observe, h, ← add_smul, sub_add_cancel, one_smul]

/-- Every point of the cube is a nonnegative actual finite mixture. -/
theorem paperMixtureCube_nonneg {n : ℕ} (u : WeilTestFn →₀ ℝ)
    (p q : Fin n → WeilTestFn →₀ ℝ) (hu : ∀ f, 0 ≤ u f)
    (hp : ∀ i f, 0 ≤ p i f) (hq : ∀ i f, 0 ≤ q i f)
    (t : Fin n → Set.Icc (0 : ℝ) 1) :
    ∀ f, 0 ≤ paperMixtureCube u p q t f := by
  intro f
  change 0 ≤ u f + (∑ i, ((1 - (t i).1) • q i + (t i).1 • p i)) f
  rw [Finsupp.finsetSum_apply]
  exact add_nonneg (hu f) (Finset.sum_nonneg fun i _ =>
    add_nonneg (mul_nonneg (sub_nonneg.mpr (t i).property.2) (hq i f))
      (mul_nonneg (t i).property.1 (hp i f)))

/-- Differences are exactly linear combinations of the endpoint differences. -/
theorem paperMixtureCube_sub {n : ℕ} (u : WeilTestFn →₀ ℝ)
    (p q : Fin n → WeilTestFn →₀ ℝ) (s t : Fin n → Set.Icc (0 : ℝ) 1) :
    paperMixtureCube u p q s - paperMixtureCube u p q t =
      ∑ i, ((s i).1 - (t i).1) • (p i - q i) := by
  rw [paperMixtureCube, paperMixtureCube, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  module

end RHTower.WeilWorkPBAP
