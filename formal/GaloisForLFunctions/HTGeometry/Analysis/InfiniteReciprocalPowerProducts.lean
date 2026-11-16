import GaloisForLFunctions.HTGeometry.Analysis.ReciprocalPowerProducts
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite reciprocal-power products

The uniform finite-product envelope proves convergence without a logarithmic
series estimate. At exponent two the telescoping limit equals two.
-/

namespace GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts

open Finset Filter
open scoped Topology

/-- Reciprocal-power factors have a convergent unordered infinite product. -/
theorem multipliable_factors (k : ℕ) :
    Multipliable (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹) := by
  let F := fun S : Finset ℕ => ∏ n ∈ S, (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹
  have hm : Monotone F := by
    intro S T hST
    apply Finset.prod_le_prod_of_subset_of_one_le hST
    · intro n _
      exact (inv_pos.mpr (factor_pos k n)).le
    · intro n _ _
      exact (one_le_inv₀ (factor_pos k n)).mpr (sub_le_self _ (by positivity))
  have hb : BddAbove (Set.range F) := by
    refine ⟨(slope k + 1) / slope k, ?_⟩
    rintro _ ⟨S, rfl⟩
    exact (subproduct_lt_uniform k S).le
  exact ⟨⨆ S, F S, tendsto_atTop_ciSup hm hb⟩

/-- The infinite product represented by the constant-index zeta-star tail. -/
noncomputable def infiniteProduct (k : ℕ) : ℝ :=
  ∏' n : ℕ, (1 - 1 / ((n : ℝ) + 2) ^ (k + 2))⁻¹

theorem product_tendsto (k : ℕ) :
    Tendsto (product k) atTop (𝓝 (infiniteProduct k)) :=
  (multipliable_factors k).hasProd.tendsto_prod_nat

/-- The rational envelope survives the infinite-product limit. -/
theorem infiniteProduct_le_uniform (k : ℕ) :
    infiniteProduct k ≤ (slope k + 1) / slope k :=
  hasProd_le_of_prod_le (multipliable_factors k).hasProd
    (fun S => (subproduct_lt_uniform k S).le)

theorem infiniteProduct_ge_one (k : ℕ) : 1 ≤ infiniteProduct k :=
  ge_of_tendsto' (product_tendsto k) (product_ge_one k)

/-- The quadratic infinite product is exactly two. -/
theorem infiniteProduct_quadratic : infiniteProduct 0 = 2 := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have heq (n : ℕ) : product 0 n = 2 - 2 / ((n : ℝ) + 2) := by
    rw [product_quadratic]
    field_simp
    ring
  have hlim : Tendsto (product 0) atTop (𝓝 2) := by
    simpa only [← heq, sub_zero] using (tendsto_const_nhds (x := (2 : ℝ))).sub hdiv
  exact tendsto_nhds_unique (product_tendsto 0) hlim

#print axioms multipliable_factors
#print axioms infiniteProduct_quadratic

end GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts
