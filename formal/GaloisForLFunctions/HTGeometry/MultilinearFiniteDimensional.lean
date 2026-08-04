import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Multilinear maps on a finite coordinate space are bounded

A multilinear map whose arguments run over a finite coordinate space is determined by its values on
tuples of coordinate vectors, so expanding each argument in coordinates bounds it by the sum of those
values.  Hence every such multilinear map is continuous, and the alternating maps on a finite
coordinate space are exactly the continuous alternating maps.  Mathlib has the
bounded-implies-continuous direction but not this boundedness.

* `multilinearMap_bound` : the bound by the values on tuples of coordinate vectors.
* `alternatingMapToContinuous` : an alternating map on a finite coordinate space is continuous.
* `continuousAlternatingEquiv` : that identification, as a linear equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

section Bound

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A multilinear map on a finite coordinate space is bounded** by the sum of its values on the
tuples of coordinate vectors. -/
theorem multilinearMap_bound (f : MultilinearMap 𝕜 (fun _ : ι => (Fin r → 𝕜)) F) :
    ∀ v : ι → (Fin r → 𝕜),
      ‖f v‖ ≤ (∑ φ : ι → Fin r, ‖f fun i => (Pi.single (φ i) (1 : 𝕜) : Fin r → 𝕜)‖) *
        ∏ i, ‖v i‖ := by
  intro v
  have hcoord : ∀ i : ι, v i = ∑ j : Fin r, v i j • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
    intro i
    funext l
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single l]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  have hexpand : f v = ∑ φ : ι → Fin r,
      (∏ i, v i (φ i)) • f fun i => (Pi.single (φ i) (1 : 𝕜) : Fin r → 𝕜) := by
    conv_lhs => rw [show v = fun i => ∑ j : Fin r, v i j • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) from
      funext hcoord]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [MultilinearMap.map_smul_univ]
  rw [hexpand]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun φ _ => ?_
  rw [norm_smul, norm_prod]
  calc (∏ i, ‖v i (φ i)‖) * ‖f fun i => (Pi.single (φ i) (1 : 𝕜) : Fin r → 𝕜)‖
      ≤ (∏ i, ‖v i‖) * ‖f fun i => (Pi.single (φ i) (1 : 𝕜) : Fin r → 𝕜)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
          fun i _ => norm_le_pi_norm (v i) (φ i)
    _ = ‖f fun i => (Pi.single (φ i) (1 : 𝕜) : Fin r → 𝕜)‖ * ∏ i, ‖v i‖ := mul_comm _ _

/-- **An alternating map on a finite coordinate space is a continuous alternating map.** -/
noncomputable def alternatingMapToContinuous (f : (Fin r → 𝕜) [⋀^ι]→ₗ[𝕜] F) :
    (Fin r → 𝕜) [⋀^ι]→L[𝕜] F :=
  f.mkContinuous (∑ φ : ι → Fin r, ‖f fun i => (Pi.single (φ i) (1 : 𝕜) : Fin r → 𝕜)‖)
    (multilinearMap_bound f.toMultilinearMap)

@[simp]
theorem alternatingMapToContinuous_apply (f : (Fin r → 𝕜) [⋀^ι]→ₗ[𝕜] F) (v : ι → (Fin r → 𝕜)) :
    alternatingMapToContinuous f v = f v := rfl

/-- **On a finite coordinate space the alternating maps are exactly the continuous alternating
maps**, and the identification is linear. -/
noncomputable def continuousAlternatingEquiv (𝕜 : Type*) [NontriviallyNormedField 𝕜] (r : ℕ)
    (ι : Type*) [Fintype ι] [DecidableEq ι] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] : ((Fin r → 𝕜) [⋀^ι]→ₗ[𝕜] F) ≃ₗ[𝕜] ((Fin r → 𝕜) [⋀^ι]→L[𝕜] F) where
  toFun := alternatingMapToContinuous
  map_add' f g := by
    refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
    ext v
    rfl
  map_smul' c f := by
    refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
    ext v
    rfl
  invFun := ContinuousAlternatingMap.toAlternatingMap
  left_inv f := by
    ext v
    rfl
  right_inv f := by
    refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
    ext v
    rfl

@[simp]
theorem continuousAlternatingEquiv_symm_apply (f : (Fin r → 𝕜) [⋀^ι]→L[𝕜] F) :
    (continuousAlternatingEquiv 𝕜 r ι F).symm f = f.toAlternatingMap := rfl

end Bound

end GaloisForLFunctions.HTGeometry
