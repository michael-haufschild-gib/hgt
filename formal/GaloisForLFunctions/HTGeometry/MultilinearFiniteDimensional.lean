import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Multilinear maps on a finite coordinate space are bounded

A multilinear map whose arguments run over a finite coordinate space is determined by its values on
tuples of coordinate vectors, so expanding each argument in coordinates bounds it by the sum of those
values.  Hence every such multilinear map is continuous, and every alternating map is a continuous
alternating map.  Mathlib has the bounded-implies-continuous direction but not this boundedness.

* `multilinearMap_bound` : the bound by the values on tuples of coordinate vectors.
* `alternatingMapToContinuous` : an alternating map on a finite coordinate space is continuous.
-/

namespace GaloisForLFunctions.HTGeometry

section Bound

variable {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **A multilinear map on a finite coordinate space is bounded** by the sum of its values on the
tuples of coordinate vectors. -/
theorem multilinearMap_bound (f : MultilinearMap ℂ (fun _ : ι => (Fin r → ℂ)) F) :
    ∀ v : ι → (Fin r → ℂ),
      ‖f v‖ ≤ (∑ φ : ι → Fin r, ‖f fun i => (Pi.single (φ i) (1 : ℂ) : Fin r → ℂ)‖) *
        ∏ i, ‖v i‖ := by
  intro v
  have hcoord : ∀ i : ι, v i = ∑ j : Fin r, v i j • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
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
      (∏ i, v i (φ i)) • f fun i => (Pi.single (φ i) (1 : ℂ) : Fin r → ℂ) := by
    conv_lhs => rw [show v = fun i => ∑ j : Fin r, v i j • (Pi.single j (1 : ℂ) : Fin r → ℂ) from
      funext hcoord]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [MultilinearMap.map_smul_univ]
  rw [hexpand]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun φ _ => ?_
  rw [norm_smul, norm_prod]
  calc (∏ i, ‖v i (φ i)‖) * ‖f fun i => (Pi.single (φ i) (1 : ℂ) : Fin r → ℂ)‖
      ≤ (∏ i, ‖v i‖) * ‖f fun i => (Pi.single (φ i) (1 : ℂ) : Fin r → ℂ)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
          fun i _ => norm_le_pi_norm (v i) (φ i)
    _ = ‖f fun i => (Pi.single (φ i) (1 : ℂ) : Fin r → ℂ)‖ * ∏ i, ‖v i‖ := mul_comm _ _

/-- **An alternating map on a finite coordinate space is a continuous alternating map.** -/
noncomputable def alternatingMapToContinuous (f : (Fin r → ℂ) [⋀^ι]→ₗ[ℂ] F) :
    (Fin r → ℂ) [⋀^ι]→L[ℂ] F :=
  f.mkContinuous (∑ φ : ι → Fin r, ‖f fun i => (Pi.single (φ i) (1 : ℂ) : Fin r → ℂ)‖)
    (multilinearMap_bound f.toMultilinearMap)

@[simp]
theorem alternatingMapToContinuous_apply (f : (Fin r → ℂ) [⋀^ι]→ₗ[ℂ] F) (v : ι → (Fin r → ℂ)) :
    alternatingMapToContinuous f v = f v := rfl

end Bound

end GaloisForLFunctions.HTGeometry
