import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Equivariant maps detected by generator annihilators

Evaluation embeds maps out of a generated module into the product of the
annihilator spaces of its generators. This is equation (13) and the dimension
mechanism of Proposition 2.20 in Zehavi, arXiv:2611.18218. Using the actual
generated submodule removes any separate generation or torsion premise.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {K R X W ι : Type*} [Field K] [Ring R] [Algebra K R]
  [AddCommGroup X] [Module R X]
  [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower K R W]

/-- Possible images of a vector respect every one of its actual annihilators. -/
def annihilatorImage (x : X) : Submodule K W where
  carrier := {w | ∀ r : R, r • x = 0 → r • w = 0}
  zero_mem' := by intro r _; exact smul_zero r
  add_mem' := by
    intro u v hu hv r hr
    rw [smul_add, hu r hr, hv r hr, add_zero]
  smul_mem' := by
    intro c w hw r hr
    rw [smul_comm r c w, hw r hr, smul_zero]

/-- Evaluation on generators, retaining all annihilator constraints. -/
def generatorEvaluation (v : ι → X) :
    (Submodule.span R (Set.range v) →ₗ[R] W) →ₗ[K] (∀ i, annihilatorImage (K := K) (R := R) (W := W) (v i)) where
  toFun f i := ⟨f ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩, by
    intro r hr
    rw [← map_smul]
    have hz : r • (⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ :
        Submodule.span R (Set.range v)) = 0 := Subtype.ext hr
    rw [hz, map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A map on a generated module is determined by its generator values. -/
theorem generatorEvaluation_injective (v : ι → X) :
    Function.Injective (generatorEvaluation (K := K) (R := R) (W := W) v) := by
  intro f g h
  apply LinearMap.ext
  intro z
  have hv (i : ι) :
      f ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ =
        g ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ :=
    congrArg Subtype.val (congrFun h i)
  have heq (x : X) (hx : x ∈ Submodule.span R (Set.range v)) :
      f ⟨x, hx⟩ = g ⟨x, hx⟩ := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hv i
    | zero => exact (map_zero f).trans (map_zero g).symm
    | add x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
    | smul r x hx ih =>
      change f (r • ⟨x, hx⟩) = g (r • ⟨x, hx⟩)
      rw [map_smul, map_smul, ih]
  exact heq z.val z.property

/-- The exact generator annihilators give a sharper bound than generator count alone. -/
theorem finrank_hom_le_sum_annihilatorImage [Fintype ι] [FiniteDimensional K W]
    (v : ι → X) :
    Module.finrank K (Submodule.span R (Set.range v) →ₗ[R] W) ≤
      ∑ i, Module.finrank K (annihilatorImage (K := K) (R := R) (W := W) (v i)) := by
  simpa only [Module.finrank_pi_fintype] using
    (LinearMap.finrank_le_finrank_of_injective
      (generatorEvaluation_injective (K := K) (R := R) (W := W) v))

/-- Uniform linear growth in the target dimension, with explicit generator constant. -/
theorem finrank_hom_le_generators_mul [Fintype ι] [FiniteDimensional K W]
    (v : ι → X) :
    Module.finrank K (Submodule.span R (Set.range v) →ₗ[R] W) ≤
      Fintype.card ι * Module.finrank K W := by
  calc
    _ ≤ ∑ i, Module.finrank K (annihilatorImage (K := K) (R := R) (W := W) (v i)) :=
      finrank_hom_le_sum_annihilatorImage (K := K) v
    _ ≤ ∑ _ : ι, Module.finrank K W :=
      Finset.sum_le_sum fun _ _ => Submodule.finrank_le _
    _ = _ := by simp

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.generatorEvaluation_injective
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.finrank_hom_le_sum_annihilatorImage
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.finrank_hom_le_generators_mul
