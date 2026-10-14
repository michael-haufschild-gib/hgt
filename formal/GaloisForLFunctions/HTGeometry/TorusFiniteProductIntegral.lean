import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Finite-coordinate integration under full torus Haar measure -/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Countable ι]

theorem measurePreserving_torus_restrict (S : Finset ι) :
    MeasurePreserving (S.restrict : UnitAddTorus ι → (↥S → UnitAddCircle))
      (torusHaar ι) (Measure.pi fun _ : ↥S => AddCircle.haarAddCircle) := by
  classical
  let φ : UnitAddTorus ι →+ (↥S → UnitAddCircle) :=
    { toFun := S.restrict
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc : Continuous φ := continuous_pi fun i => continuous_apply (i : ι)
  have hs : Function.Surjective φ := by
    intro y
    refine ⟨fun i => if hi : i ∈ S then y ⟨i, hi⟩ else 0, ?_⟩
    ext i
    simp [φ, Finset.restrict, i.property]
  exact φ.measurePreserving hc hs (by simp)

theorem integral_torus_finite_product {𝕜 : Type*} [RCLike 𝕜]
    (S : Finset ι) (f : ι → UnitAddCircle → 𝕜) (hf : ∀ i, Continuous (f i)) :
    ∫ x, ∏ i ∈ S, f i (x i) ∂torusHaar ι =
      ∏ i ∈ S, ∫ θ, f i θ ∂AddCircle.haarAddCircle := by
  classical
  have hmap := (measurePreserving_torus_restrict S).map_eq
  have hc : Continuous (fun y : ↥S → UnitAddCircle => ∏ i : ↥S, f i (y i)) :=
    continuous_finsetProd Finset.univ fun i _ => (hf i).comp (continuous_apply i)
  calc
    _ = ∫ x, ∏ i : ↥S, f i (x i) ∂torusHaar ι := by
      congr 1
      funext x
      exact (Finset.prod_attach S (fun i => f i (x i))).symm
    _ = ∫ y : ↥S → UnitAddCircle, ∏ i : ↥S, f i (y i)
        ∂Measure.pi (fun _ : ↥S => AddCircle.haarAddCircle) := by
      rw [← hmap, integral_map (measurePreserving_torus_restrict S).measurable.aemeasurable
        hc.aestronglyMeasurable]
      rfl
    _ = ∏ i : ↥S, ∫ θ, f i θ ∂AddCircle.haarAddCircle :=
      integral_fintype_prod_eq_prod (fun i : ↥S => f i)
    _ = _ := Finset.prod_attach S (fun i => ∫ θ, f i θ ∂AddCircle.haarAddCircle)

end GaloisForLFunctions.HTGeometry
