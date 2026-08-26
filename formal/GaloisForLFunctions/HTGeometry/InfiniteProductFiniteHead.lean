import Mathlib.Probability.ProductMeasure

/-!
# Finite heads of countable product laws

The first `M` coordinates of a countable product probability law have exactly the corresponding
finite product law.  The statement is type-generic and keeps the canonical `Fin M` indexing needed
by finite-dimensional observation maps.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private def finRangeEquiv (M : ℕ) : Fin M ≃ ↥(Finset.range M) where
  toFun i := ⟨i, Finset.mem_range.mpr i.isLt⟩
  invFun i := ⟨i, Finset.mem_range.mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical first-`M` coordinate projection. -/
def countableProductHead {α : Type*} (M : ℕ) (x : ℕ → α) : Fin M → α :=
  fun i => x i

/-- The first `M` coordinates of a countable product probability law have the finite product law. -/
theorem map_countableProductHead_infinitePi
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (M : ℕ) :
    Measure.map (countableProductHead M) (Measure.infinitePi (fun _ : ℕ => μ)) =
      Measure.pi (fun _ : Fin M => μ) := by
  let I : Finset ℕ := Finset.range M
  let e : Fin M ≃ ↥I := finRangeEquiv M
  let reindex : (↥I → α) → (Fin M → α) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin M => α) e.symm
  have hfun : countableProductHead M = reindex ∘ I.restrict := by
    funext x i
    rfl
  have hrestrict :
      Measure.map I.restrict (Measure.infinitePi (fun _ : ℕ => μ)) =
        Measure.pi (fun _ : ↥I => μ) := by
    simpa using
      (Measure.infinitePi_map_restrict (fun _ : ℕ => μ) (I := I))
  have hreindex : Measurable reindex :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin M => α) e.symm).measurable
  rw [hfun, ← Measure.map_map hreindex (Finset.measurable_restrict I), hrestrict]
  exact Measure.pi_map_piCongrLeft e.symm (fun _ : Fin M => μ)

end

end GaloisForLFunctions.HTGeometry
