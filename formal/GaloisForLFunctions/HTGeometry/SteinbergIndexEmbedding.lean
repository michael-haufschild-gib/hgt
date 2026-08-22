import GaloisForLFunctions.HTGeometry.SteinbergGroupPresentation

/-!
# Functoriality of Steinberg presentations under index embeddings

The stable Steinberg group is formed by allowing arbitrarily many indices.  Its finite-rank
presentations must therefore embed compatibly: an injective relabelling of indices sends every
elementary generator to the generator with relabelled endpoints and preserves all three defining
Steinberg relations.  This module supplies that canonical homomorphism.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n m : Type*}

/-- Relabel the indices of a Steinberg presentation along an injective map. -/
noncomputable def steinbergIndexMap (f : n → m) (hf : Function.Injective f) :
    SteinbergGroup R n →* SteinbergGroup R m :=
  PresentedGroup.toGroup (f := fun g : SteinbergGen R n =>
    steinbergX (fun h => g.hij (hf h)) g.a) (by
    rintro r ((hr | hr) | hr)
    · obtain ⟨i, j, hij, a, b, rfl⟩ := hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [steinbergX_mul, mul_inv_cancel]
    · obtain ⟨i, j, k, l, hij, hkl, a, b, hjk, hil, rfl⟩ := hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [steinbergX_commute (fun h => hij (hf h)) (fun h => hkl (hf h))
        (fun h => hjk (hf h)) (fun h => hil (hf h))]
      group
    · obtain ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩ := hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [steinbergX_chain (fun h => hij (hf h)) (fun h => hjk (hf h))
        (fun h => hik (hf h)), mul_inv_cancel])

@[simp]
theorem steinbergIndexMap_x (f : n → m) (hf : Function.Injective f)
    {i j : n} (hij : i ≠ j) (a : R) :
    steinbergIndexMap f hf (steinbergX hij a) = steinbergX (fun h => hij (hf h)) a :=
  PresentedGroup.toGroup.of _

end GaloisForLFunctions.HTGeometry
