import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Rescaling a family by nonzero base coefficients

A derivation-closed intermediate field contains every jet of each of its elements.  Consequently
multiplying every member of a family by a nonzero element of the coefficient field leaves the
generated differential field unchanged: the coefficient and its inverse are already in the base.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A derivation-closed intermediate field contains every jet of each of its elements. -/
private theorem differentialJet_mem_of_derivationClosed {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Differential K] {L : IntermediateField F K} (hL : DerivationClosed L) {x : K} (hx : x ∈ L)
    (n : ℕ) : differentialJet n x ∈ L := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      rw [differentialJet_succ]
      exact hL ih

/-- **Rescaling by nonzero base coefficients does not change the generated differential field.** -/
theorem differentialAdjoin_mul_base {F K ι : Type*} [Field F] [Field K] [Differential F]
    [Differential K] [Algebra F K] [DifferentialAlgebra F K] (x : ι → K) (b : ι → F)
    (hb : ∀ i, b i ≠ 0) :
    differentialAdjoin F (Set.range fun i => algebraMap F K (b i) * x i)
      = differentialAdjoin F (Set.range x) := by
  have hDCx := derivationClosed_differentialAdjoin F (Set.range x)
  have hDCy :=
    derivationClosed_differentialAdjoin F (Set.range fun i => algebraMap F K (b i) * x i)
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨z, ⟨i, rfl⟩, n, rfl⟩
    refine differentialJet_mem_of_derivationClosed hDCx ?_ n
    exact IntermediateField.mul_mem _ (IntermediateField.algebraMap_mem _ _)
      (subset_differentialAdjoin F _ (Set.mem_range_self i))
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨z, ⟨i, rfl⟩, n, rfl⟩
    refine differentialJet_mem_of_derivationClosed hDCy ?_ n
    have hmem : algebraMap F K (b i) * x i ∈
        differentialAdjoin F (Set.range fun j => algebraMap F K (b j) * x j) :=
      subset_differentialAdjoin F _ (Set.mem_range_self i)
    have hinv : algebraMap F K (b i)⁻¹ ∈
        differentialAdjoin F (Set.range fun j => algebraMap F K (b j) * x j) :=
      IntermediateField.algebraMap_mem _ _
    have hprod := IntermediateField.mul_mem _ hinv hmem
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hb i), map_one, one_mul] at hprod

end

end GaloisForLFunctions.HTGeometry
