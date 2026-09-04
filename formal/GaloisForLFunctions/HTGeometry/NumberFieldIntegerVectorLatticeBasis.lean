import GaloisForLFunctions.HTGeometry.NumberFieldMixedVectorCoordinates

/-!
# Canonical basis of the number-ring vector lattice

The coordinatewise mixed embeddings of `𝓞 K` are exactly the integer span of the canonical
flattened mixed-vector basis.  This is the conversion needed to turn a real Minkowski lattice point
back into a literal vector over the number ring.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField Module.Free
open scoped Classical NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Integral coordinate vector represented by one canonical mixed-vector basis element. -/
def numberFieldMixedVectorBasisInteger (n : ℕ)
    (r : Fin (n * Module.finrank ℚ K)) : Fin n → 𝓞 K :=
  let p := finProdFinEquiv.symm r
  fun i => if i = p.1 then numberFieldIntegerBasis K p.2 else 0

/-- Every canonical mixed-vector basis element is an embedded integral vector. -/
theorem numberFieldIntegerVectorEmbedding_basisInteger
    (n : ℕ) (r : Fin (n * Module.finrank ℚ K)) :
      numberFieldIntegerVectorEmbedding K
        (numberFieldMixedVectorBasisInteger K n r) =
      numberFieldMixedVectorBasis K n r := by
  obtain ⟨⟨p, q⟩, rfl⟩ := finProdFinEquiv.surjective r
  apply (numberFieldMixedVectorBasis K n).repr.injective
  ext s
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective s
  rw [(numberFieldMixedVectorBasis K n).repr_self]
  rw [numberFieldMixedVectorBasis_repr_integer]
  simp only [numberFieldMixedVectorBasisInteger, Equiv.symm_apply_apply]
  by_cases hi : i = p
  · subst i
    rw [if_pos rfl, (numberFieldIntegerBasis K).repr_self]
    by_cases hj : j = q
    · subst j
      simp
    · simp [hj]
  · rw [if_neg hi]
    simp [hi]

/-- Every embedded number-ring vector belongs to the integer span of the canonical mixed basis. -/
theorem numberFieldIntegerVectorEmbedding_mem_span_mixedVectorBasis
    {n : ℕ} (a : Fin n → 𝓞 K) :
    numberFieldIntegerVectorEmbedding K a ∈
      Submodule.span ℤ (Set.range (numberFieldMixedVectorBasis K n)) := by
  let z : Fin (n * Module.finrank ℚ K) → ℤ := fun r =>
    let p := finProdFinEquiv.symm r
    (numberFieldIntegerBasis K).repr (a p.1) p.2
  have hcoeff (r : Fin (n * Module.finrank ℚ K)) :
      (numberFieldMixedVectorBasis K n).repr
          (numberFieldIntegerVectorEmbedding K a) r = (z r : ℝ) := by
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective r
    rw [numberFieldMixedVectorBasis_repr_integer]
    simp only [z, Equiv.symm_apply_apply]
  have hsum : numberFieldIntegerVectorEmbedding K a =
      ∑ r, (z r : ℝ) • numberFieldMixedVectorBasis K n r := by
    symm
    calc
      ∑ r, (z r : ℝ) • numberFieldMixedVectorBasis K n r =
          ∑ r, ((numberFieldMixedVectorBasis K n).repr
            (numberFieldIntegerVectorEmbedding K a)) r •
              numberFieldMixedVectorBasis K n r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hcoeff]
      _ = numberFieldIntegerVectorEmbedding K a :=
        (numberFieldMixedVectorBasis K n).sum_repr
          (numberFieldIntegerVectorEmbedding K a)
  rw [hsum]
  exact Submodule.sum_mem _ fun r _ => by
    rw [Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self r))

/-- Coordinatewise algebraic integers are exactly the integer span of the canonical mixed basis. -/
theorem numberFieldIntegerVectorLattice_eq_span_mixedVectorBasis (n : ℕ) :
    numberFieldIntegerVectorLattice K n =
      Submodule.span ℤ (Set.range (numberFieldMixedVectorBasis K n)) := by
  apply le_antisymm
  · intro x hx
    choose a ha using fun i => hx i (Set.mem_univ i)
    have hxa : x = numberFieldIntegerVectorEmbedding K a := by
      funext i
      exact (ha i).symm
    rw [hxa]
    exact numberFieldIntegerVectorEmbedding_mem_span_mixedVectorBasis K a
  · apply Submodule.span_le.2
    rintro x ⟨r, rfl⟩
    rw [← numberFieldIntegerVectorEmbedding_basisInteger K n r]
    exact numberFieldIntegerVectorEmbedding_mem_lattice K _

end

end GaloisForLFunctions.HTGeometry
