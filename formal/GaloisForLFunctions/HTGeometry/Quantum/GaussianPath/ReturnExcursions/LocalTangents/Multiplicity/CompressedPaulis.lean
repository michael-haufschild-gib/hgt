import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Sparse Pauli realizations of a Hermitian compression -/

open Matrix Module Set Submodule
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
noncomputable section
private abbrev Mat (I : Type*) := Matrix I I ℂ
private abbrev Bits (N : ℕ) := Fin N → Bool

/-- Every Hermitian response measured on an r-dimensional space has a
Pauli expansion with at most r² words, even when the original generator
on the full register has no sparse expansion. -/
theorem sparse_pauli_response {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (L : selfAdjoint (Mat (Bits N)) →ₗ[ℝ] selfAdjoint (Mat I)) (B : selfAdjoint (Mat (Bits N))) :
    ∃ d ≤ Fintype.card I ^ 2, ∃ (w : Fin d → Fin N → Option (Fin 3)) (c : Fin d → ℝ),
      L (∑ i, c i • finitePauliSelfAdjoint (w i))=L B := by
  classical
  letI : FiniteDimensional ℝ (selfAdjoint (Mat I)) :=
    FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (Mat I)).subtype
      (Submodule.injective_subtype _)
  let b := finitePauliSelfAdjointBasis (Fin N)
  let F (w : Fin N → Option (Fin 3)) := L (b w)
  let S := span ℝ (range F)
  let d := finrank ℝ S
  have hdim : d≤Fintype.card I^2 := by
    exact S.finrank_le.trans_eq ((finrank_selfAdjoint_complexMatrix I).trans (sq _).symm)
  obtain ⟨f,hf,hspan,_⟩ := exists_fun_fin_finrank_span_eq ℝ (range F)
  choose w hw using hf
  have hmem : L B∈S := by
    apply (mem_span_range_iff_exists_fun ℝ).mpr
    refine ⟨b.repr B,?_⟩
    simpa only [F,map_sum,map_smul] using congrArg L (b.sum_repr B)
  have hfmem : L B∈span ℝ (range f) := by
    rw [hspan]
    exact hmem
  obtain ⟨c,hc⟩ := (mem_span_range_iff_exists_fun ℝ).mp hfmem
  refine ⟨d,hdim,w,c,?_⟩
  rw [map_sum]
  simpa only [map_smul,←hw,F,b,finitePauliSelfAdjointBasis_apply] using hc

#print axioms sparse_pauli_response
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
