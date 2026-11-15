import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.BinaryAffineCodes
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Homological.StabGroup
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# CSS stabilizer groups from divisible binary codes

A self-orthogonal binary code of length `N` and dimension `k` gives a
chain complex with the same code as both boundary and coboundary space.
Its first homology has dimension `N - 2k`. The actual Pauli stabilizer
group is constructed through the homological CSS framework.

Applying divisible-code orthogonality to affine binary cubes produces
length `2^(n+3)` stabilizer groups with homology dimension
`2^(n+3) - 2(n+4)`. No distance or chosen logical-operator basis is
asserted by this construction.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Quantum.Stabilizer.Homological
variable {ι : Type} [Fintype ι]

/-- Basis coefficients mapped to their actual binary check words. -/
def binaryCheckEmbedding (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    (Fin (Module.finrank (ZMod 2) C) → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
  C.subtype.comp (Module.finBasis (ZMod 2) C).equivFun.symm.toLinearMap

/-- The chosen check words are linearly independent. -/
theorem binaryCheckEmbedding_injective (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Function.Injective (binaryCheckEmbedding C) :=
  C.injective_subtype.comp (Module.finBasis (ZMod 2) C).equivFun.symm.injective

/-- Every evaluated check belongs to the original code. -/
theorem binaryCheckEmbedding_mem (C : Submodule (ZMod 2) (ι → ZMod 2))
    (a : Fin (Module.finrank (ZMod 2) C) → ZMod 2) : binaryCheckEmbedding C a ∈ C :=
  ((Module.finBasis (ZMod 2) C).equivFun.symm a).property

/-- The check embedding spans exactly the original code. -/
theorem binaryCheckEmbedding_range (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    LinearMap.range (binaryCheckEmbedding C) = C := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact binaryCheckEmbedding_mem C a
  · intro hc
    refine ⟨(Module.finBasis (ZMod 2) C).equivFun ⟨c, hc⟩, ?_⟩
    change ((Module.finBasis (ZMod 2) C).equivFun.symm
      ((Module.finBasis (ZMod 2) C).equivFun ⟨c, hc⟩) : ι → ZMod 2) = c
    rw [LinearEquiv.symm_apply_apply]

variable [DecidableEq ι]

/-- The transpose of check evaluation, expressed through coordinate duality. -/
def binaryCheckSyndrome (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    (ι → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) C) → ZMod 2) :=
  (dotProductEquiv (ZMod 2) (Fin (Module.finrank (ZMod 2) C))).symm.toLinearMap.comp
    ((binaryCheckEmbedding C).dualMap.comp (dotProductEquiv (ZMod 2) ι).toLinearMap)

/-- Independent checks allow every syndrome. -/
theorem binaryCheckSyndrome_surjective (C : Submodule (ZMod 2) (ι → ZMod 2)) :
    Function.Surjective (binaryCheckSyndrome C) :=
  (dotProductEquiv (ZMod 2) (Fin (Module.finrank (ZMod 2) C))).symm.surjective.comp
    ((LinearMap.dualMap_surjective_of_injective (binaryCheckEmbedding_injective C)).comp
      (dotProductEquiv (ZMod 2) ι).surjective)

/-- Syndrome evaluation is adjoint to check evaluation for the coordinate pairing. -/
theorem binaryCheckSyndrome_pairing (C : Submodule (ZMod 2) (ι → ZMod 2))
    (c : ι → ZMod 2) (a : Fin (Module.finrank (ZMod 2) C) → ZMod 2) :
    (dotProductEquiv (ZMod 2) _ (binaryCheckSyndrome C c)) a =
      twistedPair (RingHom.id _) c (binaryCheckEmbedding C a) := by
  change (dotProductEquiv (ZMod 2) _
    ((dotProductEquiv (ZMod 2) _).symm
      ((binaryCheckEmbedding C).dualMap (dotProductEquiv (ZMod 2) ι c)))) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Classical self-orthogonality is the chain-complex identity. -/
theorem binaryCheckSyndrome_comp_embedding (C : Submodule (ZMod 2) (ι → ZMod 2))
    (hC : SelfOrthogonal (RingHom.id _) C) :
    (binaryCheckSyndrome C).comp (binaryCheckEmbedding C) = 0 := by
  apply LinearMap.ext
  intro a
  change binaryCheckSyndrome C (binaryCheckEmbedding C a) = 0
  apply (dotProductEquiv (ZMod 2) _).injective
  rw [map_zero]
  apply LinearMap.ext
  intro b
  exact (binaryCheckSyndrome_pairing C (binaryCheckEmbedding C a) b).trans
    (hC _ (binaryCheckEmbedding_mem C a) _ (binaryCheckEmbedding_mem C b))

/-- Zero syndromes are precisely words orthogonal to the whole code. -/
theorem binaryCheckSyndrome_eq_zero_iff (C : Submodule (ZMod 2) (ι → ZMod 2))
    (c : ι → ZMod 2) :
    binaryCheckSyndrome C c = 0 ↔ ∀ d ∈ C, twistedPair (RingHom.id _) c d = 0 := by
  constructor
  · intro h d hd
    obtain ⟨a, rfl⟩ := (show d ∈ LinearMap.range (binaryCheckEmbedding C) from
      (binaryCheckEmbedding_range C).symm ▸ hd)
    rw [← binaryCheckSyndrome_pairing, h, map_zero, LinearMap.zero_apply]
  · intro h
    apply (dotProductEquiv (ZMod 2) _).injective
    rw [map_zero]
    apply LinearMap.ext
    intro a
    exact (binaryCheckSyndrome_pairing C c a).trans (h _ (binaryCheckEmbedding_mem C a))

/-- The symmetric CSS complex associated to a self-orthogonal binary code. -/
def selfOrthogonalHomologicalCode (C : Submodule (ZMod 2) (ι → ZMod 2))
    (hC : SelfOrthogonal (RingHom.id _) C) : HomologicalCode where
  C0 := Fin (Module.finrank (ZMod 2) C)
  C1 := ι
  C2 := Fin (Module.finrank (ZMod 2) C)
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := binaryCheckSyndrome C
  boundary2 := binaryCheckEmbedding C
  boundary_comp := binaryCheckSyndrome_comp_embedding C hC
  numQubits := Fintype.card ι
  numQubits_eq := rfl
  edgeEquiv := Fintype.equivFin ι

/-- The boundary space is the original classical code. -/
theorem selfOrthogonalHomologicalCode_boundaries
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C) :
    (selfOrthogonalHomologicalCode C hC).boundaries = C :=
  binaryCheckEmbedding_range C

/-- The coboundary check map is the same embedding as the boundary map. -/
theorem selfOrthogonalHomologicalCode_cutMap
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C) :
    (selfOrthogonalHomologicalCode C hC).cutMap = binaryCheckEmbedding C := by
  apply LinearMap.ext
  intro a
  apply (dotProductEquiv (ZMod 2) ι).injective
  apply LinearMap.ext
  intro c
  have ht := (selfOrthogonalHomologicalCode C hC).boundary1_cutMap_transpose c a
  have he := binaryCheckSyndrome_pairing C c a
  change (∑ j : Fin (Module.finrank (ZMod 2) C), binaryCheckSyndrome C c j * a j) =
    ∑ i : ι, c i * (selfOrthogonalHomologicalCode C hC).cutMap a i at ht
  change (∑ j : Fin (Module.finrank (ZMod 2) C), binaryCheckSyndrome C c j * a j) =
    ∑ i : ι, c i * binaryCheckEmbedding C a i at he
  change (∑ i : ι, (selfOrthogonalHomologicalCode C hC).cutMap a i * c i) =
    ∑ i : ι, binaryCheckEmbedding C a i * c i
  simpa only [mul_comm] using ht.symm.trans he

/-- Quotienting the dual code by the check code removes twice the check dimension. -/
theorem selfOrthogonalHomologicalCode_finrank_H1
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C) :
    Module.finrank (ZMod 2) (selfOrthogonalHomologicalCode C hC).H1 =
      Fintype.card ι - 2 * Module.finrank (ZMod 2) C := by
  rw [HomologicalCode.finrank_H1_eq_cycles_sub_boundaries,
    selfOrthogonalHomologicalCode_boundaries]
  have hr := LinearMap.finrank_range_add_finrank_ker (binaryCheckSyndrome C)
  rw [LinearMap.range_eq_top.mpr (binaryCheckSyndrome_surjective C),
    finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    Module.finrank_fintype_fun_eq_card] at hr
  change Module.finrank (ZMod 2) (LinearMap.ker (binaryCheckSyndrome C)) -
    Module.finrank (ZMod 2) C = _
  omega

/-- Divisibility supplies the chain law for every affine cube code in the family. -/
def binaryAffineHomologicalCode (n : ℕ) : HomologicalCode :=
  selfOrthogonalHomologicalCode (binaryCubeAffineCode n) (binaryCubeAffineCode_selfOrthogonal n)

/-- Each vertex of the binary cube supplies one physical qubit. -/
theorem binaryAffineHomologicalCode_numQubits (n : ℕ) :
    (binaryAffineHomologicalCode n).numQubits = 2 ^ (n + 3) := by
  change Fintype.card (Fin (n + 3) → ZMod 2) = _
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Exact first-homology dimension of the affine-cube CSS complex. -/
theorem binaryAffineHomologicalCode_finrank_H1 (n : ℕ) :
    Module.finrank (ZMod 2) (binaryAffineHomologicalCode n).H1 =
      2 ^ (n + 3) - 2 * (n + 4) := by
  rw [binaryAffineHomologicalCode, selfOrthogonalHomologicalCode_finrank_H1,
    binaryCubeAffineCode_finrank, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The actual commuting Pauli stabilizer group, with negative identity excluded. -/
def binaryAffineCSSStabilizerGroup (n : ℕ) :
    Quantum.StabilizerGroup (binaryAffineHomologicalCode n).numQubits :=
  (binaryAffineHomologicalCode n).homologicalStabilizerGroup

#print axioms binaryAffineCSSStabilizerGroup
#print axioms binaryAffineHomologicalCode_finrank_H1
#print axioms selfOrthogonalHomologicalCode_cutMap
#print axioms binaryCheckSyndrome_eq_zero_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
