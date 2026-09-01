import GaloisForLFunctions.HTGeometry.StokesResistance.BinaryOctahedralApplication

/-!
# Projective-octahedral application of Stokes symmetry counting

The strict `48`-element binary-octahedral Clifford lift does not act faithfully on physical
directions: its two-element scalar center acts trivially by conjugation. This module descends the
conjugation representation to the actual `24`-element projective octahedral group and applies the
finite-group machinery extracted from Moreau, *The Stokes resistance of an arbitrary particle: a
classification of hydrodynamic symmetries*, arXiv:2608.23907v1.

The four-dimensional matrix carrier splits into its scalar and traceless Pauli sectors. Its exact
fixed subspace is the one-dimensional scalar line. Thus the Reynolds projector retains one
isotropic response and removes all three vector directions; equivalently, the character average is
one and the stacked symmetry-defect kernel is exactly the scalar line.
-/

open scoped BigOperators Kronecker Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry.StokesResistance

open MonoidAlgebra Representation
open QuantumAlg QuantumAlg.QubitTwoDesign

/-- Actual projective octahedral group obtained from the strict Clifford lift. -/
abbrev ProjectiveOctahedral :=
  BinaryOctahedral ⧸ Subgroup.center BinaryOctahedral

/-- The projective octahedral group has order `24`. -/
theorem projectiveOctahedral_card : Fintype.card ProjectiveOctahedral = 24 :=
  projectiveQubitClifford_card

/-- Conjugation by a strict Clifford matrix, as a complex-linear endomorphism. -/
def cliffordConjugationLinear (g : BinaryOctahedral) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := qubitClifford g * X * (qubitClifford g)ᴴ
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp

/-- Binary-octahedral conjugation representation on the four-dimensional matrix carrier. -/
def binaryOctahedralConjugationRepresentation :
    Representation ℂ BinaryOctahedral (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun := cliffordConjugationLinear
  map_one' := by
    apply LinearMap.ext
    intro X
    simp [cliffordConjugationLinear, qubitClifford_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro X
    change qubitClifford (a * b) * X * (qubitClifford (a * b))ᴴ =
      qubitClifford a * (qubitClifford b * X * (qubitClifford b)ᴴ) *
        (qubitClifford a)ᴴ
    rw [qubitClifford_mul, Matrix.conjTranspose_mul]
    noncomm_ring

/-- Unitarity in the orientation used by conjugation of the identity matrix. -/
theorem qubitClifford_mul_conjTranspose (g : BinaryOctahedral) :
    qubitClifford g * (qubitClifford g)ᴴ = 1 := by
  have hmem : qubitClifford g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact qubitClifford_unitary g
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp hmem)

/-- The two-element scalar center acts trivially by conjugation. -/
theorem binaryOctahedral_center_le_conjugation_kernel :
    Subgroup.center BinaryOctahedral ≤
      binaryOctahedralConjugationRepresentation.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  rcases (binaryOctahedral_mem_center_iff z).mp hz with rfl | rfl
  · exact binaryOctahedralConjugationRepresentation.map_one
  · ext X
    simp [binaryOctahedralConjugationRepresentation, cliffordConjugationLinear,
      qubitClifford_negOne]

/-- Conjugation representation descended to the actual `24`-element octahedral group. -/
def projectiveOctahedralConjugationRepresentation :
    Representation ℂ ProjectiveOctahedral (Matrix (Fin 2) (Fin 2) ℂ) :=
  QuotientGroup.lift (Subgroup.center BinaryOctahedral)
    binaryOctahedralConjugationRepresentation
    binaryOctahedral_center_le_conjugation_kernel

/-- The descended action agrees with strict Clifford conjugation on representatives. -/
@[simp] theorem projectiveOctahedralConjugationRepresentation_mk
    (g : BinaryOctahedral) :
    projectiveOctahedralConjugationRepresentation (QuotientGroup.mk g) =
      cliffordConjugationLinear g := by
  rw [projectiveOctahedralConjugationRepresentation, QuotientGroup.lift_mk]
  rfl

/-- A projective-octahedral fixed matrix is fixed by the strict Clifford twirl. -/
theorem repTwirl_qubitClifford_eq_self_of_projective_invariant
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ projectiveOctahedralConjugationRepresentation.invariants) :
    QuantumAlg.repTwirl qubitClifford X = X := by
  have hterm : ∀ g : BinaryOctahedral,
      qubitClifford g * X * (qubitClifford g)ᴴ = X := by
    intro g
    have h := hX (QuotientGroup.mk g)
    simpa [projectiveOctahedralConjugationRepresentation_mk,
      cliffordConjugationLinear] using h
  unfold QuantumAlg.repTwirl
  simp_rw [hterm]
  have hcard : (Fintype.card BinaryOctahedral : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- Only scalar matrices survive exact projective-octahedral averaging. -/
theorem projectiveOctahedralConjugation_invariants_eq_scalar :
    projectiveOctahedralConjugationRepresentation.invariants =
      ℂ ∙ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  apply le_antisymm
  · intro X hX
    rw [Submodule.mem_span_singleton]
    refine ⟨X.trace / 2, ?_⟩
    calc
      (X.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
          QuantumAlg.repTwirl qubitClifford X :=
        (QuantumAlg.QubitTwoDesign.qubitClifford_repTwirl_eq_scalar X).symm
      _ = X := repTwirl_qubitClifford_eq_self_of_projective_invariant hX
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    change cliffordConjugationLinear _ 1 = 1
    simp [cliffordConjugationLinear, qubitClifford_mul_conjTranspose]

/-- Exact dimension of the projective-octahedral invariant response sector. -/
theorem projectiveOctahedralConjugation_invariants_finrank :
    Module.finrank ℂ projectiveOctahedralConjugationRepresentation.invariants = 1 := by
  rw [projectiveOctahedralConjugation_invariants_eq_scalar,
    finrank_span_singleton]
  exact one_ne_zero

/-- Moreau's character average equals the single surviving scalar response. -/
theorem projectiveOctahedralConjugation_character_average_eq_one :
    (Fintype.card ProjectiveOctahedral : ℂ)⁻¹ *
        ∑ g : ProjectiveOctahedral,
          LinearMap.trace ℂ (Matrix (Fin 2) (Fin 2) ℂ)
            (projectiveOctahedralConjugationRepresentation g) = 1 := by
  rw [← finrank_invariants_eq_character_average,
    projectiveOctahedralConjugation_invariants_finrank]
  norm_num

/-- Stacked octahedral symmetry equations vanish exactly on scalar matrices. -/
theorem projectiveOctahedralConjugation_defect_kernel_eq_scalar :
    LinearMap.ker
        (invarianceDefect projectiveOctahedralConjugationRepresentation) =
      ℂ ∙ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [ker_invarianceDefect,
    projectiveOctahedralConjugation_invariants_eq_scalar]

end GaloisForLFunctions.HTGeometry.StokesResistance
