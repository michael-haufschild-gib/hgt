import GaloisForLFunctions.RepresentationLifting.QuadraticCohomology
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Vanishing of quadratic classes for monomial and permutation actions

When distinct entries in each action-matrix row have zero product, reading the
diagonal coefficients is equivariant. It retracts the pure-square inclusion,
so the quadratic Yoneda class and all double connecting maps vanish. In
particular this applies to every finite permutation representation, over every
commutative coefficient ring of characteristic two.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry
universe u
variable {k G ι : Type u} [CommRing k] [CharP k 2] [Group G] [Fintype ι] [LinearOrder ι]

omit [CharP k 2] in
/-- Disjoint row entries prevent mixed quadratic coefficients from entering the diagonal. -/
theorem quadraticDiagonalRead_intertwines_of_disjoint_rows (A : Matrix ι ι k)
    (hA : ∀ r i j, i ≠ j → A r i * A r j = 0) (q : Sym2 ι → k) :
    quadraticDiagonalRead ((symmetricSquareMatrixGeneral A).mulVec q) =
      (A.map (fun a => a ^ 2)).mulVec (quadraticDiagonalRead q) := by
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [← tensorProjection_intertwines]
  funext r
  change tensorProjection (tensorSquareAction A T) s(r, r) =
    ∑ i, A r i ^ 2 * tensorProjection T s(i, i)
  simp only [tensorProjection_mk, ↓reduceIte]
  change (A * T * A.transpose) r r = ∑ i, A r i ^ 2 * T i i
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    calc
      A r j * T j i * A r i = (A r j * A r i) * T j i := by ring
      _ = 0 := by rw [hA r j i hji, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- Diagonal extraction is equivariant for monomial actions. -/
def monomialQuadraticRetraction (ρ : G →* Matrix ι ι k)
    (hρ : ∀ g r i j, i ≠ j → ρ g r i * ρ g r j = 0) :
    Rep.of (quadraticSymmetricRepresentation ρ) ⟶ Rep.of (quadraticFrobeniusRepresentation ρ) :=
  Rep.ofHom ⟨quadraticDiagonalRead, fun g => by
    apply LinearMap.ext
    intro q
    exact quadraticDiagonalRead_intertwines_of_disjoint_rows (ρ g) (hρ g) q⟩

theorem monomialQuadraticRetraction_inclusion (ρ : G →* Matrix ι ι k)
    (hρ : ∀ g r i j, i ≠ j → ρ g r i * ρ g r j = 0) :
    quadraticSquareInclusion ρ ≫ monomialQuadraticRetraction ρ hρ = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact quadraticDiagonalRead_square

/-- The pure-square retraction annihilates the quadratic Yoneda two-extension. -/
theorem monomial_quadraticSequenceClass_zero (ρ : G →* Matrix ι ι k)
    (hρ : ∀ g r i j, i ≠ j → ρ g r i * ρ g r j = 0) :
    quadraticSequenceClass ρ = 0 := by
  have hz : (quadraticFirstSequence_shortExact ρ).extClass = 0 :=
    (extClass_zero_iff_retraction _ _).mpr
      ⟨monomialQuadraticRetraction ρ hρ, monomialQuadraticRetraction_inclusion ρ hρ⟩
  unfold quadraticSequenceClass
  rw [hz]
  exact Ext.comp_zero _ _ 1 2 rfl

/-- Every quadratic double connecting map vanishes for a monomial action. -/
theorem monomial_quadraticConnecting_zero (ρ : G →* Matrix ι ι k)
    (hρ : ∀ g r i j, i ≠ j → ρ g r i * ρ g r j = 0) (n : ℕ) :
    quadraticConnecting ρ n = 0 := by
  have hz := cohomologyConnecting_eq_zero_of_retraction (quadraticFirstSequence ρ)
    (quadraticFirstSequence_shortExact ρ) (monomialQuadraticRetraction ρ hρ)
    (monomialQuadraticRetraction_inclusion ρ hρ) (n + 1)
  exact (congrArg (fun f => groupCohomology.δ (quadraticSecondSequence_shortExact ρ)
    n (n + 1) rfl ≫ f) hz).trans comp_zero

/-- All invariant quadratic tensors of a monomial representation have zero obstruction. -/
theorem monomial_quadraticCohomologyClass_zero (ρ : G →* Matrix ι ι k)
    (hρ : ∀ g r i j, i ≠ j → ρ g r i * ρ g r j = 0) :
    quadraticCohomologyClass ρ = 0 := by
  unfold quadraticCohomologyClass
  rw [monomial_quadraticConnecting_zero ρ hρ]
  rfl

/-- The matrix representation induced by a finite permutation action. -/
def permutationMatrixRepresentation (σ : G →* Equiv.Perm ι) : G →* Matrix ι ι k :=
  (Matrix.permMatrixHom (R := k)).comp σ

omit [CharP k 2] in
theorem permutationMatrixRepresentation_disjoint_rows (σ : G →* Equiv.Perm ι)
    (g : G) (r i j : ι) (hij : i ≠ j) :
    permutationMatrixRepresentation (k := k) σ g r i *
      permutationMatrixRepresentation (k := k) σ g r j = 0 := by
  by_cases hi : (σ g).symm r = i
  · simp [permutationMatrixRepresentation, Matrix.permMatrixHom, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, hi, hij]
  · simp [permutationMatrixRepresentation, Matrix.permMatrixHom, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, hi]

/-- Every finite permutation action has trivial quadratic Yoneda class. -/
theorem permutation_quadraticSequenceClass_zero (σ : G →* Equiv.Perm ι) :
    quadraticSequenceClass (permutationMatrixRepresentation (k := k) σ) = 0 :=
  monomial_quadraticSequenceClass_zero _ (permutationMatrixRepresentation_disjoint_rows σ)

/-- Every quadratic connecting map of a finite permutation action is zero. -/
theorem permutation_quadraticConnecting_zero (σ : G →* Equiv.Perm ι) (n : ℕ) :
    quadraticConnecting (permutationMatrixRepresentation (k := k) σ) n = 0 :=
  monomial_quadraticConnecting_zero _ (permutationMatrixRepresentation_disjoint_rows σ) n

/-- All invariant quadratic tensors in finite permutation modules have zero obstruction. -/
theorem permutation_quadraticCohomologyClass_zero (σ : G →* Equiv.Perm ι) :
    quadraticCohomologyClass (permutationMatrixRepresentation (k := k) σ) = 0 :=
  monomial_quadraticCohomologyClass_zero _ (permutationMatrixRepresentation_disjoint_rows σ)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.monomial_quadraticSequenceClass_zero
#print axioms GaloisForLFunctions.RepresentationLifting.monomial_quadraticCohomologyClass_zero
#print axioms GaloisForLFunctions.RepresentationLifting.permutation_quadraticSequenceClass_zero
#print axioms GaloisForLFunctions.RepresentationLifting.permutation_quadraticCohomologyClass_zero
