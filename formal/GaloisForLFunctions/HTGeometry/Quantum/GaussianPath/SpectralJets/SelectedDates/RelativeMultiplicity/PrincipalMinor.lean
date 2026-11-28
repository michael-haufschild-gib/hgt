import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Independent diagonal phases force matrix rank -/

open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.RelativeMultiplicity
noncomputable section
variable {F L I : Type*} [Field F] [Field L] [Algebra F L] [Fintype I] [DecidableEq I]

/-- Subtracting a fixed matrix from a diagonal matrix with algebraically
independent entries leaves a nonsingular matrix. Specializing all diagonal
variables to the same indeterminate gives the monic characteristic polynomial. -/
theorem independent_diagonal_det (p : I → L) (hp : AlgebraicIndependent F p)
    (W : Matrix I I F) : (diagonal p - (algebraMap F L).mapMatrix W).det ≠ 0 := by
  classical
  let M : Matrix I I (MvPolynomial I F) := diagonal MvPolynomial.X -
    (MvPolynomial.C : F →+* MvPolynomial I F).mapMatrix W
  have hmap {A : Type*} [CommRing A] [Algebra F A] (q : I → A) :
      (MvPolynomial.aeval q).toRingHom.mapMatrix M =
        diagonal q - (algebraMap F A).mapMatrix W := by
    ext i j
    by_cases h : i=j
    · subst j
      simp [M,RingHom.mapMatrix_apply]
    · simp [M,RingHom.mapMatrix_apply,diagonal_apply_ne _ h,h]
  have hM : M.det≠0 := by
    intro hz
    let f := MvPolynomial.aeval (fun _ : I => (Polynomial.X : Polynomial F))
    have hchar : f.toRingHom.mapMatrix M=W.charmatrix := hmap _
    have hh := f.toRingHom.map_det M
    rw [hz,map_zero,hchar] at hh
    exact W.charpoly_monic.ne_zero hh.symm
  have hh := (MvPolynomial.aeval p).toRingHom.map_det M
  rw [hmap p] at hh
  rw [←hh]
  simpa only [map_zero] using (algebraicIndependent_iff_injective_aeval.mp hp).ne hM

/-- Every independent subset of the diagonal readings gives a lower bound
for the rank, even if all readings outside that subset are dependent. -/
theorem independent_diagonal_rank {J : Type*} [Fintype J] [DecidableEq J]
    (j : J ↪ I) (p : I → L) (hp : AlgebraicIndependent F (p ∘ j))
    (W : Matrix I I F) :
    Fintype.card J ≤ (diagonal p - (algebraMap F L).mapMatrix W).rank := by
  let M := diagonal p - (algebraMap F L).mapMatrix W
  have heq : M.submatrix j j=diagonal (p ∘ j) - (algebraMap F L).mapMatrix (W.submatrix j j) := by
    ext u v
    by_cases h : u=v
    · subst v
      simp [M]
    · simp [M,diagonal_apply_ne _ h,diagonal_apply_ne _ (j.injective.ne h),h,j.injective.ne h]
  have hu : IsUnit (M.submatrix j j).det := by
    rw [heq,isUnit_iff_ne_zero]
    exact independent_diagonal_det _ hp _
  exact ((M.submatrix j j).rank_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hu)).symm.le.trans
    (M.rank_submatrix_le j j)

#print axioms independent_diagonal_rank
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.RelativeMultiplicity
