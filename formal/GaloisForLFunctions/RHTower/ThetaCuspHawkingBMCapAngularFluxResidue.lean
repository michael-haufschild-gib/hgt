import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCapAngularFluxCusp

/-!
The complete literal scalar flux and the original first Stokes current have
exactly proportional constant residues after spectral specialization, including
at exponent collisions. The difference carries the height exponent as a factor.
This algebraic source identity supplies no complete physical action admission
or independent-reader vanishing premise.
-/

set_option autoImplicit false
open scoped BigOperators
namespace RHTower.D4BMCapAngularFluxResidue
open D4BMCapAngularFluxCusp
noncomputable section

/-- The exact discrepancy from the first Stokes coefficient is divisible by its
original specialized height exponent; no spectral nonresonance is assumed. -/
theorem coefficient_stokes_decomposition (u v : ℂ) (e1 e2 e3 : Bool) :
    constantCoefficient u v e1 e2 e3=
      (v^(2 : ℕ)-1/4)/2*d4BMCanonicalFirstStokesConstantBoundaryCoefficient u v e1 e2 e3-
      (d4BMCompletedEisensteinCuspConstantCoefficient u e1*
        d4BMCompletedEisensteinCuspConstantCoefficient u e2*
        d4BMCompletedEisensteinCuspConstantCoefficient v e3*
        d4BMCompletedEisensteinCuspWeylExponent v e3/2)*
      (d4BMCompletedEisensteinCuspWeylExponent u e1+
        d4BMCompletedEisensteinCuspWeylExponent u e2-
        d4BMCompletedEisensteinCuspWeylExponent v e3)*
      d4BMSpecializeDiagonalCuspAffineExponent u v
        (d4BMDiagonalEisensteinCuspBoundaryExponent e1 e2 e3) := by
  rw [d4BM_diagonalCuspBoundaryExponent_specialization]
  unfold constantCoefficient d4BMCanonicalFirstStokesConstantBoundaryCoefficient
  cases e1 <;> cases e2 <;> cases e3 <;>
    simp only [d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign,
      Bool.false_eq_true,↓reduceIte,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul] <;> ring

/-- The constant residue of the complete literal flux is exactly half the reader
eigenvalue times the already original first Stokes residue, at arbitrary parameters.
This is specialization first and remains valid at every exponent collision. -/
theorem specialized_constant_eq_first_stokes (u v : ℂ) :
    (Finsupp.mapDomain (d4BMSpecializeDiagonalCuspAffineExponent u v)
      (constantFamily u v)) 0=
      (v^(2 : ℕ)-1/4)/2*(Finsupp.mapDomain (d4BMSpecializeDiagonalCuspAffineExponent u v)
        (d4BMCanonicalFirstStokesConstantBoundaryFamily u v)) 0 := by
  classical
  have ht (e1 e2 e3 : Bool) :
      (Finsupp.single (d4BMSpecializeDiagonalCuspAffineExponent u v
        (d4BMDiagonalEisensteinCuspBoundaryExponent e1 e2 e3))
        (constantCoefficient u v e1 e2 e3)) (0:ℂ)=
      (v^(2 : ℕ)-1/4)/2*(Finsupp.single (d4BMSpecializeDiagonalCuspAffineExponent u v
        (d4BMDiagonalEisensteinCuspBoundaryExponent e1 e2 e3))
        (d4BMCanonicalFirstStokesConstantBoundaryCoefficient u v e1 e2 e3)) (0:ℂ) := by
    by_cases he : d4BMSpecializeDiagonalCuspAffineExponent u v
        (d4BMDiagonalEisensteinCuspBoundaryExponent e1 e2 e3)=0
    · simp only [Finsupp.single_apply,he,↓reduceIte]
      rw [coefficient_stokes_decomposition,he,mul_zero,sub_zero]
    · simp only [Finsupp.single_apply,he,↓reduceIte,mul_zero]
  simp only [constantFamily,d4BMCanonicalFirstStokesConstantBoundaryFamily,
    d4BMDiagonalEisensteinCuspBoundaryFamily,Fintype.sum_bool,Finsupp.mapDomain_add,
    Finsupp.mapDomain_single,Finsupp.add_apply]
  simp_rw [ht]
  ring

end
end RHTower.D4BMCapAngularFluxResidue
