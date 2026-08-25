import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDeterminantNorm
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDoubleCentralizer

/-!
# Degree-power form of the determinant norm

For a finite central division algebra `A/F`, every maximal commutative subfield has one common
degree `n`, with `n² = [A : F]`.  Restricting left multiplication to a maximal commutative subfield
containing an element shows that its regular determinant is an `n`-th power in `F`.

This supplies the divisibility input needed to bound the relative determinant value group by `n`
over a discretely valued local field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F A : Type u} [Field F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

/-- A finite central division algebra has a degree `n` whose square is its dimension, and every
left-regular determinant is an `n`-th power in the center. -/
theorem exists_divisionAlgebra_degree_and_norm_eq_pow :
    ∃ n : ℕ, 0 < n ∧ n * n = Module.finrank F A ∧
      ∀ x : A, ∃ t : F, Algebra.norm F x = t ^ n := by
  obtain ⟨S, hzeroS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (0 : A)
  let n := Module.finrank F S
  have hnpos : 0 < n := Module.finrank_pos
  have hnsq : n * n = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS
  refine ⟨n, hnpos, hnsq, ?_⟩
  intro x
  obtain ⟨T, hxT, hcommT, hfieldT, hmaxT⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A x
  letI : Field T := hfieldT.toField
  have hTsq : Module.finrank F T * Module.finrank F T = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A T hcommT hfieldT hmaxT
  have hTn : Module.finrank F T = n := by
    exact Nat.mul_self_inj.mp (hTsq.trans hnsq.symm)
  haveI towerFTA : IsScalarTower F T A := by
    constructor
    intro c t a
    simp only [Algebra.smul_def]
    change (((algebraMap F T c : T) : A) * (t : A)) * a =
      algebraMap F A c * ((t : A) * a)
    rw [show ((algebraMap F T c : T) : A) = algebraMap F A c from rfl, mul_assoc]
  haveI finiteTA : Module.Finite T A :=
    @Module.Finite.of_restrictScalars_finite F T A inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance towerFTA inferInstance
  have htower : Module.finrank F T * Module.finrank T A = Module.finrank F A :=
    Module.finrank_mul_finrank F T A
  have hright : Module.finrank T A = n := by
    have hprod : Module.finrank F T * Module.finrank T A =
        Module.finrank F T * Module.finrank F T := htower.trans hTsq.symm
    exact (Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := F) (M := T)) hprod).trans hTn
  let tx : T := ⟨x, hxT (Algebra.self_mem_adjoin_singleton F x)⟩
  refine ⟨Algebra.norm F tx, ?_⟩
  rw [divisionAlgebra_norm_eq_subalgebra_norm_pow T hfieldT tx, hright]

/-- Degree of a finite central division algebra, selected from a maximal commutative subfield. -/
noncomputable def divisionAlgebraDegree : ℕ :=
  exists_divisionAlgebra_degree_and_norm_eq_pow (F := F) (A := A) |>.choose

/-- Division-algebra degree is positive. -/
theorem divisionAlgebraDegree_pos : 0 < divisionAlgebraDegree (F := F) (A := A) :=
  exists_divisionAlgebra_degree_and_norm_eq_pow (F := F) (A := A) |>.choose_spec.1

/-- Square of division-algebra degree is its dimension over the center. -/
theorem divisionAlgebraDegree_mul_self :
    divisionAlgebraDegree (F := F) (A := A) *
        divisionAlgebraDegree (F := F) (A := A) =
      Module.finrank F A :=
  exists_divisionAlgebra_degree_and_norm_eq_pow (F := F) (A := A) |>.choose_spec.2.1

/-- Every left-regular determinant is a power with exponent the division-algebra degree. -/
theorem divisionAlgebra_norm_eq_degree_pow (x : A) :
    ∃ t : F, Algebra.norm F x = t ^ divisionAlgebraDegree (F := F) (A := A) :=
  exists_divisionAlgebra_degree_and_norm_eq_pow (F := F) (A := A) |>.choose_spec.2.2 x

/-- A chosen degree-root in the center of the nonzero regular determinant of a division-algebra
unit. -/
noncomputable def divisionAlgebraDeterminantDegreeRoot (x : Aˣ) : Fˣ :=
  Units.mk0 (divisionAlgebra_norm_eq_degree_pow (F := F) (A := A) (x : A) |>.choose) <| by
    intro hzero
    have hpow := divisionAlgebra_norm_eq_degree_pow
      (F := F) (A := A) (x : A) |>.choose_spec
    rw [hzero, zero_pow (divisionAlgebraDegree_pos (F := F) (A := A)).ne'] at hpow
    exact Algebra.norm_ne_zero_iff.mpr x.ne_zero hpow

/-- The regular determinant of a unit is the degree-th power of its chosen central root. -/
theorem divisionAlgebraDeterminantDegreeRoot_pow (x : Aˣ) :
    Algebra.norm F (x : A) =
      (divisionAlgebraDeterminantDegreeRoot (F := F) (A := A) x : F) ^
        divisionAlgebraDegree (F := F) (A := A) :=
  divisionAlgebra_norm_eq_degree_pow (F := F) (A := A) (x : A) |>.choose_spec

end

end GaloisForLFunctions.HTGeometry.ABHN
