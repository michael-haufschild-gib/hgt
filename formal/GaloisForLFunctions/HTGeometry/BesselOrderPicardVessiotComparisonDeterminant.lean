import GaloisForLFunctions.HTGeometry.BesselOrderPicardVessiotNoNewConstants
import GaloisForLFunctions.HTGeometry.DifferenceComparisonAlgebra
import GaloisForLFunctions.HTGeometry.DifferenceAutomorphismFixedFieldFundamental
import GaloisForLFunctions.HTGeometry.GaloisMonoidRootDeterminant

/-!
# Bessel-order Picard--Vessiot comparison determinant

The ordinary Picard--Vessiot ring already constructed for the Bessel-order companion has exact
constants.  This file constructs its tensor comparison matrix and proves unconditionally that the
square of its determinant is one.  All quotient, simplicity, fundamental-solution, invertibility,
and base-compatibility data are discharged by the concrete Picard--Vessiot construction.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions.HTGeometry
open scoped TensorProduct Differential

abbrev BesselOrderPVNoNewConstantsData.PVRing {s : ℝ}
    (data : BesselOrderPVNoNewConstantsData s) :=
  (pvLocalization (RatFunc Constants) 2) ⧸ data.M

/-- Fundamental solution matrix in the concrete ordinary Bessel-order Picard--Vessiot ring. -/
def BesselOrderPVNoNewConstantsData.fundamentalMatrix {s : ℝ}
    (data : BesselOrderPVNoNewConstantsData s) : Matrix (Fin 2) (Fin 2) data.PVRing :=
  (pvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk data.M)

/-- Difference automorphism induced on the concrete ordinary Bessel-order Picard--Vessiot ring. -/
def BesselOrderPVNoNewConstantsData.sigmaEquiv {s : ℝ}
    (data : BesselOrderPVNoNewConstantsData s) : data.PVRing ≃+* data.PVRing :=
  sigmaQuotientEquiv (besselOrderPVSigma s) data.M data.isSigmaIdeal data.isSigmaIdeal_symm

/-- The quotient difference automorphism restricts to the rational shift on the base. -/
theorem BesselOrderPVNoNewConstantsData.baseCompatible {s : ℝ}
    (data : BesselOrderPVNoNewConstantsData s) (x : RatFunc Constants) :
    data.sigmaEquiv (algebraMap (RatFunc Constants) data.PVRing x) =
      algebraMap (RatFunc Constants) data.PVRing (FieldShift.ratShiftEquiv x) := by
  change sigmaQuotientEquiv (besselOrderPVSigma s) data.M data.isSigmaIdeal
      data.isSigmaIdeal_symm
        (Ideal.Quotient.mk data.M (algebraMap (RatFunc Constants)
          (pvLocalization (RatFunc Constants) 2) x)) =
    Ideal.Quotient.mk data.M (algebraMap (RatFunc Constants)
      (pvLocalization (RatFunc Constants) 2) (FieldShift.ratShiftEquiv x))
  rw [sigmaQuotientEquiv_mk]
  simp only [besselOrderPVSigma, pvSigma_algebraMap]

/-- Concrete comparison data in the tensor square of the ordinary Bessel-order PV ring. -/
structure BesselOrderPVNoNewConstantsData.ComparisonDeterminantData {s : ℝ}
    (data : BesselOrderPVNoNewConstantsData s) where
  Z : Matrix (Fin 2) (Fin 2) (data.PVRing ⊗[RatFunc Constants] data.PVRing)
  factorization : leftFundamental (RatFunc Constants) data.fundamentalMatrix * Z =
    rightFundamental (RatFunc Constants) data.fundamentalMatrix
  fixed : ∀ i j,
    differenceTensorEquiv FieldShift.ratShiftEquiv data.sigmaEquiv data.baseCompatible (Z i j) =
      Z i j
  det_isUnit : IsUnit Z.det
  det_sq_eq_one : Z.det ^ 2 = 1

/-- Every concrete ordinary Bessel-order PV ring has comparison data with determinant square one. -/
theorem BesselOrderPVNoNewConstantsData.comparisonDeterminantData_nonempty
    {s : ℝ} (data : BesselOrderPVNoNewConstantsData s) :
    Nonempty data.ComparisonDeterminantData := by
  letI : Nontrivial data.PVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  letI : Invertible data.fundamentalMatrix :=
    Matrix.invertibleOfIsUnitDet data.fundamentalMatrix data.fundamental_det_isUnit
  have hfund : data.fundamentalMatrix.map data.sigmaEquiv =
      ((FieldShift.besselOrderCompanion (slope s)).map
        (algebraMap (RatFunc Constants) data.PVRing)) * data.fundamentalMatrix := by
    ext i j
    exact data.fundamental i j
  obtain ⟨Z, hZ, hZfixed, hZunit⟩ := exists_tensor_comparison_matrix
    FieldShift.ratShiftEquiv data.sigmaEquiv data.baseCompatible
    (FieldShift.besselOrderCompanion (slope s)) data.fundamentalMatrix hfund
  have hAdet :
      (((FieldShift.besselOrderCompanion (slope s)).map
        (algebraMap (RatFunc Constants) data.PVRing))).det = -1 := by
    simp [FieldShift.besselOrderCompanion, Matrix.det_fin_two]
  have hnonew : ∀ x : data.PVRing, data.sigmaEquiv x = x →
      ∃ a : RatFunc Constants, x = algebraMap (RatFunc Constants) data.PVRing a := by
    intro x hx
    obtain ⟨a, -, ha⟩ := data.noNewConstants x hx
    exact ⟨a, ha⟩
  have hdet := comparisonMatrix_det_sq_eq_one_of_neg_one_system
    ((FieldShift.besselOrderCompanion (slope s)).map
      (algebraMap (RatFunc Constants) data.PVRing))
    data.fundamentalMatrix hAdet data.fundamental_det_isUnit hfund hnonew Z hZ
  exact ⟨⟨Z, hZ, fun i j => congrFun (congrFun hZfixed i) j, hZunit, hdet⟩⟩

/-- Unconditional ordinary Bessel-order PV comparison determinant theorem. -/
theorem besselOrder_picardVessiot_comparisonDeterminant_exists :
    ∀ s : ℝ, ∃ data : BesselOrderPVNoNewConstantsData s,
      Nonempty data.ComparisonDeterminantData := by
  intro s
  obtain ⟨data⟩ := besselOrder_picardVessiot_noNewConstants_exists s
  exact ⟨data, data.comparisonDeterminantData_nonempty⟩

/-- Chosen inverse of the comparison determinant. -/
noncomputable def BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.inverseDet
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData) :
    data.PVRing ⊗[RatFunc Constants] data.PVRing :=
  ↑comparison.det_isUnit.unit⁻¹

theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.det_mul_inverseDet
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData) :
    comparison.Z.det * comparison.inverseDet = 1 := by
  change comparison.Z.det * (↑comparison.det_isUnit.unit⁻¹ :
    data.PVRing ⊗[RatFunc Constants] data.PVRing) = 1
  calc
    comparison.Z.det * (↑comparison.det_isUnit.unit⁻¹ :
        data.PVRing ⊗[RatFunc Constants] data.PVRing) =
        (↑comparison.det_isUnit.unit :
          data.PVRing ⊗[RatFunc Constants] data.PVRing) *
          ↑comparison.det_isUnit.unit⁻¹ := by
            exact congrArg (fun x => x *
              (↑comparison.det_isUnit.unit⁻¹ :
                data.PVRing ⊗[RatFunc Constants] data.PVRing))
              comparison.det_isUnit.unit_spec.symm
    _ = 1 := by simp

/-- Finite ordinary comparison algebra of the concrete Bessel PV datum. -/
abbrev BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.Algebra
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData) :=
  comparisonAlgebra (C := Constants) comparison.Z comparison.inverseDet

/-- Every ordinary Bessel Galois-monoid determinant has square one. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.galoisMonoid_det_sq_eq_one
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData)
    (S : Set (comparison.Algebra →ₐ[Constants] Constants))
    {g : Matrix (Fin 2) (Fin 2) Constants}
    (hg : g ∈ galoisMonoid comparison.Algebra comparison.Z
      (fun i j => mem_comparisonAlgebra_entry comparison.Z comparison.inverseDet i j) S) :
    g.det ^ 2 = 1 :=
  galoisMonoid_det_pow_eq_one comparison.Algebra comparison.Z
    (fun i j => mem_comparisonAlgebra_entry comparison.Z comparison.inverseDet i j)
    comparison.det_sq_eq_one S hg

/-- Every ordinary Bessel Galois-monoid determinant is nonzero. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.galoisMonoid_det_ne_zero
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData)
    (S : Set (comparison.Algebra →ₐ[Constants] Constants))
    {g : Matrix (Fin 2) (Fin 2) Constants}
    (hg : g ∈ galoisMonoid comparison.Algebra comparison.Z
      (fun i j => mem_comparisonAlgebra_entry comparison.Z comparison.inverseDet i j) S) :
    g.det ≠ 0 :=
  galoisMonoid_det_ne_zero_of_sq_eq_one comparison.Algebra comparison.Z
    (fun i j => mem_comparisonAlgebra_entry comparison.Z comparison.inverseDet i j)
    comparison.det_sq_eq_one S hg

/-- Every ordinary Bessel Galois-monoid determinant is a differential constant. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.galoisMonoid_det_constant
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData)
    (S : Set (comparison.Algebra →ₐ[Constants] Constants))
    {g : Matrix (Fin 2) (Fin 2) Constants}
    (hg : g ∈ galoisMonoid comparison.Algebra comparison.Z
      (fun i j => mem_comparisonAlgebra_entry comparison.Z comparison.inverseDet i j) S) :
    g.det ∈ differentialConstants Constants :=
  galoisMonoid_det_mem_differentialConstants_of_sq_eq_one
    comparison.Algebra comparison.Z
    (fun i j => mem_comparisonAlgebra_entry comparison.Z comparison.inverseDet i j)
    comparison.det_sq_eq_one S hg

/-- The ordinary quotient difference action fixes the constant coefficient field. -/
theorem BesselOrderPVNoNewConstantsData.baseConstantsFixed
    {s : ℝ} (data : BesselOrderPVNoNewConstantsData s) (c : Constants) :
    data.sigmaEquiv (algebraMap Constants data.PVRing c) =
      algebraMap Constants data.PVRing c := by
  rw [IsScalarTower.algebraMap_apply Constants (RatFunc Constants) data.PVRing,
    data.baseCompatible, FieldShift.ratShiftEquiv_apply, FieldShift.ratShift_const]

/-- Exact ordinary constants, restated over `Constants` rather than `Constants(z)`. -/
theorem BesselOrderPVNoNewConstantsData.noNewConstants_over_constants
    {s : ℝ} (data : BesselOrderPVNoNewConstantsData s)
    (x : data.PVRing) (hx : data.sigmaEquiv x = x) :
    ∃ c : Constants, x = algebraMap Constants data.PVRing c := by
  obtain ⟨a, ha, hxa⟩ := data.noNewConstants x hx
  have harat : FieldShift.ratShift a = a := by
    simpa only [FieldShift.ratShiftEquiv_apply] using ha
  obtain ⟨c, hac⟩ := FieldShift.ratShift_fixed_eq_const harat
  refine ⟨c, ?_⟩
  rw [hxa, hac, IsScalarTower.algebraMap_apply Constants (RatFunc Constants) data.PVRing]

/-- Every element of the concrete ordinary comparison algebra is shift-fixed. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.algebra_fixed
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData)
    (e : data.PVRing ⊗[RatFunc Constants] data.PVRing)
    (he : e ∈ comparison.Algebra) :
    differenceTensorEquiv FieldShift.ratShiftEquiv data.sigmaEquiv
      data.baseCompatible e = e :=
  comparisonAlgebra_fixed data.baseCompatible data.baseConstantsFixed
    comparison.Z comparison.fixed comparison.inverseDet comparison.det_mul_inverseDet he

/-- Left PV coordinates and the concrete comparison algebra generate the tensor square. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.tensor_generated
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData) :
    Algebra.adjoin Constants
      (Set.range (fun r : data.PVRing =>
        r ⊗ₜ[RatFunc Constants] (1 : data.PVRing)) ∪
        (comparison.Algebra : Set
          (data.PVRing ⊗[RatFunc Constants] data.PVRing))) = ⊤ :=
  adjoin_comparisonAlgebra_eq_top data.fundamentalMatrix data.detInverse
    data.fundamental_det_mul_inverse data.generated comparison.Z comparison.inverseDet
    comparison.factorization comparison.det_mul_inverseDet

/-- A constants basis of the comparison algebra remains independent over the concrete PV ring. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.basis_independent
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData) :
    LinearIndependent data.PVRing (fun i =>
      (((Module.Free.chooseBasis Constants comparison.Algebra) i : comparison.Algebra) :
        data.PVRing ⊗[RatFunc Constants] data.PVRing)) := by
  letI : Nontrivial data.PVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  exact linearIndependent_comparisonAlgebra_chooseBasis
    data.baseCompatible data.baseConstantsFixed data.isSigmaSimple
    data.noNewConstants_over_constants comparison.Z comparison.fixed comparison.inverseDet
    comparison.det_mul_inverseDet

/-- The fixed field of the full ordinary Bessel difference-automorphism group is the base. -/
theorem BesselOrderPVNoNewConstantsData.ComparisonDeterminantData.fixedField
    {s : ℝ} {data : BesselOrderPVNoNewConstantsData s}
    (comparison : data.ComparisonDeterminantData)
    {x : data.PVRing}
    (hx : ∀ g : differenceAut (K := RatFunc Constants) data.sigmaEquiv, g.1 x = x) :
    ∃ k : RatFunc Constants,
      x = algebraMap (RatFunc Constants) data.PVRing k := by
  letI : Nontrivial data.PVRing := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  exact exists_eq_algebraMap_of_forall_differenceAut_of_comparison
    data.baseCompatible data.baseConstantsFixed data.isSigmaSimple
    data.noNewConstants_over_constants data.fundamentalMatrix comparison.Z
    comparison.factorization comparison.fixed comparison.inverseDet
    comparison.det_mul_inverseDet data.detInverse data.fundamental_det_mul_inverse
    data.generated hx

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
