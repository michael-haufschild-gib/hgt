import GaloisForLFunctions.HTGeometry.BesselOrderPeriodicConstantCompositum
import GaloisForLFunctions.HTGeometry.BesselOrderActualFundamentalMatrix

/-!
# Actual Bessel system over exact periodic constants

Scalar extension from the unit-periodic meromorphic field to the common differentially closed
constant field preserves sigma-simplicity and has exactly that common field as its fixed ring.  The
actual phase-twisted `I`/`K` fundamental matrix embeds in this ring, remains nonsingular, and obeys
the exact translated Bessel companion system.
-/

open scoped Differential TensorProduct UnivMeroFieldInstances

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher

noncomputable section

noncomputable instance besselActualPeriodicConstantsAlgebra :
    Algebra UnitPeriodicMeromorphicField BesselPeriodicConstants :=
  periodicToBesselPeriodicConstants.toAlgebra

/-- Scalar extension containing the common constants and actual global meromorphic functions. -/
abbrev BesselActualPeriodicScalarRing :=
  BesselPeriodicConstants ⊗[UnitPeriodicMeromorphicField] meroField Set.univ

/-- Unit order translation on the actual periodic scalar extension. -/
def besselActualPeriodicScalarShift :
    BesselActualPeriodicScalarRing ≃+* BesselActualPeriodicScalarRing :=
  scalarExtensionSigma (C := UnitPeriodicMeromorphicField)
    (L := BesselPeriodicConstants) (F := meroField Set.univ)
    (addTranslationMeroEquiv 1) unitTranslation_fixed_periodic

/-- The actual periodic scalar extension is sigma-simple. -/
theorem besselActualPeriodicScalarShift_isSigmaSimple :
    IsSigmaSimple besselActualPeriodicScalarShift :=
  scalarExtension_isSigmaSimple
    (C := UnitPeriodicMeromorphicField)
    (L := BesselPeriodicConstants) (F := meroField Set.univ)
    (addTranslationMeroEquiv 1) unitTranslation_fixed_periodic
    unitTranslation_exact_periodic

/-- Fixed elements of the actual scalar extension are precisely the common constants. -/
theorem besselActualPeriodicScalarShift_fixed
    {z : BesselActualPeriodicScalarRing}
    (hz : besselActualPeriodicScalarShift z = z) :
    ∃ c : BesselPeriodicConstants,
      z = Algebra.TensorProduct.includeLeft
        (R := UnitPeriodicMeromorphicField)
        (S := UnitPeriodicMeromorphicField)
        (A := BesselPeriodicConstants)
        (B := meroField Set.univ) c :=
  scalarExtension_fixed_eq_includeLeft
    (C := UnitPeriodicMeromorphicField)
    (L := BesselPeriodicConstants) (F := meroField Set.univ)
    (addTranslationMeroEquiv 1) unitTranslation_fixed_periodic
    unitTranslation_exact_periodic hz

/-- Actual nonsingular Bessel matrix in the exact-periodic scalar extension. -/
def besselOrderActualFundamentalMatrixPeriodicScalar
    (s : ℝ) (hs : 0 < s) :
    Matrix (Fin 2) (Fin 2) BesselActualPeriodicScalarRing :=
  (besselOrderActualFundamentalMatrix s hs).map
    (Algebra.TensorProduct.includeRight :
      meroField Set.univ →ₐ[UnitPeriodicMeromorphicField]
        BesselActualPeriodicScalarRing).toRingHom

/-- Meromorphic Bessel companion matrix in the exact-periodic scalar extension. -/
def besselOrderCompanionPeriodicScalar (s : ℝ) :
    Matrix (Fin 2) (Fin 2) BesselActualPeriodicScalarRing :=
  (besselOrderCompanionMero s).map
    (Algebra.TensorProduct.includeRight :
      meroField Set.univ →ₐ[UnitPeriodicMeromorphicField]
        BesselActualPeriodicScalarRing).toRingHom

/-- The embedded actual matrix solves the translated Bessel companion system. -/
theorem besselOrderActualFundamentalMatrixPeriodicScalar_system
    (s : ℝ) (hs : 0 < s) :
    (besselOrderActualFundamentalMatrixPeriodicScalar s hs).map
        besselActualPeriodicScalarShift =
      besselOrderCompanionPeriodicScalar s *
        besselOrderActualFundamentalMatrixPeriodicScalar s hs := by
  ext i j
  simp only [besselOrderActualFundamentalMatrixPeriodicScalar,
    besselOrderCompanionPeriodicScalar, Matrix.map_apply, Matrix.mul_apply]
  change (1 : BesselPeriodicConstants) ⊗ₜ[UnitPeriodicMeromorphicField]
      addTranslationMeroEquiv 1 (besselOrderActualFundamentalMatrix s hs i j) = _
  have hentry := congrFun (congrFun
    (besselOrderActualFundamentalMatrix_system s hs) i) j
  change addTranslationMeroEquiv 1
      (besselOrderActualFundamentalMatrix s hs i j) =
    (besselOrderCompanionMero s *
      besselOrderActualFundamentalMatrix s hs) i j at hentry
  rw [hentry]
  simp [Matrix.mul_apply, TensorProduct.tmul_add,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Nonsingularity survives the faithful right tensor inclusion. -/
theorem besselOrderActualFundamentalMatrixPeriodicScalar_det_ne_zero
    (s : ℝ) (hs : 0 < s) :
    (besselOrderActualFundamentalMatrixPeriodicScalar s hs).det ≠ 0 := by
  have hright : Function.Injective
      (Algebra.TensorProduct.includeRight :
        meroField Set.univ →ₐ[UnitPeriodicMeromorphicField]
          BesselActualPeriodicScalarRing) := by
    letI : Module.Free UnitPeriodicMeromorphicField (meroField Set.univ) :=
      Module.Free.of_divisionRing _ _
    letI : Module.Flat UnitPeriodicMeromorphicField (meroField Set.univ) :=
      Module.Flat.of_free
    exact Algebra.TensorProduct.includeRight_injective
      (R := UnitPeriodicMeromorphicField)
      (A := BesselPeriodicConstants) (B := meroField Set.univ)
      (algebraMap UnitPeriodicMeromorphicField BesselPeriodicConstants).injective
  rw [besselOrderActualFundamentalMatrixPeriodicScalar]
  have hdet := RingHom.map_det
    (Algebra.TensorProduct.includeRight :
      meroField Set.univ →ₐ[UnitPeriodicMeromorphicField]
        BesselActualPeriodicScalarRing).toRingHom
    (besselOrderActualFundamentalMatrix s hs)
  rw [RingHom.mapMatrix_apply] at hdet
  rw [← hdet]
  intro hzero
  apply besselOrderActualFundamentalMatrix_det_ne_zero s hs
  apply hright
  exact hzero.trans (map_zero
    (Algebra.TensorProduct.includeRight :
      meroField Set.univ →ₐ[UnitPeriodicMeromorphicField]
        BesselActualPeriodicScalarRing)).symm

end


end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
