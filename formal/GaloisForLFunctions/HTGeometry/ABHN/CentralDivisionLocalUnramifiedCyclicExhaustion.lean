import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalCyclicReconstruction
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedRootLiftEquiv
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2BrauerFaithful

/-!
# Unramified cyclic exhaustion of the local Brauer group

Every local Brauer class has a cyclic-algebra representative whose defining cyclic field is
explicitly equivalent to a finite unramified Hensel root lift of the same degree. This combines
crossed-product reconstruction with the concrete fields carrying the finite `ZMod n` invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued WithZero WithZeroMulInt

variable {F : Type} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F]

/-- Every local Brauer class occurs in a cyclic slice certified equivalent to a concrete finite
unramified root lift, with exact agreement of the two extension degrees. -/
theorem nonarchimedeanLocal_brauerGroup_exists_unramifiedRootLiftCyclicRepresentative
    (x : BrauerGroup F) :
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
      change (NormedField.valuation (K := F)).IsNontrivial
      exact Valuation.RankOne.toIsNontrivial
    letI : IsNonarchimedeanLocalField F :=
      isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
    ∃ (T : Type) (_ : Field T) (_ : Algebra F T) (_ : FiniteDimensional F T)
      (_ : IsGalois F T) (_ : IsCyclic Gal(T / F)) (a : Fˣ),
      x = brauerClass
          (cyclicGaloisAlgebraCSA F T ((a⁻¹ : Fˣ) : F) (Units.ne_zero (a⁻¹))) ∧
        ∃ R : NonarchimedeanFiniteUnramifiedRootLift F,
          R.polynomial.natDegree = Module.finrank F T ∧
          let B := AdjoinRoot R.polynomial
          let U := FractionRing B
          ∃ (_ : IsDomain B) (_ : Algebra F U),
            Nonempty (U ≃ₐ[F] T) ∧
              Nonempty (cyclicGaloisH2 F T ≃+ ZMod R.polynomial.natDegree) ∧
                Nonempty (ZMod R.polynomial.natDegree ≃+
                  cyclicGaloisBrauerSubgroup F T) := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  obtain ⟨D, hD, aD, finD, centralD, hx⟩ :=
    brauerGroup_exists_centralDivisionRepresentative F x
  letI : DivisionRing D := hD
  letI : Algebra F D := aD
  letI : Module.Finite F D := finD
  letI : Algebra.IsCentral F D := centralD
  obtain ⟨z, hT, hdegree, ⟨hres⟩, hGalois, hCyclic, u, a, hcomm, hpow, ⟨e⟩⟩ :=
    exists_residueExhausting_cyclicGaloisAlgebraAlgEquiv (F := F) (A := D)
  let T := Algebra.adjoin F ({((z :
    divisionAlgebraDeterminantValuationSubring (F := F) (A := D)) : D)} : Set D)
  letI : Field T := hT.toField
  letI : Algebra F T := Subalgebra.algebra T
  letI : NormedDivisionRing D :=
    divisionAlgebraRootDeterminantNormedDivisionRing (F := F) (A := D)
  letI : NontriviallyNormedField T :=
    divisionAlgebraRestrictedRootDeterminantNontriviallyNormedField
      (F := F) (A := D) T hT
  letI : NormedSpace F T :=
    divisionAlgebraRestrictedRootDeterminantNormedSpace (F := F) (A := D) T hT
  letI : CompleteSpace T :=
    divisionAlgebraRestrictedRootDeterminantCompleteSpace (F := F) (A := D) T hT
  letI : IsUltrametricDist T :=
    divisionAlgebraRestrictedRootDeterminantIsUltrametricDist
      (F := F) (A := D) T hT
  letI : ProperSpace T :=
    divisionAlgebraRestrictedRootDeterminantProperSpace (F := F) (A := D) T hT
  letI : FiniteDimensional F T := by infer_instance
  letI : IsGalois F T := hGalois
  letI : IsCyclic Gal(T / F) := hCyclic
  obtain ⟨R, hRdegree, hdom, aFU, ⟨eUT⟩, ⟨hInv⟩⟩ :=
    divisionAlgebraResidueExhaustingMaximalSubfield_exists_unramifiedRootLiftAlgEquiv
      (F := F) (A := D) T hT hdegree hres
  let hBrauerInv : ZMod R.polynomial.natDegree ≃+ cyclicGaloisBrauerSubgroup F T :=
    cyclicGaloisInvariantBrauerSubgroupAddEquiv
      F T R.polynomial.natDegree hInv
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, a, ?_,
    R, hRdegree, hdom, aFU, ⟨eUT⟩, ⟨hInv⟩, ⟨hBrauerInv⟩⟩
  exact hx.trans (brauerClass_eq_of_algEquiv
    (cyclicGaloisAlgebraCSA F T ((a⁻¹ : Fˣ) : F) (Units.ne_zero (a⁻¹)))
    (centralDivisionCSA F D) e).symm

/-- Every Brauer class over a nonarchimedean local field lies in a finite cyclic subgroup that
is an explicitly certified unramified cyclic slice. This is the finite-slice form of local Brauer
exhaustion needed before assembling the `ℚ/ℤ` colimit invariant. -/
theorem nonarchimedeanLocal_brauerGroup_exists_finiteUnramifiedCyclicSlice
    (x : BrauerGroup F) :
    ∃ (n : ℕ) (S : AddSubgroup (BrauerGroup F)), Nonempty (ZMod n ≃+ S) ∧ x ∈ S := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  obtain ⟨T, hT, aFT, finT, galoisT, cyclicT, a, hx, R, hRdegree, hdom, aFU,
      ⟨eUT⟩, ⟨hInv⟩, ⟨hBrauerInv⟩⟩ :=
    nonarchimedeanLocal_brauerGroup_exists_unramifiedRootLiftCyclicRepresentative x
  letI : Field T := hT
  letI : Algebra F T := aFT
  letI : FiniteDimensional F T := finT
  letI : IsGalois F T := galoisT
  letI : IsCyclic Gal(T / F) := cyclicT
  refine ⟨R.polynomial.natDegree, cyclicGaloisBrauerSubgroup F T, ⟨hBrauerInv⟩, ?_⟩
  rw [hx]
  exact cyclicGaloisAlgebra_brauerClass_mem_cyclicGaloisBrauerSubgroup F T (a⁻¹)

end

end GaloisForLFunctions.HTGeometry.ABHN
