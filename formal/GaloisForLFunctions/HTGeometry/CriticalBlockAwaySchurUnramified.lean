import GaloisForLFunctions.HTGeometry.CriticalSourceChartAwaySchurUnramified
import GaloisForLFunctions.HTGeometry.CriticalBlockNormalizationChart
import GaloisForLFunctions.HTGeometry.IntegralClosureLocalizationEquiv
import GaloisForLFunctions.HTGeometry.DedekindIntermediateFormalUnramified
import GaloisForLFunctions.HTGeometry.CriticalSourceChartMiracleFlatnessData

/-!
# Critical block normalizations are unramified away from Schur

For a block containing the canonical sheet, localize its normalization and the source chart at a
height-one observation prime.  The localized block normalization is the normalization of the local
DVR in the block field, hence Dedekind.  Formal unramifiedness of the source localization descends
through this Dedekind intermediate normalization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 3000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- A canonical-sheet block normalization is formally unramified over every height-one observation
prime distinct from the Schur divisor. -/
theorem criticalBlockNormalization_baseLocalization_formallyUnramified_of_ne_schur
    (P : Ideal (criticalObservationChartRing K m n)) [P.IsPrime]
    (hPheight : P.height = 1)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hmem : criticalSourceNormalClosureEmbedding K m n ∈ B)
    (hP : P ≠ criticalSchurChartUnder K (m := m) (n := n)) :
    Algebra.FormallyUnramified (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid (CriticalBlockNormalization K B)
        P.primeCompl)) := by
  let A := criticalObservationChartRing K m n
  let F := criticalObservationField K m n
  let M := CriticalBlockFixedField K B
  let C := CriticalBlockNormalization K B
  let S := criticalSourceChartRing K m n
  let Ap := Localization.AtPrime P
  let Cp := Localization (Algebra.algebraMapSubmonoid C P.primeCompl)
  let Sp := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  have hunitF : ∀ y : P.primeCompl, IsUnit (algebraMap A F y) := by
    intro y
    have hy0 : (y : A) ≠ 0 := by
      intro hy
      apply y.property
      rw [hy]
      exact P.zero_mem
    have hymap : algebraMap A F (y : A) ≠ 0 := by
      intro hmap
      apply hy0
      apply IsFractionRing.injective A F
      simpa using hmap
    exact hymap.isUnit
  letI : Algebra Ap F :=
    (IsLocalization.lift (S := Ap) (P := F) (g := algebraMap A F) hunitF).toAlgebra
  letI : IsScalarTower A Ap F := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (S := Ap) (P := F) (g := algebraMap A F) hunitF x).symm
  letI : IsFractionRing Ap F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      P.primeCompl Ap F
  letI : Algebra Ap M :=
    ((algebraMap F M).comp (algebraMap Ap F)).toAlgebra
  letI : IsScalarTower Ap F M := IsScalarTower.of_algebraMap_eq' rfl
  let D := integralClosure Ap M
  let fCS : C →ₐ[A] S := blockNormalizationToChart K hB hmem
  letI : Algebra C S := fCS.toAlgebra
  letI : IsScalarTower A C S := IsScalarTower.of_algHom fCS
  let fCpSp : Cp →ₐ[Ap] Sp :=
    IsLocalization.mapₐ P.primeCompl Ap Cp Sp fCS
  have hfCpSp : Function.Injective fCpSp :=
    IsLocalization.mapₐ_injective_of_injective P.primeCompl Ap Cp Sp fCS
      (injective_blockNormalizationToChart K hB hmem)
  letI : Algebra Cp Sp := fCpSp.toAlgebra
  letI : IsScalarTower Ap Cp Sp := IsScalarTower.of_algHom fCpSp
  letI : IsScalarTower A Ap M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A F M,
      IsScalarTower.algebraMap_apply Ap F M,
      ← IsScalarTower.algebraMap_apply A Ap F]
  let eC : Cp ≃ₐ[Ap] D :=
    integralClosureLocalizationAlgEquiv P.primeCompl
  let fDSp : D →ₐ[Ap] Sp := fCpSp.comp eC.symm.toAlgHom
  letI : Algebra D Sp := fDSp.toAlgebra
  letI : IsScalarTower Ap D Sp := IsScalarTower.of_algHom fDSp
  have hfDSp : Function.Injective fDSp := hfCpSp.comp eC.symm.injective
  letI : FaithfulSMul D Sp :=
    (faithfulSMul_iff_algebraMap_injective D Sp).2 hfDSp
  letI : IsDiscreteValuationRing Ap :=
    isDiscreteValuationRing_localizationAtPrime hPheight
  letI : IsDedekindDomain Ap := inferInstance
  haveI : FiniteDimensional F M := by infer_instance
  letI : Module.Finite Ap D := IsIntegralClosure.finite Ap F M D
  letI : IsDedekindDomain D := IsIntegralClosure.isDedekindDomain Ap F M D
  letI : Algebra.IsIntegral D Sp := Algebra.IsIntegral.tower_top Ap
  letI : Algebra.FormallyUnramified Ap Sp :=
    criticalSourceChart_baseLocalization_formallyUnramified_of_ne_schur K P hPheight hP
  have hD : Algebra.FormallyUnramified Ap D :=
    Algebra.formallyUnramified_of_dedekind_intermediate
      (R := Ap) (S := D) (T := Sp)
  exact (Algebra.FormallyUnramified.iff_of_equiv eC).mpr hD

end
end GaloisForLFunctions.HTGeometry
