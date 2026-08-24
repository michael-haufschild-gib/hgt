import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageDenseRank
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteInertia

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Literal projected Hardy leakage of the finite shifted-Xi tail. -/
def xiShiftFiniteLeakageCore
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    HardyDisk →L[ℂ] finiteBlaschkeModelSpace (xiShiftFinitePoleBlaschke omega) :=
  modelSpaceLeakageCore
    (finiteBlaschkeModelSpace (xiShiftFinitePoleBlaschke omega))
    (hardyMul (xiShiftFiniteSchurNumerator omega homega))

/-- A nonexceptional finite shifted-Xi tail leaks onto its complete denominator model channel. -/
theorem xiShiftFiniteLeakageCore_surjective
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) :
    Function.Surjective (xiShiftFiniteLeakageCore homega) := by
  apply modelSpaceLeakageCore_surjective_of_finiteDimensional
  exact adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_nonzero
    (xiShiftFiniteSchurNumerator omega homega)
    (xiShiftFinitePoleBlaschke omega)
    (xiShiftFiniteSchurNumerator_nonzero_on_poleBlaschkeZeros homega hnon)

/-- Exact finite shifted-Xi leakage rank, with every pole copy counted. -/
theorem finrank_range_xiShiftFiniteLeakageCore
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) :
    Module.finrank ℂ (xiShiftFiniteLeakageCore homega).range =
      Fintype.card (XiShiftRightZeroCopy omega) := by
  have hinj :=
    adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_nonzero
      (xiShiftFiniteSchurNumerator omega homega)
      (xiShiftFinitePoleBlaschke omega)
      (xiShiftFiniteSchurNumerator_nonzero_on_poleBlaschkeZeros homega hnon)
  calc
    Module.finrank ℂ (xiShiftFiniteLeakageCore homega).range =
        Module.finrank ℂ (finiteBlaschkeModelSpace (xiShiftFinitePoleBlaschke omega)) :=
      finrank_range_modelSpaceLeakageCore_of_finiteDimensional
        (finiteBlaschkeModelSpace (xiShiftFinitePoleBlaschke omega))
        (hardyMul (xiShiftFiniteSchurNumerator omega homega)) hinj
    _ = (xiShiftFinitePoleBlaschke omega).deg :=
      finrank_finiteBlaschkeModelSpace (xiShiftFinitePoleBlaschke omega)
    _ = Fintype.card (XiShiftRightZeroCopy omega) :=
      xiShiftFinitePoleBlaschke_deg omega

end

end RHTower

