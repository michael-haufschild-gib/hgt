import GaloisForLFunctions.RHTower.HedenmalmThetaDerivativeHistorySpectrum
import GaloisForLFunctions.RHTower.HedenmalmPrimeTranslationJordanCapstone
import GaloisForLFunctions.HTGeometry.GeneralizedEigenspaceQuotient
import GaloisForLFunctions.HTGeometry.CompactInvariantQuotient

/-!
# The full nonzero Xi divisor on the actual derivative-history quotient

The compact source inverse acts on the literal Hilbert quotient by its closed
actual derivative history. The restriction to history has spectrum `{0}`.
For each nonzero scalar, quotient projection therefore identifies every
generalized root space, including the maximal root block. Thus the quotient
retains all nonzero spectral values and their full algebraic multiplicities.
The existing determinant identity identifies these multiplicities with the
analytic Xi divisor, without a strip or simplicity hypothesis.
-/

open MeasureTheory Set Topology Complex Module

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmHilbertSchmidt

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev RH := thetaQuantileDerivativeHistory

theorem thetaQuantileDerivativeHistory_isClosed :
    IsClosed (thetaQuantileDerivativeHistory : Set H) :=
  (Submodule.span ℂ (range thetaQuantileDerivativeVector)).isClosed_topologicalClosure

local instance : IsClosed (RH : Set H) := thetaQuantileDerivativeHistory_isClosed
local instance : CompleteSpace RH := thetaQuantileDerivativeHistory_isClosed.completeSpace_coe

abbrev ThetaDerivativeHistoryQuotient := H ⧸ thetaQuantileDerivativeHistory

def thetaDerivativeHistoryQuotientProjection : H →L[ℂ] ThetaDerivativeHistoryQuotient :=
  thetaQuantileDerivativeHistory.mkQL

def thetaDerivativeHistoryQuotientInverse :
    ThetaDerivativeHistoryQuotient →L[ℂ] ThetaDerivativeHistoryQuotient :=
  continuousInvariantQuotient thetaCompactSourceInverse thetaQuantileDerivativeHistory
    (fun _ hf => thetaQuantileDerivativeHistory_invariant hf)

theorem thetaDerivativeHistoryQuotientProjection_eq_zero_iff (f : H) :
    thetaDerivativeHistoryQuotientProjection f = 0 ↔ f ∈ thetaQuantileDerivativeHistory :=
  Submodule.Quotient.mk_eq_zero thetaQuantileDerivativeHistory

theorem thetaDerivativeHistoryQuotientProjection_derivative (n : ℕ) :
    thetaDerivativeHistoryQuotientProjection (thetaQuantileDerivativeVector n) = 0 :=
  (thetaDerivativeHistoryQuotientProjection_eq_zero_iff _).mpr
    (thetaQuantileDerivativeVector_mem_history n)

theorem thetaDerivativeHistoryQuotientInverse_projection (f : H) :
    thetaDerivativeHistoryQuotientInverse (thetaDerivativeHistoryQuotientProjection f) =
      thetaDerivativeHistoryQuotientProjection (thetaCompactSourceInverse f) :=
  continuousInvariantQuotient_mkQL _ _ _ f

theorem isCompactOperator_thetaDerivativeHistoryQuotientInverse :
    IsCompactOperator thetaDerivativeHistoryQuotientInverse :=
  isCompactOperator_continuousInvariantQuotient _ _ _
    isCompactOperator_thetaCompactSourceInverse

/-- Every nonzero shift of the actual history restriction is invertible. -/
theorem isUnit_thetaDerivativeHistoryInverse_sub_smul {lam : ℂ} (hlam : lam ≠ 0) :
    IsUnit (thetaDerivativeHistoryInverse - lam • 1) := by
  have hnot : lam ∉ spectrum ℂ thetaDerivativeHistoryInverse := by
    rw [thetaDerivativeHistoryInverse_spectrum]
    simpa using hlam
  have hu := (spectrum.notMem_iff).mp hnot
  simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using hu.neg

private theorem thetaHistory_linear_shift_isUnit {lam : ℂ} (hlam : lam ≠ 0) :
    IsUnit (thetaCompactSourceInverse.toLinearMap.restrict
      (fun _ hf => thetaQuantileDerivativeHistory_invariant hf) - lam • 1) := by
  change IsUnit ((thetaDerivativeHistoryInverse - lam • 1).toLinearMap)
  exact ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mp
    (isUnit_thetaDerivativeHistoryInverse_sub_smul hlam)

/-- Quotient projection itself is the exact equivalence on every nonzero root level. -/
def thetaDerivativeHistoryQuotientRootEquiv {lam : ℂ} (hlam : lam ≠ 0) (k : ℕ∞) :
    Module.End.genEigenspace thetaCompactSourceInverse.toLinearMap lam k ≃ₗ[ℂ]
      Module.End.genEigenspace thetaDerivativeHistoryQuotientInverse.toLinearMap lam k :=
  quotientGenEigenspaceEquiv thetaCompactSourceInverse.toLinearMap thetaQuantileDerivativeHistory
    (fun _ hf => thetaQuantileDerivativeHistory_invariant hf) lam
    (thetaHistory_linear_shift_isUnit hlam) k

theorem thetaDerivativeHistoryQuotientRootEquiv_apply {lam : ℂ} (hlam : lam ≠ 0)
    (k : ℕ∞) (f : Module.End.genEigenspace thetaCompactSourceInverse.toLinearMap lam k) :
    (thetaDerivativeHistoryQuotientRootEquiv hlam k f : ThetaDerivativeHistoryQuotient) =
      thetaDerivativeHistoryQuotientProjection f := rfl

theorem finrank_genEigenspace_thetaDerivativeHistoryQuotientInverse {lam : ℂ}
    (hlam : lam ≠ 0) (k : ℕ∞) :
    Module.finrank ℂ (Module.End.genEigenspace thetaCompactSourceInverse.toLinearMap lam k) =
      Module.finrank ℂ
        (Module.End.genEigenspace thetaDerivativeHistoryQuotientInverse.toLinearMap lam k) :=
  (thetaDerivativeHistoryQuotientRootEquiv hlam k).finrank_eq

theorem finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse {lam : ℂ}
    (hlam : lam ≠ 0) :
    Module.finrank ℂ (Module.End.maxGenEigenspace thetaCompactSourceInverse.toLinearMap lam) =
      Module.finrank ℂ
        (Module.End.maxGenEigenspace thetaDerivativeHistoryQuotientInverse.toLinearMap lam) :=
  finrank_genEigenspace_thetaDerivativeHistoryQuotientInverse hlam ⊤

theorem thetaDerivativeHistoryQuotientProjection_root_ne_zero {lam : ℂ}
    (hlam : lam ≠ 0) {k : ℕ∞} {f : H}
    (hf : f ∈ Module.End.genEigenspace thetaCompactSourceInverse.toLinearMap lam k)
    (hf0 : f ≠ 0) : thetaDerivativeHistoryQuotientProjection f ≠ 0 := by
  intro hzero
  exact hf0 (eq_zero_of_mem_genEigenspace_of_mem_invariant thetaCompactSourceInverse.toLinearMap
    thetaQuantileDerivativeHistory (fun _ hf => thetaQuantileDerivativeHistory_invariant hf)
    lam (thetaHistory_linear_shift_isUnit hlam) hf
    ((thetaDerivativeHistoryQuotientProjection_eq_zero_iff f).mp hzero))

theorem hasEigenvalue_thetaDerivativeHistoryQuotientInverse_iff {lam : ℂ} (hlam : lam ≠ 0) :
    Module.End.HasEigenvalue thetaDerivativeHistoryQuotientInverse.toLinearMap lam ↔
      Module.End.HasEigenvalue thetaCompactSourceInverse.toLinearMap lam :=
  hasEigenvalue_mapQ_iff thetaCompactSourceInverse.toLinearMap thetaQuantileDerivativeHistory
    (fun _ hf => thetaQuantileDerivativeHistory_invariant hf) lam
    (thetaHistory_linear_shift_isUnit hlam)

/-- The literal quotient preserves the entire nonzero spectrum. -/
theorem mem_spectrum_thetaDerivativeHistoryQuotientInverse_iff {lam : ℂ} (hlam : lam ≠ 0) :
    lam ∈ spectrum ℂ thetaDerivativeHistoryQuotientInverse ↔
      lam ∈ spectrum ℂ thetaCompactSourceInverse :=
  (isCompactOperator_thetaDerivativeHistoryQuotientInverse.hasEigenvalue_iff_mem_spectrum hlam).symm.trans
    ((hasEigenvalue_thetaDerivativeHistoryQuotientInverse_iff hlam).trans
      (isCompactOperator_thetaCompactSourceInverse.hasEigenvalue_iff_mem_spectrum hlam))

theorem nonzero_spectrum_thetaDerivativeHistoryQuotientInverse :
    spectrum ℂ thetaDerivativeHistoryQuotientInverse \ {0} =
      spectrum ℂ thetaCompactSourceInverse \ {0} := by
  ext lam
  constructor
  · rintro ⟨hspec, hzero⟩
    have hlam : lam ≠ 0 := by simpa using hzero
    exact ⟨(mem_spectrum_thetaDerivativeHistoryQuotientInverse_iff hlam).mp hspec, hzero⟩
  · rintro ⟨hspec, hzero⟩
    have hlam : lam ≠ 0 := by simpa using hzero
    exact ⟨(mem_spectrum_thetaDerivativeHistoryQuotientInverse_iff hlam).mpr hspec, hzero⟩

/-- Reciprocal nonzero quotient spectral values are exactly all complex Xi zeros. -/
theorem thetaDerivativeHistoryQuotientInverse_reciprocal_mem_spectrum_iff_XiC_eq_zero
    {z : ℂ} (hz : z ≠ 0) :
    -z⁻¹ ∈ spectrum ℂ thetaDerivativeHistoryQuotientInverse ↔ XiC z = 0 := by
  have hlam : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
  rw [mem_spectrum_thetaDerivativeHistoryQuotientInverse_iff hlam,
    ← isCompactOperator_thetaCompactSourceInverse.hasEigenvalue_iff_mem_spectrum hlam]
  constructor
  · intro h
    obtain ⟨f, hf⟩ := h.exists_hasEigenvector
    exact XiC_eq_zero_of_thetaCompactSourceInverse_eigen hz hf.2 hf.apply_eq_smul
  · intro hXi
    have hdet := (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).mpr hXi
    obtain ⟨f, hf0, hf⟩ := (thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector hz).mp hdet
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr ?_, hf0⟩
    change thetaCompactSourceInverse f = -z⁻¹ • f
    simpa only [thetaKernelOperator_eq_thetaCompactSourceInverse] using hf

/-- The canonical actual source eigenmode has a nonzero quotient class. -/
theorem thetaDivisorEigenvector_quotient_ne_zero (z : ℂ) (hstrip : |z.im| < 1)
    (hzero : xiC thetaSource z = 0) :
    thetaDerivativeHistoryQuotientProjection (thetaDivisorEigenvector z hstrip hzero) ≠ 0 := by
  have hXi : XiC z = 0 := by rw [← xiC_thetaSource hstrip]; exact hzero
  have hz : z ≠ 0 := by intro hz; exact XiC_zero_ne (by simpa [hz] using hXi)
  apply thetaDerivativeHistoryQuotientProjection_root_ne_zero (neg_ne_zero.mpr (inv_ne_zero hz))
    (k := 1)
  · exact Module.End.mem_eigenspace_iff.mpr (thetaCompactSourceInverse_eigen z hstrip hzero)
  · exact thetaDivisorEigenvector_ne_zero z hstrip hzero

theorem thetaDerivativeHistoryQuotientInverse_thetaDivisorEigenvector
    (z : ℂ) (hstrip : |z.im| < 1) (hzero : xiC thetaSource z = 0) :
    thetaDerivativeHistoryQuotientInverse
        (thetaDerivativeHistoryQuotientProjection (thetaDivisorEigenvector z hstrip hzero)) =
      -z⁻¹ • thetaDerivativeHistoryQuotientProjection (thetaDivisorEigenvector z hstrip hzero) := by
  rw [thetaDerivativeHistoryQuotientInverse_projection, thetaCompactSourceInverse_eigen, map_smul]

/-- The quotient keeps the full analytic Xi multiplicity at every complex zero. -/
theorem analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse
    {z : ℂ} (hXi : XiC z = 0) :
    analyticOrderAt XiC z =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        thetaDerivativeHistoryQuotientInverse.toLinearMap (-z⁻¹)) : ℕ∞) := by
  have hz : z ≠ 0 := by intro hz; exact XiC_zero_ne (by simpa [hz] using hXi)
  have hlam : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
  calc
    _ = (Module.finrank ℂ (Module.End.maxGenEigenspace
        thetaCompactSourceInverse.toLinearMap (-z⁻¹)) : ℕ∞) := by
      change analyticOrderAt XiC z =
        (Module.finrank ℂ (Module.End.maxGenEigenspace
          (thetaKernelOperator : Module.End ℂ H) (-z⁻¹)) : ℕ∞)
      exact analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_thetaKernelOperator hXi
    _ = _ := by rw [finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse hlam]

theorem finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse_eq_xiSupportMultiplicity
    (rho : XiDivisorSupport) :
    Module.finrank ℂ (Module.End.maxGenEigenspace thetaDerivativeHistoryQuotientInverse.toLinearMap
      (-(xiSpectralPointSupport rho)⁻¹)) = xiSupportMultiplicity rho := by
  have hXi := XiC_xiSpectralPointSupport_eq_zero rho
  have hz : xiSpectralPointSupport rho ≠ 0 := by
    intro hz
    exact XiC_zero_ne (by simpa [hz] using hXi)
  rw [← finrank_maxGenEigenspace_thetaDerivativeHistoryQuotientInverse
    (neg_ne_zero.mpr (inv_ne_zero hz))]
  change Module.finrank ℂ (Module.End.maxGenEigenspace
    (thetaKernelOperator : Module.End ℂ H) (-(xiSpectralPointSupport rho)⁻¹)) =
      xiSupportMultiplicity rho
  exact finrank_maxGenEigenspace_thetaKernelOperator_eq_xiSupportMultiplicity rho

end

end RHTower.HedenmalmThetaSource
