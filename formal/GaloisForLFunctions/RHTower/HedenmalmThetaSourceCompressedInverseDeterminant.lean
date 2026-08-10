import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDeterminantIdentity
import GaloisForLFunctions.RHTower.HedenmalmThetaTraceKernel
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Hedenmalm's source-derived compact reciprocal-divisor operator

This capstone closes the operator-theoretic clauses of the theta-source card.  The operator is the
source-derived Hilbert--Schmidt inverse `thetaKernelOperator`; no Xi-zero enumeration occurs in its
definition.  Its pencil, nonzero spectrum, algebraic multiplicities, regularized determinant, trace
calibration, and RH spectral-reality criterion are all unconditional consequences of the preceding
source modules.
-/

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry
open Module.End
open MeasureTheory

noncomputable section

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-! ## The source pencil and its exact divisor -/

/-- The bounded source pencil `I + zB`. -/
def thetaSourcePencil (z : ℂ) : ThetaH →L[ℂ] ThetaH :=
  1 + z • thetaKernelOperator

/-- Algebraic rescaling of the resolvent pencil away from the origin. -/
theorem thetaSourcePencil_eq_rescaled_resolvent {z : ℂ} (hz : z ≠ 0) :
    thetaSourcePencil z =
      (algebraMap ℂ (ThetaH →L[ℂ] ThetaH) (-z)) *
        (algebraMap ℂ (ThetaH →L[ℂ] ThetaH) (-z⁻¹) - thetaKernelOperator) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [thetaSourcePencil, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.algebraMap_apply]
  have hscalar : (-z) * (-z⁻¹) = 1 := by field_simp [hz]
  rw [smul_sub, smul_smul, hscalar, one_smul]
  module

/-- **Exact source-pencil divisor law.**  The source pencil is noninvertible exactly at the
centered completed Xi divisor, including `z = 0`. -/
theorem thetaSourcePencil_not_isUnit_iff_XiC_eq_zero (z : ℂ) :
    ¬ IsUnit (thetaSourcePencil z) ↔ XiC z = 0 := by
  by_cases hz : z = 0
  · subst z
    simp [thetaSourcePencil, XiC_zero_ne]
  · constructor
    · intro hnonunit
      have hmu : -z⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
      rcases isCompactOperator_thetaKernelOperator.hasEigenvalue_or_mem_resolventSet hmu with
        heigen | hres
      · obtain ⟨f, hf⟩ := heigen.exists_hasUnifEigenvector
        have hf' : thetaCompactSourceInverse f = (-z⁻¹) • f := by
          rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]
          exact hf.apply_eq_smul
        exact XiC_eq_zero_of_thetaCompactSourceInverse_eigen hz hf.2
          hf'
      · exfalso
        apply hnonunit
        rw [thetaSourcePencil_eq_rescaled_resolvent hz]
        apply IsUnit.mul
        · exact IsUnit.map (algebraMap ℂ (ThetaH →L[ℂ] ThetaH))
            ((isUnit_iff_ne_zero).mpr (neg_ne_zero.mpr hz))
        · exact hres
    · intro hXi hunit
      have hdet : thetaSourceEntireDet2 z = 0 :=
        (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).2 hXi
      obtain ⟨f, hf0, hf⟩ :=
        (thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector hz).1 hdet
      have hker : thetaSourcePencil z f = 0 := by
        rw [thetaSourcePencil, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, hf, smul_smul]
        field_simp [hz]
        simp
      exact hf0 ((ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
        (by simpa using hker))

/-- The three exact divisor descriptions: Xi zero, noninvertible source pencil, and reciprocal
point spectrum. -/
theorem XiC_eq_zero_iff_sourcePencil_not_isUnit_iff_eigenvector (z : ℂ) :
    XiC z = 0 ↔
      (¬ IsUnit (thetaSourcePencil z) ∧
        ∃ f : ThetaH, f ≠ 0 ∧ thetaKernelOperator f = (-z⁻¹) • f) := by
  by_cases hz : z = 0
  · subst z
    simp [thetaSourcePencil, XiC_zero_ne]
  · constructor
    · intro hXi
      have hdet : thetaSourceEntireDet2 z = 0 :=
        (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).2 hXi
      exact ⟨(thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).2 hXi,
        (thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector hz).1 hdet⟩
    · exact fun h ↦ (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).1 h.1

/-! ## Nonzero spectrum and the reflection pairing -/

/-- The nonzero spectrum of the source inverse is exactly the reciprocal centered Xi divisor. -/
theorem thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero {mu : ℂ} (hmu : mu ≠ 0) :
    mu ∈ spectrum ℂ thetaKernelOperator ↔
      ∃ z : ℂ, XiC z = 0 ∧ mu = -z⁻¹ := by
  constructor
  · intro hspec
    have heigen : HasEigenvalue
        (thetaKernelOperator : Module.End ℂ ThetaH) mu :=
      (isCompactOperator_thetaKernelOperator.hasEigenvalue_iff_mem_spectrum hmu).2 hspec
    obtain ⟨f, hf⟩ := heigen.exists_hasUnifEigenvector
    refine ⟨-mu⁻¹, ?_, ?_⟩
    · have hf' : thetaCompactSourceInverse f = mu • f := by
        rw [← thetaKernelOperator_eq_thetaCompactSourceInverse]
        exact hf.apply_eq_smul
      apply XiC_eq_zero_of_thetaCompactSourceInverse_eigen
        (neg_ne_zero.mpr (inv_ne_zero hmu)) hf.2
      simpa only [inv_neg, inv_inv, neg_neg] using hf'
    · simp [hmu]
  · rintro ⟨z, hXi, rfl⟩
    have hz : z ≠ 0 := fun hz ↦ XiC_zero_ne (hz ▸ hXi)
    have hdet : thetaSourceEntireDet2 z = 0 :=
      (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).2 hXi
    obtain ⟨f, hf0, hf⟩ :=
      (thetaSourceEntireDet2_eq_zero_iff_exists_eigenvector hz).1 hdet
    apply (isCompactOperator_thetaKernelOperator.hasEigenvalue_iff_mem_spectrum
      (neg_ne_zero.mpr (inv_ne_zero hz))).1
    exact (show HasEigenvector
      (thetaKernelOperator : Module.End ℂ ThetaH) (-z⁻¹) f from
        ⟨mem_eigenspace_iff.mpr hf, hf0⟩).hasUnifEigenvalue

/-- Reflection pairs every nonzero spectral point under `mu ↦ -mu`. -/
theorem neg_mem_spectrum_thetaKernelOperator {mu : ℂ}
    (hmu : mu ≠ 0) (hspec : mu ∈ spectrum ℂ thetaKernelOperator) :
    -mu ∈ spectrum ℂ thetaKernelOperator := by
  obtain ⟨z, hXi, hmuEq⟩ :=
    (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero hmu).1 hspec
  have hz : z ≠ 0 := fun hz ↦ XiC_zero_ne (hz ▸ hXi)
  apply (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero (neg_ne_zero.mpr hmu)).2
  refine ⟨-z, ?_, ?_⟩
  · simpa only [XiC_even] using hXi
  · rw [hmuEq]
    simp [hz]

/-- The entire source determinant is even, reflecting `RBR = -B`. -/
theorem thetaSourceEntireDet2_even (z : ℂ) :
    thetaSourceEntireDet2 (-z) = thetaSourceEntireDet2 z := by
  rw [thetaSourceEntireDet2_eq_XiC_normalized,
    thetaSourceEntireDet2_eq_XiC_normalized, XiC_even]

/-- Evenness preserves the determinant's local analytic order at paired points. -/
theorem analyticOrderAt_thetaSourceEntireDet2_neg (z : ℂ) :
    analyticOrderAt thetaSourceEntireDet2 (-z) =
      analyticOrderAt thetaSourceEntireDet2 z := by
  let negMap : ℂ → ℂ := fun w ↦ -w
  have hcomp : analyticOrderAt (thetaSourceEntireDet2 ∘ negMap) z =
      analyticOrderAt thetaSourceEntireDet2 (-z) := by
    apply analyticOrderAt_comp_of_deriv_ne_zero
    · fun_prop
    · simp [negMap]
  calc
    analyticOrderAt thetaSourceEntireDet2 (-z) =
        analyticOrderAt (thetaSourceEntireDet2 ∘ negMap) z := hcomp.symm
    _ = analyticOrderAt thetaSourceEntireDet2 z :=
      analyticOrderAt_congr (Filter.Eventually.of_forall fun w ↦ thetaSourceEntireDet2_even w)

/-- Reflection preserves the algebraic multiplicity of every nonzero spectral point. -/
theorem finrank_maxGenEigenspace_thetaKernelOperator_neg_eq
    {mu : ℂ} (hmu : mu ≠ 0) (hspec : mu ∈ spectrum ℂ thetaKernelOperator) :
    Module.finrank ℂ (maxGenEigenspace
      (thetaKernelOperator : Module.End ℂ ThetaH) (-mu)) =
    Module.finrank ℂ (maxGenEigenspace
      (thetaKernelOperator : Module.End ℂ ThetaH) mu) := by
  let z : ℂ := -mu⁻¹
  obtain ⟨w, hXi, hw⟩ :=
    (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero hmu).1 hspec
  have hzEq : z = w := by
    dsimp only [z]
    rw [hw]
    simp [inv_neg]
  have hzXi : XiC z = 0 := hzEq ▸ hXi
  have hnegXi : XiC (-z) = 0 := by simpa only [XiC_even] using hzXi
  have hdet : thetaSourceEntireDet2 z = 0 :=
    (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).2 hzXi
  have hdetNeg : thetaSourceEntireDet2 (-z) = 0 :=
    (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero (-z)).2 hnegXi
  have horder := analyticOrderAt_thetaSourceEntireDet2_neg z
  rw [analyticOrderAt_thetaSourceEntireDet2_eq_algebraicMultiplicity hdetNeg,
    analyticOrderAt_thetaSourceEntireDet2_eq_algebraicMultiplicity hdet] at horder
  have hleft : -(-z)⁻¹ = -mu := by
    dsimp only [z]
    simp only [neg_neg, inv_inv]
  have hright : -z⁻¹ = mu := by
    dsimp only [z]
    rw [inv_neg, inv_inv]
    simp
  rw [hleft, hright] at horder
  exact_mod_cast horder

/-! ## Terminal RH criterion -/

/-- Every nonzero source spectral point is real exactly when RH holds. -/
theorem riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real :
    RiemannHypothesis ↔
      ∀ mu : ℂ, mu ∈ spectrum ℂ thetaKernelOperator → mu ≠ 0 →
        ∃ t : ℝ, mu = (t : ℂ) := by
  constructor
  · intro hRH mu hspec hmu
    obtain ⟨z, hXi, hmuEq⟩ :=
      (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero hmu).1 hspec
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).1 hXi
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have hz : z = (t : ℂ) := hq.symm.trans ht
    refine ⟨-t⁻¹, ?_⟩
    rw [hmuEq, hz]
    simp
  · intro hreal
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    let z : ℂ := xiSpectralPoint q
    have hzXi : XiC z = 0 := XiC_xiSpectralPoint_eq_zero q
    have hz : z ≠ 0 := xiSpectralPoint_ne_zero q
    let mu : ℂ := -z⁻¹
    have hmu : mu ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hz)
    have hspec : mu ∈ spectrum ℂ thetaKernelOperator :=
      (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero hmu).2 ⟨z, hzXi, rfl⟩
    obtain ⟨t, ht⟩ := hreal mu hspec hmu
    refine ⟨-t⁻¹, ?_⟩
    change z = ((-t⁻¹ : ℝ) : ℂ)
    have hzmu : z = -mu⁻¹ := by simp [mu, hz]
    rw [hzmu, ht]
    simp

/-- Set-theoretic spelling of the terminal criterion in the card. -/
theorem riemannHypothesis_iff_thetaKernelOperator_spectrum_diff_zero_subset_real :
    RiemannHypothesis ↔
      spectrum ℂ thetaKernelOperator \ {0} ⊆
        Set.range (fun t : ℝ ↦ (t : ℂ)) := by
  rw [riemannHypothesis_iff_thetaKernelOperator_nonzero_spectrum_real]
  constructor
  · intro h mu hmu
    obtain ⟨t, ht⟩ := h mu hmu.1 hmu.2
    exact ⟨t, ht.symm⟩
  · intro h mu hspec hmu
    obtain ⟨t, ht⟩ := h ⟨hspec, hmu⟩
    exact ⟨t, ht.symm⟩

end

end RHTower.HedenmalmThetaSource
