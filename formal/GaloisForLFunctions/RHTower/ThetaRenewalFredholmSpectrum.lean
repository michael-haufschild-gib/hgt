import GaloisForLFunctions.RHTower.ThetaRenewalPositiveFredholm
import GaloisForLFunctions.HTGeometry.CoordinateDeterminantMultiplicity
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

/-!
# Actual renewal resonances as compact-operator eigenvalues

Every zero, with its exact algebraic multiplicity, belongs to the explicit
theta-source operator. No source admission or spectral realization premise
is supplied by the caller.
-/

noncomputable section
open Complex ContinuousLinearMap HilbertSchmidt
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem thetaRenewalFredholm_entire
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2) (z : ℂ) :
    det2Op b (z • thetaRenewalFredholmOperator) =
      entireDet2 (coordMatrix b thetaRenewalFredholmOperator) (-z) := by
  rw [det2Op, coordMatrix_smul,
    entireDet2_smul (isHS_coordMatrix b thetaRenewalFredholmOperator_isHilbertSchmidt)]
  simp

theorem thetaRenewalDenominator_eq_zero_iff_scaled_eigenvector
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2) (z : ℂ) :
    thetaRenewalDenominator z = 0 ↔
      ∃ v : ThetaRenewalL2, v ≠ 0 ∧ (z • thetaRenewalFredholmOperator) v = -v := by
  have he : det2Op b (z • thetaRenewalFredholmOperator) = 0 ↔
      thetaRenewalDenominator z = 0 := by
    rw [thetaRenewalFredholm_det2]
    simp [thetaRenewalDenominator_zero_ne, Complex.exp_ne_zero]
  exact he.symm.trans (det2Op_eq_zero_iff b
    (thetaRenewalFredholmOperator_isHilbertSchmidt.smul z))

theorem thetaRenewalDenominator_eq_zero_iff_eigenvector
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2)
    {z : ℂ} (hz : z ≠ 0) :
    thetaRenewalDenominator z = 0 ↔
      ∃ v : ThetaRenewalL2, v ≠ 0 ∧ thetaRenewalFredholmOperator v = -z⁻¹ • v := by
  rw [thetaRenewalDenominator_eq_zero_iff_scaled_eigenvector b]
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, ?_⟩
    have h := congrArg (fun u : ThetaRenewalL2 => z⁻¹ • u) hv
    simpa [smul_smul, hz] using h
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, ?_⟩
    simp [hv, smul_smul, hz]

/-- Exact multiplicity on the original L² space, with finite-dimensionality proved. -/
theorem thetaRenewalFredholm_algebraicMultiplicity
    {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ ThetaRenewalL2)
    {z : ℂ} (hz : thetaRenewalDenominator z = 0) :
    (analyticOrderAt thetaRenewalDenominator z =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (thetaRenewalFredholmOperator : ThetaRenewalL2 →ₗ[ℂ] ThetaRenewalL2) (-z⁻¹)) : ℕ∞)) ∧
    FiniteDimensional ℂ (Module.End.maxGenEigenspace
      (thetaRenewalFredholmOperator : ThetaRenewalL2 →ₗ[ℂ] ThetaRenewalL2) (-z⁻¹)) := by
  let M := coordMatrix b thetaRenewalFredholmOperator
  have hM : IsHS M := isHS_coordMatrix b thetaRenewalFredholmOperator_isHilbertSchmidt
  have hzero : entireDet2 M (-z) = 0 := by
    rw [← thetaRenewalFredholm_entire b z, thetaRenewalFredholm_det2, hz]
    simp
  have hm := analyticOrderAt_coordMatrix_eq_finrank_and_finite b
    thetaRenewalFredholmOperator_isHilbertSchmidt hzero
  have ha : AnalyticAt ℂ (entireDet2 M) (-z) :=
    (differentiable_entireDet2 hM).analyticAt (-z)
  have ha' : AnalyticAt ℂ (fun w => entireDet2 M (-w)) z := by
    simpa using (analyticAt_comp_affine (μ := -1) (ν := 0) (z := z)
      (by simpa using ha))
  have ho := analyticOrderAt_comp_affine (μ := -1) (ν := 0) (z := z)
    (by norm_num : (-1 : ℂ) ≠ 0) (by simpa using ha) (by simpa using hm.1)
  have he : thetaRenewalDenominator = fun w =>
      (thetaRenewalDenominator 0 * Complex.exp ((thetaRenewalDrift : ℂ) * w)) *
        entireDet2 M (-w) := by
    funext w
    rw [thetaRenewalDenominator_eq_fredholm b w, thetaRenewalFredholm_entire]
  have hp : AnalyticAt ℂ
      (fun w => thetaRenewalDenominator 0 * Complex.exp ((thetaRenewalDrift : ℂ) * w)) z := by
    fun_prop
  have hpnz : thetaRenewalDenominator 0 * Complex.exp ((thetaRenewalDrift : ℂ) * z) ≠ 0 :=
    mul_ne_zero thetaRenewalDenominator_zero_ne (Complex.exp_ne_zero _)
  have hprod : analyticOrderAt (fun w =>
      (thetaRenewalDenominator 0 * Complex.exp ((thetaRenewalDrift : ℂ) * w)) *
        entireDet2 M (-w)) z = analyticOrderAt (fun w => entireDet2 M (-w)) z := by
    have h := analyticOrderAt_mul hp ha'
    rw [hp.analyticOrderAt_eq_zero.mpr hpnz, zero_add] at h
    simpa only using! h
  have hinv : (-z)⁻¹ = -z⁻¹ := _root_.inv_neg
  rw [hinv] at hm ho
  constructor
  · rw [he, hprod]
    simpa only [neg_one_mul, add_zero] using! ho
  · exact hm.2

end RHTower
