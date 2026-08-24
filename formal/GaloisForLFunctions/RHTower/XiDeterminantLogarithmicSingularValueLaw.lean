import GaloisForLFunctions.HTGeometry.SelfAdjointGeneralizedEigenspace
import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect

/-!
# Exact Xi determinants: divisor and self-adjoint spectral laws

This leaf begins the exact infinite-dimensional bridge required by the
`xi-determinant-logarithmic-singular-value-law` card.  It proves, without an added spectral
realization hypothesis, that a nowhere-vanishing entire gauge times a Hilbert--Carleman
determinant of a self-adjoint Hilbert--Schmidt kernel forces RH and transports every Xi
multiplicity to the ordinary reciprocal eigenspace of the carrier.
-/

open Complex Set
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- Exact zero-free-gauge `det₂` identity plus self-adjointness forces every centered Xi zero to
be real, hence proves RH. -/
theorem riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  intro z hz
  have hdet : GaloisForLFunctions.HTGeometry.entireDet2 K z = 0 := by
    have : H z * GaloisForLFunctions.HTGeometry.entireDet2 K z = 0 := by
      simpa [hXi z] using hz
    exact (mul_eq_zero.mp this).resolve_left (hH z)
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hone :=
      (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2 hK).eq_one_at_zero
    rw [hdet] at hone
    exact zero_ne_one hone
  obtain ⟨w, hw0, hw⟩ :=
    (GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
      hK hz0).mp hdet
  have heig : Module.End.HasEigenvalue
      (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2) z⁻¹ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hw, hw0⟩
  have hsymm : (toOperator hK :
      lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  have hreal := hsymm.conj_eigenvalue_eq_self heig
  change star z⁻¹ = z⁻¹ at hreal
  have him := congrArg Complex.im hreal
  simp at him
  have hnorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  have hnorm0 : Complex.normSq z ≠ 0 := ne_of_gt hnorm
  field_simp [hnorm0] at him
  linarith

/-- A zero-free entire gauge changes neither the Xi divisor nor its multiplicities: the analytic
order at every Xi zero is the full algebraic multiplicity of the reciprocal carrier spectrum. -/
theorem analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_of_exactDeterminant
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {z : ℂ} (hz : XiC z = 0) :
    analyticOrderAt XiC z =
      (Module.finrank ℂ (Module.End.maxGenEigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ]
          lp (fun _ : ι => ℂ) 2) z⁻¹) : ℕ∞) := by
  have hdet : GaloisForLFunctions.HTGeometry.entireDet2 K z = 0 := by
    have hzero : H z * GaloisForLFunctions.HTGeometry.entireDet2 K z = 0 := by
      simpa [hXi z] using hz
    exact (mul_eq_zero.mp hzero).resolve_left (hH z)
  calc
    analyticOrderAt XiC z =
        analyticOrderAt
          (GaloisForLFunctions.HTGeometry.entireDet2 K) z := by
      apply analyticOrderAt_eq_of_factor_ne_zero
      · exact (hHanalytic.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
      · exact
          ((GaloisForLFunctions.HTGeometry.differentiable_entireDet2 hK).differentiableOn.analyticOnNhd
            isOpen_univ) z (mem_univ z)
      · exact hXi
      · exact hH z
    _ = _ :=
      GaloisForLFunctions.HTGeometry.analyticOrderAt_entireDet2_eq_finrank_maxGenEigenspace
        hK hdet

/-- Under self-adjointness, the determinant multiplicity is geometric: symmetric operators have no
nontrivial Jordan chains at their necessarily real reciprocal Xi eigenvalues. -/
theorem analyticOrderAt_XiC_eq_finrank_eigenspace_of_exactSelfAdjointDeterminant
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {z : ℂ} (hz : XiC z = 0) :
    analyticOrderAt XiC z =
      (Module.finrank ℂ (Module.End.eigenspace
        (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ]
          lp (fun _ : ι => ℂ) 2) z⁻¹) : ℕ∞) := by
  have hRH := riemannHypothesis_of_XiC_eq_zeroFree_mul_entireDet2
    hK hself H hH hXi
  have hzreal : z.im = 0 :=
    (riemannHypothesis_iff_XiC_zeros_real.mp hRH) z hz
  have hzinv : star z⁻¹ = z⁻¹ := by
    apply Complex.ext
    · simp
    · simp [Complex.inv_im, hzreal]
  rw [← GaloisForLFunctions.HTGeometry.maxGenEigenspace_eq_eigenspace_of_isSymmetric
    (toOperator hK : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself) z⁻¹ hzinv]
  exact analyticOrderAt_XiC_eq_finrank_maxGenEigenspace_of_exactDeterminant
    hK H hHanalytic hH hXi hz

end

end RHTower
