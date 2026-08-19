import GaloisForLFunctions.RHTower.SuzukiTaCharacteristicRealization

/-!
# Suzuki v2 characteristic zeros as a self-adjoint spectrum

This file completes the operator-theoretic content of Suzuki v2, Theorem 1.5 on the literal
energy space `H(T_a)`.  The characteristic function is the exact Fourier--Laplace boundary
determinant of the two normalized deficiency vectors.  Its zero vector is admitted to the
von Neumann extension by the Green boundary form, hence is a nonzero eigenvector.  Self-adjoint
symmetry then forces every characteristic zero onto the real axis.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- Suzuki's finite-aperture characteristic function, written directly in the energy-space
Fourier--Laplace coordinates of the normalized deficiency vectors. -/
def suzukiTaCharacteristic
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ) : ℂ :=
  (z - I) * suzukiTaSpectralMoment a (star z) (suzukiTaPlusDeficiency a) +
    suzukiTaBoundaryPhase theta * (z + I) *
      suzukiTaSpectralMoment a (star z) (suzukiTaMinusDeficiency a)

/-- The displayed Suzuki determinant is exactly the Green boundary pairing of the canonical
spectral vector with the extension's boundary generator. -/
theorem suzukiTaCharacteristic_eq_boundaryPairing
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ) :
    suzukiTaCharacteristic a theta z =
      LinearPMap.adjointBoundaryPairing (suzukiTaMinimalDerivative a)
        (suzukiTaSpectralVectorDomain a (star z))
        (suzukiTaBoundaryVectorDomain a theta) := by
  rw [suzukiTaCharacteristic, LinearPMap.adjointBoundaryPairing,
    suzukiTa_adjoint_spectralVector, suzukiTa_adjoint_boundaryVector]
  change
    (z - I) * suzukiTaSpectralMoment a (star z) (suzukiTaPlusDeficiency a) +
        suzukiTaBoundaryPhase theta * (z + I) *
          suzukiTaSpectralMoment a (star z) (suzukiTaMinusDeficiency a) =
      inner ℂ ((star z) • suzukiTaSpectralVector a (star z))
          (suzukiTaPlusDeficiency a +
            suzukiTaBoundaryPhase theta • suzukiTaMinusDeficiency a) -
        inner ℂ (suzukiTaSpectralVector a (star z))
          (I • suzukiTaPlusDeficiency a -
            I • (suzukiTaBoundaryPhase theta • suzukiTaMinusDeficiency a))
  rw [inner_smul_left, inner_add_right, inner_smul_right,
    inner_sub_right, inner_smul_right, inner_smul_right]
  simp only [suzukiTaSpectralVector_inner, map_smul,
    starRingEnd_apply, star_star]
  ring

/-- A characteristic zero supplies the canonical nonzero vector in the self-adjoint extension
domain. -/
theorem suzukiTaSpectralVector_mem_extension_of_characteristic_eq_zero
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ)
    (hz : suzukiTaCharacteristic a theta z = 0) :
    suzukiTaSpectralVector a (star z) ∈
      (suzukiTaSelfAdjointExtension a theta).domain := by
  apply LinearPMap.mem_deficiencyExtensionDomain_of_boundary_zero
    (dense_suzukiTaShiftedDerivativePMap_domain a 0)
    (suzukiTaMinimalDerivative_symmetric a)
    (suzukiTaPlusDeficiencyDomain a) (suzukiTaMinusDeficiencyDomain a)
    (suzukiTaBoundaryPhase theta)
    (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta)
    (suzukiTaSpectralVectorDomain a (star z))
  change LinearPMap.adjointBoundaryPairing (suzukiTaMinimalDerivative a)
      (suzukiTaSpectralVectorDomain a (star z))
      (suzukiTaBoundaryVectorDomain a theta) = 0
  rw [← suzukiTaCharacteristic_eq_boundaryPairing]
  exact hz

def suzukiTaCharacteristicEigenvector
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ)
    (hz : suzukiTaCharacteristic a theta z = 0) :
    (suzukiTaSelfAdjointExtension a theta).domain :=
  ⟨suzukiTaSpectralVector a (star z),
    suzukiTaSpectralVector_mem_extension_of_characteristic_eq_zero a theta z hz⟩

theorem suzukiTaCharacteristicEigenvector_ne_zero
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ)
    (hz : suzukiTaCharacteristic a theta z = 0) :
    ((suzukiTaCharacteristicEigenvector a theta z hz :
      (suzukiTaSelfAdjointExtension a theta).domain) : SuzukiTaHilbert a) ≠ 0 :=
  suzukiTaSpectralVector_ne_zero a (star z)

/-- Exact eigenvalue equation behind Suzuki v2, Theorem 1.5. -/
theorem suzukiTa_characteristicZero_is_eigenvalue
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ)
    (hz : suzukiTaCharacteristic a theta z = 0) :
    suzukiTaSelfAdjointExtension a theta
        (suzukiTaCharacteristicEigenvector a theta z hz) =
      (star z) • suzukiTaSpectralVector a (star z) := by
  calc
    suzukiTaSelfAdjointExtension a theta
        (suzukiTaCharacteristicEigenvector a theta z hz) =
      (suzukiTaMinimalDerivative a).adjoint
        ⟨suzukiTaSpectralVector a (star z),
          LinearPMap.deficiencyExtensionDomain_le_adjoint
            (dense_suzukiTaShiftedDerivativePMap_domain a 0)
            (suzukiTaMinimalDerivative_symmetric a)
            (suzukiTaPlusDeficiencyDomain a) (suzukiTaMinusDeficiencyDomain a)
            (suzukiTaBoundaryPhase theta)
            (suzukiTaSpectralVector_mem_extension_of_characteristic_eq_zero
              a theta z hz)⟩ := by
        exact LinearPMap.deficiencyExtension_apply
          (dense_suzukiTaShiftedDerivativePMap_domain a 0)
          (suzukiTaMinimalDerivative_symmetric a)
          (suzukiTaPlusDeficiencyDomain a) (suzukiTaMinusDeficiencyDomain a)
          (suzukiTaBoundaryPhase theta)
          (suzukiTaCharacteristicEigenvector a theta z hz)
    _ = (star z) • suzukiTaSpectralVector a (star z) := by
      convert suzukiTa_adjoint_spectralVector a (star z)
      rfl

/-- A nonzero eigenvalue of a symmetric complex Hilbert-space operator is real. -/
theorem eigenvalue_im_eq_zero_of_isFormalAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {A : H →ₗ.[ℂ] H} (hSymm : A.IsFormalAdjoint A)
    (x : A.domain) (lambda : ℂ) (hx0 : (x : H) ≠ 0)
    (hx : A x = lambda • (x : H)) : lambda.im = 0 := by
  have hpair := hSymm x x
  rw [hx, inner_smul_left, inner_smul_right] at hpair
  have hinner : inner ℂ (x : H) (x : H) ≠ 0 := inner_self_ne_zero.mpr hx0
  have hstar : star lambda = lambda := by
    apply mul_right_cancel₀ hinner
    exact hpair
  have hre := congrArg Complex.im hstar
  change -lambda.im = lambda.im at hre
  linarith

/-- Every zero of Suzuki's finite-aperture characteristic function is real. -/
theorem suzukiTaCharacteristic_zero_im_eq_zero
    (a : SuzukiPositiveAperture) (theta : ℝ) (z : ℂ)
    (hz : suzukiTaCharacteristic a theta z = 0) : z.im = 0 := by
  let x := suzukiTaCharacteristicEigenvector a theta z hz
  have hDenseExtension : Dense
      ((suzukiTaSelfAdjointExtension a theta).domain : Set (SuzukiTaHilbert a)) := by
    exact (dense_suzukiTaShiftedDerivativePMap_domain a 0).mono
      (LinearPMap.le_deficiencyExtension
        (dense_suzukiTaShiftedDerivativePMap_domain a 0)
        (suzukiTaMinimalDerivative_symmetric a)
        (suzukiTaPlusDeficiencyDomain a) (suzukiTaMinusDeficiencyDomain a)
        (suzukiTaBoundaryPhase theta)).1
  have hSymmExtension :
      (suzukiTaSelfAdjointExtension a theta).IsFormalAdjoint
        (suzukiTaSelfAdjointExtension a theta) := by
    have hformal := LinearPMap.adjoint_isFormalAdjoint hDenseExtension
    have hEq : (suzukiTaSelfAdjointExtension a theta).adjoint =
        suzukiTaSelfAdjointExtension a theta :=
      LinearPMap.isSelfAdjoint_def.mp
        (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta)
    nth_rewrite 1 [← hEq]
    exact hformal
  have him : (star z).im = 0 :=
    eigenvalue_im_eq_zero_of_isFormalAdjoint
      hSymmExtension
      x (star z)
      (suzukiTaCharacteristicEigenvector_ne_zero a theta z hz)
      (suzukiTa_characteristicZero_is_eigenvalue a theta z hz)
  simpa using him

end RHTower
