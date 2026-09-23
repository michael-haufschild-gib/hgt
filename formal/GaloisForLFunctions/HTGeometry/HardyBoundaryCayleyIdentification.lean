import GaloisForLFunctions.HTGeometry.CayleyBoundaryL2
import GaloisForLFunctions.HTGeometry.DiskMultiplierBoundary
import GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph
import GaloisForLFunctions.HTGeometry.LpSingleExtension

/-!
# Identification of concrete and abstract Hardy Cayley transports

The coefficient Hardy boundary followed by the explicit circle-to-line half-density agrees with
the project's feature-Gram Cayley unitary, up to the unavoidable global phase `i`.  The proof first
computes both maps on every coordinate monomial and then uses density of coordinate singles.
-/

open MeasureTheory Complex Filter
open scoped ENNReal NNReal lp InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem hardyDiskBoundary_single (n : ℕ) :
    hardyDiskBoundary (lp.single 2 n (1 : ℂ) : HardyDisk) =
      circleMonomialLp circleLebesgue n := by
  rw [hardyDiskBoundary_apply]
  have hsum := hasSum_circleMonomial_smul_circleRieszFischerOfNat
    (lp.single 2 n (1 : ℂ) : HardyDisk)
    (lp.memℓp (lp.single 2 n (1 : ℂ) : HardyDisk))
  rw [← hsum.tsum_eq]
  rw [tsum_eq_single n]
  · simp [lp.single_apply]
  · intro b hb
    simp [lp.single_apply, hb]

theorem circleLineCayleyIsometry_circleMonomial (n : ℕ) :
    circleLineCayleyIsometry (circleMonomialLp circleLebesgue n) =
      (Real.sqrt Real.pi : ℂ)⁻¹ •
        ((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
          RealLineL2)) := by
  apply Lp.ext
  have hmonWeighted := (circleMonomialLp_coeFn_ae circleLebesgue n).comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hmon :
      (fun x => circleMonomialLp circleLebesgue n (circleCayley x)) =ᵐ[volume]
        fun x => (circleCayley x : ℂ) ^ n :=
    (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
      standardCauchyWeight_pos).mp hmonWeighted
  filter_upwards [
    circleLineCayleyIsometry_ae_explicit
      (circleMonomialLp circleLebesgue n),
    hmon,
    coe_cayleyHardyShift_pow n,
    Lp.coeFn_smul (Real.sqrt Real.pi : ℂ)⁻¹
      ((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
        RealLineL2))] with x hleft hmonx hshift hsmul
  rw [hleft, hmonx, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hshift, circleCayley_coe]
  ring

/-- Upper-half-plane point corresponding to the disk origin. -/
def cayleyIPoint : UpperHalfPlanePoint := ⟨I, by simp⟩

theorem upperToDiskCayley_I : upperToDiskCayley I = 0 := by
  simp [upperToDiskCayley]

theorem hardyKernel_zero_eq_hardyOne :
    hardyKernel (a := (0 : ℂ)) (by norm_num) = hardyOne := by
  apply lp.ext
  funext n
  cases n with
  | zero => simp [hardyKernel, hardyKernelCoeff, hardyOne, lp.single_apply]
  | succ n => simp [hardyKernel, hardyKernelCoeff, hardyOne, lp.single_apply]

theorem cayleyLineFeatureScale_I :
    cayleyLineFeatureScale cayleyIPoint =
      -I * (Real.sqrt Real.pi : ℂ)⁻¹ := by
  have hsqrt : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  simp only [cayleyLineFeatureScale, cayleyIPoint, Complex.conj_I]
  field_simp [hsqrt]
  push_cast
  ring

theorem hardyDiskLineCayleyUnitary_hardyOne :
    hardyDiskLineCayleyUnitary hardyOne =
      (-I * (Real.sqrt Real.pi : ℂ)⁻¹) • cayleyBaseFeature := by
  have h := hardyDiskLineCayleyUnitary_apply_feature cayleyIPoint
  have hleft : cayleyDiskHardyFeature cayleyIPoint = hardyOne := by
    apply lp.ext
    funext n
    cases n with
    | zero =>
        simp [cayleyDiskHardyFeature, cayleyIPoint,
          hardyKernel, hardyKernelCoeff, hardyOne, lp.single_apply]
    | succ n =>
        simp [cayleyDiskHardyFeature, cayleyIPoint,
          hardyKernel, hardyKernelCoeff, hardyOne, lp.single_apply]
  rw [hleft] at h
  change hardyDiskLineCayleyUnitary hardyOne =
      cayleyLineFeatureScale cayleyIPoint • cayleyBaseFeature at h
  rw [cayleyLineFeatureScale_I] at h
  exact h

theorem normalizedCayleyBlaschkeUnit_I :
    normalizedCayleyBlaschkeUnit I = 1 := by
  simp [normalizedCayleyBlaschkeUnit, normalizedBlaschkePhase_upperHalfPlaneNormalizedBlaschkeCayley,
    cayleyBlaschkeUnit, upperToDiskCayley]
  have htwoI : I + I ≠ (0 : ℂ) := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  have hratio : (-I - I) / (I + I) = (-1 : ℂ) := by
    apply (div_eq_iff htwoI).2
    ring
  rw [hratio]
  simp

theorem cayleyNormalizedBlaschkeMultiplier_I_fn (z : ℂ) :
    (cayleyNormalizedBlaschkeMultiplier cayleyIPoint).fn z = z := by
  simp [cayleyNormalizedBlaschkeMultiplier, cayleyIPoint,
    normalizedBlaschkeMultiplier, normalizedBlaschkeFactor, upperToDiskCayley]

theorem hardyDiskLineCayleyUnitary_shift (f : HardyDisk) :
    hardyDiskLineCayleyUnitary (hardyMul diskShift f) =
      cayleyHardyShift (hardyDiskLineCayleyUnitary f) := by
  let F := cayleyNormalizedBlaschkeMultiplier cayleyIPoint
  have hmul : hardyMul F f = hardyMul diskShift f := by
    exact hardyMul_congr (fun z _ => cayleyNormalizedBlaschkeMultiplier_I_fn z) f
  have htransport := cayleyTransport_normalizedBlaschkeMultiplier_eq cayleyIPoint
  have happly := cayleyTransportHardyMultiplier_apply F f
  change cayleyTransportHardyMultiplier F (hardyDiskLineCayleyUnitary f) =
      hardyDiskLineCayleyUnitary (hardyMul F f) at happly
  rw [htransport] at happly
  change normalizedCayleyBlaschkeUnit I •
      cayleyHardyShift (hardyDiskLineCayleyUnitary f) =
        hardyDiskLineCayleyUnitary (hardyMul F f) at happly
  rw [normalizedCayleyBlaschkeUnit_I, one_smul, hmul] at happly
  exact happly.symm

theorem hardyDiskLineCayleyUnitary_single (n : ℕ) :
    hardyDiskLineCayleyUnitary
        (lp.single 2 n (1 : ℂ) : HardyDisk) =
      (-I * (Real.sqrt Real.pi : ℂ)⁻¹) •
        ((cayleyHardyShift ^ n) cayleyBaseFeature) := by
  rw [← shift_pow_hardyOne]
  induction n with
  | zero => simpa using hardyDiskLineCayleyUnitary_hardyOne
  | succ n ih =>
      rw [pow_succ']
      change hardyDiskLineCayleyUnitary
          (hardyMul diskShift (((hardyMul diskShift) ^ n) hardyOne)) = _
      rw [hardyDiskLineCayleyUnitary_shift, ih]
      simp only [map_smul]
      rw [pow_succ']
      change (-I * (Real.sqrt Real.pi : ℂ)⁻¹) •
          cayleyHardyShift ((cayleyHardyShift ^ n) cayleyBaseFeature) =
        (-I * (Real.sqrt Real.pi : ℂ)⁻¹) •
          cayleyHardyShift ((cayleyHardyShift ^ n) cayleyBaseFeature)
      rfl

def explicitHardyBoundaryCayleyCLM : HardyDisk →L[ℂ] RealLineL2 :=
  circleLineCayleyIsometry.toContinuousLinearMap.comp
    hardyDiskBoundary.toContinuousLinearMap

def abstractHardyBoundaryCayleyCLM : HardyDisk →L[ℂ] RealLineL2 :=
  I • (UpperHardyL2.subtypeL.comp hardyDiskLineCayleyCLM)

theorem explicitHardyBoundaryCayleyCLM_eq_abstract :
    explicitHardyBoundaryCayleyCLM = abstractHardyBoundaryCayleyCLM := by
  apply ext_of_eq_on_single (p := (2 : ℝ≥0∞)) (by norm_num)
  intro n c
  rw [show (lp.single 2 n c : HardyDisk) =
      c • (lp.single 2 n (1 : ℂ) : HardyDisk) by
    apply lp.ext
    funext k
    simp [lp.single_apply, Pi.single_apply]]
  simp only [map_smul]
  congr 1
  change circleLineCayleyIsometry
      (hardyDiskBoundary (lp.single 2 n (1 : ℂ) : HardyDisk)) =
    I • ((((hardyDiskLineCayleyUnitary
      (lp.single 2 n (1 : ℂ) : HardyDisk)) : UpperHardyL2) : RealLineL2))
  rw [hardyDiskBoundary_single, circleLineCayleyIsometry_circleMonomial,
    hardyDiskLineCayleyUnitary_single]
  change (Real.sqrt Real.pi : ℂ)⁻¹ •
      ((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
        RealLineL2)) =
    I • ((-I * (Real.sqrt Real.pi : ℂ)⁻¹) •
      ((((cayleyHardyShift ^ n) cayleyBaseFeature : UpperHardyL2) :
        RealLineL2)))
  rw [smul_smul]
  rw [show I * (-I * (Real.sqrt Real.pi : ℂ)⁻¹) =
      (Real.sqrt Real.pi : ℂ)⁻¹ by
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]]

/-- The explicit boundary Cayley transform is the abstract Hardy unitary with global phase `i`. -/
theorem circleLineCayleyIsometry_hardyDiskBoundary (f : HardyDisk) :
    circleLineCayleyIsometry (hardyDiskBoundary f) =
      I • ((hardyDiskLineCayleyUnitary f : UpperHardyL2) : RealLineL2) := by
  have h := congrArg (fun T : HardyDisk →L[ℂ] RealLineL2 => T f)
    explicitHardyBoundaryCayleyCLM_eq_abstract
  change circleLineCayleyIsometry (hardyDiskBoundary f) =
      I • ((hardyDiskLineCayleyUnitary f : UpperHardyL2) : RealLineL2) at h
  exact h

end
end GaloisForLFunctions.HTGeometry
