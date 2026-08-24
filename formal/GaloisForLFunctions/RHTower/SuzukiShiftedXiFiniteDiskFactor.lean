import GaloisForLFunctions.HTGeometry.UpperHalfPlaneFiniteBlaschkeCayley
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteBlaschke
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteTailProduct
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Cayley image of one finite-tail numerator zero. -/
def xiShiftNumeratorDiskCoordinate (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) : ℂ :=
  upperToDiskCayley (xiShiftNumeratorCoordinate omega q)

theorem norm_xiShiftNumeratorDiskCoordinate_lt_one
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    ‖xiShiftNumeratorDiskCoordinate omega q‖ < 1 := by
  exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk _
    (xiShiftNumeratorCoordinate_im_pos homega q)

/-- Finite Blaschke numerator obtained from all reflected shifted-tail zeros. -/
def xiShiftFiniteNumeratorBlaschke (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] : FiniteBlaschke :=
  finiteBlaschkeOfFiniteFamily
    (xiShiftNumeratorDiskCoordinate omega)
    (norm_xiShiftNumeratorDiskCoordinate_lt_one homega)

@[simp]
theorem xiShiftFiniteNumeratorBlaschke_deg
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    (xiShiftFiniteNumeratorBlaschke omega homega).deg =
      Fintype.card (XiShiftRightZeroCopy omega) := by
  exact finiteBlaschkeOfFiniteFamily_deg
    (xiShiftNumeratorDiskCoordinate omega)
    (norm_xiShiftNumeratorDiskCoordinate_lt_one homega)

theorem xiShiftFiniteNumeratorBlaschke_fn
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] (u : ℂ) :
    (xiShiftFiniteNumeratorBlaschke omega homega).fn u =
      ∏ q : XiShiftRightZeroCopy omega,
        blaschkeFactor (xiShiftNumeratorDiskCoordinate omega q) u := by
  exact finiteBlaschkeOfFiniteFamily_fn
    (xiShiftNumeratorDiskCoordinate omega)
    (norm_xiShiftNumeratorDiskCoordinate_lt_one homega) u

/-- Cayley normalization of the finite numerator product. -/
def xiShiftFiniteNumeratorCayleyUnit (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    cayleyBlaschkeUnit (xiShiftNumeratorCoordinate omega q)

/-- Cayley normalization of the finite pole product. -/
def xiShiftFinitePoleCayleyUnit (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    cayleyBlaschkeUnit (xiShiftPoleCoordinate omega q)

/-- Unimodular scale converting the half-plane finite quotient into its disk quotient. -/
def xiShiftFiniteCayleyUnit (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] : ℂ :=
  xiShiftFinitePoleCayleyUnit omega /
    xiShiftFiniteNumeratorCayleyUnit omega

theorem norm_xiShiftFiniteNumeratorCayleyUnit_eq_one
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    ‖xiShiftFiniteNumeratorCayleyUnit omega‖ = 1 := by
  exact norm_prod_cayleyBlaschkeUnit_eq_one
    (xiShiftNumeratorCoordinate omega)
    (xiShiftNumeratorCoordinate_im_pos homega)

theorem norm_xiShiftFinitePoleCayleyUnit_eq_one
    (omega : ℝ) [Fintype (XiShiftRightZeroCopy omega)] :
    ‖xiShiftFinitePoleCayleyUnit omega‖ = 1 := by
  exact norm_prod_cayleyBlaschkeUnit_eq_one
    (xiShiftPoleCoordinate omega)
    (xiShiftPoleCoordinate_im_pos omega)

theorem norm_xiShiftFiniteCayleyUnit_eq_one
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    ‖xiShiftFiniteCayleyUnit omega‖ = 1 := by
  rw [xiShiftFiniteCayleyUnit, norm_div,
    norm_xiShiftFinitePoleCayleyUnit_eq_one,
    norm_xiShiftFiniteNumeratorCayleyUnit_eq_one homega]
  norm_num

theorem xiShiftFiniteNumeratorBlaschke_cayley
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    {z : ℂ} (hz : 0 < z.im) :
    (xiShiftFiniteNumeratorBlaschke omega homega).fn
        (upperToDiskCayley z) =
      xiShiftFiniteNumeratorCayleyUnit omega *
        xiShiftFiniteNumeratorHalfPlaneBlaschke omega z := by
  rw [xiShiftFiniteNumeratorBlaschke_fn,
    xiShiftFiniteNumeratorCayleyUnit,
    xiShiftFiniteNumeratorHalfPlaneBlaschke,
    xiShiftFiniteNumeratorProduct,
    xiShiftFiniteConjNumeratorProduct]
  change (∏ q : XiShiftRightZeroCopy omega,
      blaschkeFactor
        (upperToDiskCayley (xiShiftNumeratorCoordinate omega q))
        (upperToDiskCayley z)) = _
  rw [prod_blaschkeFactor_upperToDiskCayley
    (xiShiftNumeratorCoordinate omega)
    (xiShiftNumeratorCoordinate_im_pos homega) hz]
  congr 1
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro q _
  rfl

theorem xiShiftFinitePoleBlaschke_cayley
    {omega : ℝ} [Fintype (XiShiftRightZeroCopy omega)]
    {z : ℂ} (hz : 0 < z.im) :
    (xiShiftFinitePoleBlaschke omega).fn (upperToDiskCayley z) =
      xiShiftFinitePoleCayleyUnit omega *
        xiShiftFinitePoleHalfPlaneBlaschke omega z := by
  rw [xiShiftFinitePoleBlaschke_fn,
    xiShiftFinitePoleCayleyUnit,
    xiShiftFinitePoleHalfPlaneBlaschke,
    xiShiftFinitePoleProduct,
    xiShiftFiniteConjPoleProduct]
  change (∏ q : XiShiftRightZeroCopy omega,
      blaschkeFactor
        (upperToDiskCayley (xiShiftPoleCoordinate omega q))
        (upperToDiskCayley z)) = _
  rw [prod_blaschkeFactor_upperToDiskCayley
    (xiShiftPoleCoordinate omega)
    (xiShiftPoleCoordinate_im_pos omega) hz]
  congr 1
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro q _
  rfl

/-- Finite transverse-tail quotient in disk generalized-Schur coordinates. -/
theorem xiShiftExtremeTheta_eq_finiteDiskBlaschke_div
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    {z : ℂ} (hz : 0 < z.im)
    (hext : xiShiftExtremeE omega z ≠ 0) :
    xiShiftExtremeTheta omega z =
      xiShiftFiniteCayleyUnit omega *
        ((xiShiftFiniteNumeratorBlaschke omega homega).fn
            (upperToDiskCayley z) /
          (xiShiftFinitePoleBlaschke omega).fn
            (upperToDiskCayley z)) := by
  have hnumUnit : xiShiftFiniteNumeratorCayleyUnit omega ≠ 0 :=
    norm_ne_zero_iff.mp (by
      rw [norm_xiShiftFiniteNumeratorCayleyUnit_eq_one homega]
      norm_num)
  have hpoleUnit : xiShiftFinitePoleCayleyUnit omega ≠ 0 :=
    norm_ne_zero_iff.mp (by
      rw [norm_xiShiftFinitePoleCayleyUnit_eq_one]
      norm_num)
  have hdenFactor :=
    xiShiftExtremeCanonicalProduct_denominator_shift_factorization
      omega homega z
  have hpoleMul : xiShiftFinitePoleProduct omega z ≠ 0 := by
    have hprod : xiShiftFinitePoleProduct omega z *
        xiShiftFiniteConjNumeratorProduct omega z ≠ 0 := by
      intro hzero
      apply hext
      rw [xiShiftExtremeE, hdenFactor]
      simpa only [mul_assoc, mul_zero] using
        congrArg (fun u => xiShiftFiniteTailScale omega * u) hzero
    exact (mul_ne_zero_iff.mp hprod).1
  have hconjPoleMul : xiShiftFiniteConjPoleProduct omega z ≠ 0 := by
    rw [xiShiftFiniteConjPoleProduct]
    apply Finset.prod_ne_zero_iff.mpr
    intro q _
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    have hp := xiShiftPoleCoordinate_im_pos omega q
    norm_num at him
    linarith
  have hpoleH : xiShiftFinitePoleHalfPlaneBlaschke omega z ≠ 0 := by
    rw [xiShiftFinitePoleHalfPlaneBlaschke]
    exact div_ne_zero hpoleMul hconjPoleMul
  rw [xiShiftExtremeTheta_eq_finiteHalfPlaneBlaschke_div homega hext,
    xiShiftFiniteNumeratorBlaschke_cayley homega hz,
    xiShiftFinitePoleBlaschke_cayley hz,
    xiShiftFiniteCayleyUnit]
  field_simp

/-- The shifted symmetric core is entire before division. -/
theorem differentiable_xiShiftCoreCanonicalProduct (omega : ℝ) :
    Differentiable ℂ (xiShiftCoreCanonicalProduct omega) := by
  intro z
  exact ((xiShiftCoreCanonicalProduct_analytic omega) z
    (Set.mem_univ z)).differentiableAt

theorem differentiableAt_xiShiftCoreE (omega : ℝ) (z : ℂ) :
    DifferentiableAt ℂ (xiShiftCoreE omega) z := by
  unfold xiShiftCoreE
  exact (differentiable_xiShiftCoreCanonicalProduct omega _).comp z
    ((differentiableAt_id.neg).sub_const _)

theorem differentiableAt_xiShiftCoreTheta
    {omega : ℝ} {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (xiShiftCoreTheta omega) z := by
  have hden := xiShiftCoreE_ne_zero_upperHalfPlane (omega := omega) hz
  unfold xiShiftCoreTheta
  exact ((differentiableAt_xiShiftCoreE omega (-z)).comp z differentiableAt_id.neg).div
    (differentiableAt_xiShiftCoreE omega z) hden

theorem differentiableAt_suzukiUpperCayleyInv
    {u : ℂ} (hu : u ≠ 1) :
    DifferentiableAt ℂ
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u := by
  unfold GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  exact (differentiableAt_const _).mul
    (((differentiableAt_const _).add differentiableAt_id).div
      ((differentiableAt_const _).sub differentiableAt_id) hden)

/-- Symmetric shifted-Xi core as a contractive disk multiplier. -/
def xiShiftCoreDiskMultiplier (omega : ℝ) : DiskMultiplier where
  fn := fun u => xiShiftCoreTheta omega
    (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u)
  diff := by
    intro u hu
    have hnorm : ‖u‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hu1 : u ≠ 1 := by
      intro h
      rw [h, norm_one] at hnorm
      exact (lt_irrefl 1) hnorm
    have him := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hnorm
    exact ((differentiableAt_xiShiftCoreTheta him).comp u
      (differentiableAt_suzukiUpperCayleyInv hu1)).differentiableWithinAt
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := by
    intro u hu
    have hnorm : ‖u‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    exact norm_xiShiftCoreTheta_le_one
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hnorm)

/-- Unimodular finite-tail Cayley scale as a disk multiplier. -/
def xiShiftFiniteCayleyUnitMultiplier
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] : DiskMultiplier where
  fn := fun _ => xiShiftFiniteCayleyUnit omega
  diff := differentiableOn_const _
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := by
    intro _ _
    exact le_of_eq (norm_xiShiftFiniteCayleyUnit_eq_one homega)

/-- Schur numerator for the finite transverse shifted-Xi quotient. -/
def xiShiftFiniteSchurNumerator
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] : DiskMultiplier :=
  (xiShiftFiniteCayleyUnitMultiplier omega homega).mul
    ((xiShiftFiniteNumeratorBlaschke omega homega).toMultiplier.mul
      (xiShiftCoreDiskMultiplier omega))

@[simp]
theorem xiShiftFiniteSchurNumerator_bd
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    (xiShiftFiniteSchurNumerator omega homega).bd = 1 := by
  change 1 * (1 * 1) = 1
  norm_num

theorem xiShiftFiniteSchurNumerator_fn
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] (u : ℂ) :
    (xiShiftFiniteSchurNumerator omega homega).fn u =
      xiShiftFiniteCayleyUnit omega *
        (xiShiftFiniteNumeratorBlaschke omega homega).fn u *
        xiShiftCoreTheta omega
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u) := by
  change xiShiftFiniteCayleyUnit omega *
      ((xiShiftFiniteNumeratorBlaschke omega homega).fn u *
        xiShiftCoreTheta omega
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u)) = _
  ring

/-- Literal shifted-Xi quotient equals one finite generalized-Schur quotient after Cayley. -/
theorem suzukiCanonicalTheta_eq_finiteGeneralizedSchur_cayley
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    {z : ℂ} (hz : 0 < z.im)
    (hE : suzukiCanonicalE omega z ≠ 0) :
    suzukiCanonicalTheta omega z =
      (xiShiftFiniteSchurNumerator omega homega).fn
          (upperToDiskCayley z) /
        (xiShiftFinitePoleBlaschke omega).fn
          (upperToDiskCayley z) := by
  have hext : xiShiftExtremeE omega z ≠ 0 := by
    intro hzero
    apply hE
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  rw [suzukiCanonicalTheta_eq_extremeTheta_mul_coreTheta hz hE,
    xiShiftExtremeTheta_eq_finiteDiskBlaschke_div homega hz hext,
    xiShiftFiniteSchurNumerator_fn]
  have hcayley : upperToDiskCayley z = lineCayley z := rfl
  rw [hcayley,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley]
  · ring
  · intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith

end

end RHTower
