import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurValueKernel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiFiniteInertia

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem upperToDiskCayley_suzukiUpperCayleyInv
    {u : ℂ} (hu : u ≠ 1) :
    upperToDiskCayley (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u) = u := by
  rw [upperToDiskCayley, GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  field_simp [hden]
  ring

theorem upperToDiskKernelWeight_ne_zero_of_im_pos
    {z : ℂ} (hz : 0 < z.im) :
    upperToDiskKernelWeight z ≠ 0 := by
  have hzI : z + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hsqrtR : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtC : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hsqrtR
  exact div_ne_zero hsqrtC hzI

theorem upperHalfPlane_sub_conj_ne_zero
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    z - (starRingEnd ℂ) w ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  norm_num at him
  linarith

theorem xiShiftFinitePoleBlaschke_cayley_eq_zero_iff
    (omega : ℝ) [Fintype (XiShiftRightZeroCopy omega)]
    {z : ℂ} (hz : 0 < z.im) :
    (xiShiftFinitePoleBlaschke omega).fn (upperToDiskCayley z) = 0 ↔
      suzukiCanonicalE omega z = 0 := by
  classical
  have hcz : ‖upperToDiskCayley z‖ ≤ 1 :=
    (GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz).le
  rw [xiShiftFinitePoleBlaschke_fn, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  rw [suzukiCanonicalE_eq_zero_iff_exists_shiftRight omega hz]
  constructor
  · rintro ⟨q, hq⟩
    have heq : upperToDiskCayley z = xiShiftPoleDiskCoordinate omega q := by
      apply (blaschkeFactor_eq_zero_iff
        (norm_xiShiftPoleDiskCoordinate_lt_one omega q) hcz).mp
      simpa [blaschkeFactor] using hq
    refine ⟨q, ?_⟩
    have hzinv : z + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith
    have hpinv : xiShiftPoleCoordinate omega q + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      have hp := xiShiftPoleCoordinate_im_pos omega q
      norm_num at him
      linarith
    have heq' := congrArg GaloisForLFunctions.RHTower.suzukiUpperCayleyInv heq
    change GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (lineCayley z) =
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
        (lineCayley (xiShiftPoleCoordinate omega q)) at heq'
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hzinv,
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpinv] at heq'
    exact heq'.symm
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply (blaschkeFactor_eq_zero_iff
      (norm_xiShiftPoleDiskCoordinate_lt_one omega q) hcz).mpr
    change upperToDiskCayley z = upperToDiskCayley (xiShiftPoleCoordinate omega q)
    rw [hq]

theorem xiShiftFinitePoleBlaschke_cayley_ne_zero_iff
    (omega : ℝ) [Fintype (XiShiftRightZeroCopy omega)]
    {z : ℂ} (hz : 0 < z.im) :
    (xiShiftFinitePoleBlaschke omega).fn (upperToDiskCayley z) ≠ 0 ↔
      suzukiCanonicalE omega z ≠ 0 := by
  exact not_congr (xiShiftFinitePoleBlaschke_cayley_eq_zero_iff omega hz)

/-- Regular upper-half-plane nodes for the literal shifted-Xi quotient. -/
def XiShiftRegularUpperNode (omega : ℝ) :=
  {z : ℂ // 0 < z.im ∧ suzukiCanonicalE omega z ≠ 0}

/-- Literal shifted-Xi Hermite--Biehler kernel on its regular upper-half-plane locus. -/
def xiShiftRegularUpperKernel (omega : ℝ)
    (z w : XiShiftRegularUpperNode omega) : ℂ :=
  upperHalfPlaneSchurKernel (suzukiCanonicalTheta omega) z.1 w.1

/-- Combined Cayley and finite-denominator diagonal weight. -/
def xiShiftFiniteUpperKernelWeight (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)]
    (z : XiShiftRegularUpperNode omega) : ℂ :=
  upperToDiskKernelWeight z.1 *
    ((xiShiftFinitePoleBlaschke omega).fn (upperToDiskCayley z.1))⁻¹

theorem xiShiftFiniteUpperKernelWeight_ne_zero
    (omega : ℝ) [Fintype (XiShiftRightZeroCopy omega)]
    (z : XiShiftRegularUpperNode omega) :
    xiShiftFiniteUpperKernelWeight omega z ≠ 0 := by
  exact mul_ne_zero
    (upperToDiskKernelWeight_ne_zero_of_im_pos z.property.1)
    (inv_ne_zero
      ((xiShiftFinitePoleBlaschke_cayley_ne_zero_iff omega z.property.1).mpr
        z.property.2))

theorem one_sub_mul_conj_ne_zero_of_norm_lt_one
    {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - z * (starRingEnd ℂ) w ≠ 0 := by
  intro hzero
  have hprod : z * (starRingEnd ℂ) w = 1 := by linear_combination -hzero
  have hnorm := congrArg norm hprod
  rw [norm_mul, RCLike.norm_conj, norm_one] at hnorm
  nlinarith [norm_nonneg z, norm_nonneg w]

theorem xiShiftRegularUpperKernel_eq_finiteDisk_congruence
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (z w : XiShiftRegularUpperNode omega) :
    xiShiftRegularUpperKernel omega z w =
      xiShiftFiniteUpperKernelWeight omega z *
        finiteBlaschkeGeneralizedSchurValueKernel
          (xiShiftFiniteSchurNumerator omega homega)
          (xiShiftFinitePoleBlaschke omega)
          (upperToDiskCayley z.1) (upperToDiskCayley w.1) *
        (starRingEnd ℂ) (xiShiftFiniteUpperKernelWeight omega w) := by
  have hzI : z.1 + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [z.property.1]
  have hwI : (starRingEnd ℂ) w.1 - I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [w.property.1]
  have hzw : z.1 - (starRingEnd ℂ) w.1 ≠ 0 :=
    upperHalfPlane_sub_conj_ne_zero z.property.1 w.property.1
  have hcz := GaloisForLFunctions.cayley_upperHalfPlane_to_disk z.1 z.property.1
  have hcw := GaloisForLFunctions.cayley_upperHalfPlane_to_disk w.1 w.property.1
  have hbz : (xiShiftFinitePoleBlaschke omega).fn
      (upperToDiskCayley z.1) ≠ 0 :=
    (xiShiftFinitePoleBlaschke_cayley_ne_zero_iff omega z.property.1).mpr
      z.property.2
  have hbw : (xiShiftFinitePoleBlaschke omega).fn
      (upperToDiskCayley w.1) ≠ 0 :=
    (xiShiftFinitePoleBlaschke_cayley_ne_zero_iff omega w.property.1).mpr
      w.property.2
  have hden : 1 - upperToDiskCayley z.1 *
      (starRingEnd ℂ) (upperToDiskCayley w.1) ≠ 0 :=
    one_sub_mul_conj_ne_zero_of_norm_lt_one hcz hcw
  rw [xiShiftRegularUpperKernel,
    upperHalfPlaneSchurKernel_eq_cayley_congruence
      (suzukiCanonicalTheta omega) hzI hwI hzw,
    suzukiCanonicalTheta_eq_finiteGeneralizedSchur_cayley
      homega z.property.1 z.property.2,
    suzukiCanonicalTheta_eq_finiteGeneralizedSchur_cayley
      homega w.property.1 w.property.2,
    diskSchurValueKernel_div_eq_generalized_congruence hbz hbw hden]
  simp only [xiShiftFiniteUpperKernelWeight,
    finiteBlaschkeGeneralizedSchurValueKernel,
    diskGeneralizedSchurValueKernel, map_mul, map_inv₀]
  field_simp [hbz, hbw, hden,
    (map_ne_zero (starRingEnd ℂ)).mpr hbw]

/-- Inverse Cayley image of the exterior disk annulus as a regular shifted-Xi node. -/
def xiShiftFiniteExteriorToRegularUpper
    (omega : ℝ) [Fintype (XiShiftRightZeroCopy omega)]
    (u : (xiShiftFinitePoleBlaschke omega).exteriorDisk) :
    XiShiftRegularUpperNode omega := by
  have hu : ‖(u.1 : ℂ)‖ < 1 := u.property.2
  have hu1 : u.1 ≠ 1 := by
    intro h
    rw [h, norm_one] at hu
    exact (lt_irrefl 1) hu
  let z := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv u.1
  have hz : 0 < z.im :=
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hu
  have hc : upperToDiskCayley z = u.1 :=
    upperToDiskCayley_suzukiUpperCayleyInv hu1
  have hB : (xiShiftFinitePoleBlaschke omega).fn u.1 ≠ 0 :=
    (xiShiftFinitePoleBlaschke omega).fn_ne_zero_of_mem_exteriorDisk u.property
  refine ⟨z, hz, ?_⟩
  apply (xiShiftFinitePoleBlaschke_cayley_ne_zero_iff omega hz).mp
  rwa [hc]

theorem upperToDiskCayley_xiShiftFiniteExteriorToRegularUpper
    (omega : ℝ) [Fintype (XiShiftRightZeroCopy omega)]
    (u : (xiShiftFinitePoleBlaschke omega).exteriorDisk) :
    upperToDiskCayley (xiShiftFiniteExteriorToRegularUpper omega u).1 = u.1 := by
  apply upperToDiskCayley_suzukiUpperCayleyInv
  intro h
  have hu := u.property.2
  rw [h, norm_one] at hu
  exact (lt_irrefl 1) hu

theorem xiShiftRegularUpperKernel_exactNegativeSquares_finite
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) :
    HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega)
        (Fintype.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r : ℕ, HasFiniteKernelNegativeDimension
          (xiShiftRegularUpperKernel omega) r →
        r ≤ Fintype.card (XiShiftRightZeroCopy omega) := by
  let F := xiShiftFiniteSchurNumerator omega homega
  let B := xiShiftFinitePoleBlaschke omega
  have hzero : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0 := by
    exact xiShiftFiniteSchurNumerator_nonzero_on_poleBlaschkeZeros
      homega hnon
  have hdisk := finiteBlaschkeGeneralizedSchurValueKernel_exactNegativeSquares
    F B (by simp [F, xiShiftFiniteSchurNumerator_bd]) hzero
  have hext := finiteBlaschkeGeneralizedSchurValueKernel_hasExteriorNegativeDimension
    F B hzero
  constructor
  · have hlower : HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel omega) B.deg := by
      let e : B.exteriorDisk → XiShiftRegularUpperNode omega :=
        fun u => xiShiftFiniteExteriorToRegularUpper omega u
      let a : B.exteriorDisk → ℂ := fun u =>
        (xiShiftFiniteUpperKernelWeight omega (e u))⁻¹
      have ha : ∀ u, a u ≠ 0 := fun u =>
        inv_ne_zero (xiShiftFiniteUpperKernelWeight_ne_zero omega (e u))
      apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
        (fun u v : B.exteriorDisk =>
          finiteBlaschkeGeneralizedSchurValueKernel F B u v)
        (xiShiftRegularUpperKernel omega) e a ha
      · intro u v
        have hcong := xiShiftRegularUpperKernel_eq_finiteDisk_congruence
          homega (e u) (e v)
        have hcu : upperToDiskCayley (e u).1 = u.1 :=
          upperToDiskCayley_xiShiftFiniteExteriorToRegularUpper omega u
        have hcv : upperToDiskCayley (e v).1 = v.1 :=
          upperToDiskCayley_xiShiftFiniteExteriorToRegularUpper omega v
        rw [hcu, hcv] at hcong
        change finiteBlaschkeGeneralizedSchurValueKernel F B u.1 v.1 =
          (xiShiftFiniteUpperKernelWeight omega (e u))⁻¹ *
            xiShiftRegularUpperKernel omega (e u) (e v) *
            (starRingEnd ℂ)
              ((xiShiftFiniteUpperKernelWeight omega (e v))⁻¹)
        rw [hcong]
        simp only [map_inv₀]
        field_simp [xiShiftFiniteUpperKernelWeight_ne_zero omega (e u),
          xiShiftFiniteUpperKernelWeight_ne_zero omega (e v),
          (map_ne_zero (starRingEnd ℂ)).mpr
            (xiShiftFiniteUpperKernelWeight_ne_zero omega (e v))]
        rfl
      · exact hext
    simpa [B, xiShiftFinitePoleBlaschke_deg] using hlower
  · intro r hupper
    have hdiskr : HasFiniteKernelNegativeDimension
        (fun u v : Metric.ball (0 : ℂ) 1 =>
          finiteBlaschkeGeneralizedSchurValueKernel F B u v) r := by
      let e : XiShiftRegularUpperNode omega → Metric.ball (0 : ℂ) 1 :=
        fun z => ⟨upperToDiskCayley z.1,
          by
            rw [Metric.mem_ball, dist_zero_right]
            exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk
              z.1 z.property.1⟩
      let a : XiShiftRegularUpperNode omega → ℂ := fun z =>
        xiShiftFiniteUpperKernelWeight omega z
      have ha : ∀ z, a z ≠ 0 := fun z =>
        xiShiftFiniteUpperKernelWeight_ne_zero omega z
      apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
        (xiShiftRegularUpperKernel omega)
        (fun u v : Metric.ball (0 : ℂ) 1 =>
          finiteBlaschkeGeneralizedSchurValueKernel F B u v)
        e a ha
      · intro z w
        exact xiShiftRegularUpperKernel_eq_finiteDisk_congruence homega z w
      · exact hupper
    have hle : r ≤ B.deg := hdisk.2 r hdiskr
    simpa [B, xiShiftFinitePoleBlaschke_deg] using hle

end

end RHTower
