import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteDiskFactor
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteLeakageRank
import GaloisForLFunctions.HTGeometry.GeneralizedSchurValueKernelRankProfile
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteBlaschkeIsometry
import GaloisForLFunctions.RHTower.SuzukiShiftedXiLeakageNormBounds

/-!
# Infinite shifted-Xi kernel identification and exact cancelled rank

Conjugation-closed finite tail packets identify the literal canonical-product quotient with the
phase-normalized infinite disk Blaschke quotient at Hermitian cross-product level. Cayley transport
then identifies the regular Suzuki kernel, by invertible diagonal congruence, with the arbitrary-
inner generalized-Schur value kernel. The resulting rank classification is valid at exceptional
shifts: common numerator/denominator factors are measured by restricted adjoint rank.
-/

open Complex Set Filter Topology Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open scoped Classical

theorem tprod_eq_zero_of_multipliable_factor
    {ι : Type*} {f : ι → ℂ} (hf : Multipliable f)
    (i : ι) (hi : f i = 0) :
    (∏' j, f j) = 0 := by
  have hzero : Tendsto
      (fun s : Finset ι => s.prod f) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with s hs
    symm
    exact Finset.prod_eq_zero (by simpa using hs) hi
  exact tendsto_nhds_unique hf.hasProd hzero

theorem pair_denominator_ne_zero_of_extremeE_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega) {z : ℂ}
    (hext : xiShiftExtremeE omega z ≠ 0)
    (q : XiShiftRightZeroCopy omega) :
    xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1 ≠ 0 := by
  intro hq
  apply hext
  rw [xiShiftExtremeE,
    xiShiftExtremeCanonicalProduct_eq_right_pair_tprod omega homega]
  exact tprod_eq_zero_of_multipliable_factor
    (multipliable_xiShiftRightReflectionPairFactor omega
      (-z - (omega : ℂ) * I)) q hq

theorem xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega) {z : ℂ} (hz : 0 < z.im)
    (hext : xiShiftExtremeE omega z ≠ 0) :
    (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z) ≠ 0 := by
  have hzI : z + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  apply indexedBlaschkeProduct_ne_zero
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)
    (summable_one_sub_norm_xiShiftPoleDiskCoordinate homega)
    (GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)
  intro q heq
  have hpI : xiShiftPoleCoordinate omega q + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [xiShiftPoleCoordinate_im_pos omega q]
  have hinv := congrArg GaloisForLFunctions.RHTower.suzukiUpperCayleyInv heq
  change lineCayley z = lineCayley (xiShiftPoleCoordinate omega q) at heq
  change GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (lineCayley z) =
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
      (lineCayley (xiShiftPoleCoordinate omega q)) at hinv
  rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hzI,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpI] at hinv
  have hpair := pair_denominator_ne_zero_of_extremeE_ne_zero homega hext q
  apply hpair
  rw [xiShiftRightReflectionPairFactor_denominator_shift_scale, hinv]
  ring

theorem hasProd_xiShiftNumeratorNormalizedFactor
    {omega : ℝ} (homega : 0 ≤ omega) {u : ℂ} (hu : ‖u‖ < 1) :
    HasProd (fun q : XiShiftRightZeroCopy omega =>
        normalizedBlaschkeFactor (xiShiftNumeratorDiskCoordinate omega q) u)
      ((xiShiftNumeratorBlaschkeMultiplier homega).fn u) := by
  have h := (indexedBlaschkeProduct_hasProdLocallyUniformlyOn
    (xiShiftNumeratorDiskCoordinate omega)
    (norm_xiShiftNumeratorDiskCoordinate_lt_one homega)
    (summable_one_sub_norm_xiShiftNumeratorDiskCoordinate homega)).hasProd
      (show u ∈ Metric.ball (0 : ℂ) 1 by
        simpa [Metric.mem_ball, dist_zero_right] using hu)
  exact h

theorem hasProd_xiShiftPoleNormalizedFactor
    {omega : ℝ} (homega : 0 ≤ omega) {u : ℂ} (hu : ‖u‖ < 1) :
    HasProd (fun q : XiShiftRightZeroCopy omega =>
        normalizedBlaschkeFactor (xiShiftPoleDiskCoordinate omega q) u)
      ((xiShiftPoleBlaschkeMultiplier homega).fn u) := by
  have h := (indexedBlaschkeProduct_hasProdLocallyUniformlyOn
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)
    (summable_one_sub_norm_xiShiftPoleDiskCoordinate homega)).hasProd
      (show u ∈ Metric.ball (0 : ℂ) 1 by
        simpa [Metric.mem_ball, dist_zero_right] using hu)
  exact h

theorem hasProd_xiShiftRightReflectionPairQuotientFactor
    {omega : ℝ} (homega : 0 ≤ omega) {z : ℂ}
    (hext : xiShiftExtremeE omega z ≠ 0) :
    HasProd (fun q : XiShiftRightZeroCopy omega =>
        xiShiftRightReflectionPairQuotientFactor omega z q)
      (xiShiftExtremeTheta omega z) := by
  have hnum := hasProd_xiShiftRightReflectionPairFactor
    omega homega (z - (omega : ℂ) * I)
  have hden := hasProd_xiShiftRightReflectionPairFactor
    omega homega (-z - (omega : ℂ) * I)
  have hquot := HasProd.div_of_limit_ne_zero hnum hden (by
    simpa only [xiShiftExtremeE] using hext)
  simpa only [xiShiftExtremeTheta, xiShiftExtremeE, neg_neg,
    xiShiftRightReflectionPairQuotientFactor] using hquot

theorem xiShiftExtremeTheta_cross_eq_infiniteBlaschke_cross
    {omega : ℝ} (homega : 0 ≤ omega)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hextz : xiShiftExtremeE omega z ≠ 0)
    (hextw : xiShiftExtremeE omega w ≠ 0) :
    xiShiftExtremeTheta omega z *
        (starRingEnd ℂ) (xiShiftExtremeTheta omega w) =
      ((xiShiftNumeratorBlaschkeMultiplier homega).fn
            (upperToDiskCayley z) /
          (xiShiftPoleBlaschkeMultiplier homega).fn
            (upperToDiskCayley z)) *
        (starRingEnd ℂ)
          ((xiShiftNumeratorBlaschkeMultiplier homega).fn
                (upperToDiskCayley w) /
            (xiShiftPoleBlaschkeMultiplier homega).fn
                (upperToDiskCayley w)) := by
  let close : Finset (XiShiftRightZeroCopy omega) →
      Finset (XiShiftRightZeroCopy omega) :=
    xiShiftRightConjClosedFinset omega
  let fN (v : ℂ) (s : Finset (XiShiftRightZeroCopy omega)) : ℂ :=
    xiShiftFiniteNumeratorNormalizedProductOn omega (close s)
      (upperToDiskCayley v)
  let fP (v : ℂ) (s : Finset (XiShiftRightZeroCopy omega)) : ℂ :=
    xiShiftFinitePoleNormalizedProductOn omega (close s)
      (upperToDiskCayley v)
  let fQ (v : ℂ) (s : Finset (XiShiftRightZeroCopy omega)) : ℂ :=
    (close s).prod (fun q => xiShiftRightReflectionPairQuotientFactor omega v q)
  have hclose : Tendsto close atTop atTop :=
    xiShiftRightConjClosedFinset_tendsto_atTop omega
  have hNz : Tendsto (fN z) atTop
      (𝓝 ((xiShiftNumeratorBlaschkeMultiplier homega).fn
        (upperToDiskCayley z))) := by
    exact (hasProd_xiShiftNumeratorNormalizedFactor homega
      (GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)).comp hclose
  have hNw : Tendsto (fN w) atTop
      (𝓝 ((xiShiftNumeratorBlaschkeMultiplier homega).fn
        (upperToDiskCayley w))) := by
    exact (hasProd_xiShiftNumeratorNormalizedFactor homega
      (GaloisForLFunctions.cayley_upperHalfPlane_to_disk w hw)).comp hclose
  have hPz : Tendsto (fP z) atTop
      (𝓝 ((xiShiftPoleBlaschkeMultiplier homega).fn
        (upperToDiskCayley z))) := by
    exact (hasProd_xiShiftPoleNormalizedFactor homega
      (GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz)).comp hclose
  have hPw : Tendsto (fP w) atTop
      (𝓝 ((xiShiftPoleBlaschkeMultiplier homega).fn
        (upperToDiskCayley w))) := by
    exact (hasProd_xiShiftPoleNormalizedFactor homega
      (GaloisForLFunctions.cayley_upperHalfPlane_to_disk w hw)).comp hclose
  have hpz0 := xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
    homega hz hextz
  have hpw0 := xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
    homega hw hextw
  have hFz : Tendsto (fun s => fN z s / fP z s) atTop
      (𝓝 ((xiShiftNumeratorBlaschkeMultiplier homega).fn
            (upperToDiskCayley z) /
          (xiShiftPoleBlaschkeMultiplier homega).fn
            (upperToDiskCayley z))) :=
    hNz.div hPz hpz0
  have hFw : Tendsto (fun s => fN w s / fP w s) atTop
      (𝓝 ((xiShiftNumeratorBlaschkeMultiplier homega).fn
            (upperToDiskCayley w) /
          (xiShiftPoleBlaschkeMultiplier homega).fn
            (upperToDiskCayley w))) :=
    hNw.div hPw hpw0
  have hQz : Tendsto (fQ z) atTop (𝓝 (xiShiftExtremeTheta omega z)) := by
    exact (hasProd_xiShiftRightReflectionPairQuotientFactor homega hextz).comp
      hclose
  have hQw : Tendsto (fQ w) atTop (𝓝 (xiShiftExtremeTheta omega w)) := by
    exact (hasProd_xiShiftRightReflectionPairQuotientFactor homega hextw).comp
      hclose
  have hstarF := (Complex.continuous_conj.tendsto _).comp hFw
  have hstarQ := (Complex.continuous_conj.tendsto _).comp hQw
  have hlimF := hFz.mul hstarF
  have hlimQ := hQz.mul hstarQ
  have hevent : ∀ s : Finset (XiShiftRightZeroCopy omega),
      (fN z s / fP z s) * (starRingEnd ℂ) (fN w s / fP w s) =
        fQ z s * (starRingEnd ℂ) (fQ w s) := by
    intro s
    apply finset_normalized_cross_eq_pair_cross homega (close s)
    · exact xiShiftRightConjClosedFinset_image omega s
    · exact hz
    · exact hw
    · intro q hq
      exact pair_denominator_ne_zero_of_extremeE_ne_zero homega hextz q
    · intro q hq
      exact pair_denominator_ne_zero_of_extremeE_ne_zero homega hextw q
  exact tendsto_nhds_unique hlimQ
    (hlimF.congr' (Eventually.of_forall hevent))

theorem suzukiCanonicalTheta_cross_eq_infiniteGeneralizedSchurQuotient_cross
    {omega : ℝ} (homega : 0 ≤ omega)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im)
    (hEz : suzukiCanonicalE omega z ≠ 0)
    (hEw : suzukiCanonicalE omega w ≠ 0) :
    suzukiCanonicalTheta omega z *
        (starRingEnd ℂ) (suzukiCanonicalTheta omega w) =
      ((xiShiftInfiniteSchurNumerator homega).fn
            (upperToDiskCayley z) /
          (xiShiftPoleBlaschkeMultiplier homega).fn
            (upperToDiskCayley z)) *
        (starRingEnd ℂ)
          ((xiShiftInfiniteSchurNumerator homega).fn
                (upperToDiskCayley w) /
            (xiShiftPoleBlaschkeMultiplier homega).fn
                (upperToDiskCayley w)) := by
  have hextz : xiShiftExtremeE omega z ≠ 0 := by
    intro hzero
    apply hEz
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  have hextw : xiShiftExtremeE omega w ≠ 0 := by
    intro hzero
    apply hEw
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  have htail := xiShiftExtremeTheta_cross_eq_infiniteBlaschke_cross
    homega hz hw hextz hextw
  have hzI : z + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hwI : w + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  rw [suzukiCanonicalTheta_eq_extremeTheta_mul_coreTheta hz hEz,
    suzukiCanonicalTheta_eq_extremeTheta_mul_coreTheta hw hEw]
  change (xiShiftExtremeTheta omega z * xiShiftCoreTheta omega z) *
      (starRingEnd ℂ) (xiShiftExtremeTheta omega w * xiShiftCoreTheta omega w) =
    (((xiShiftNumeratorBlaschkeMultiplier homega).fn (upperToDiskCayley z) *
          xiShiftCoreTheta omega
            (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
              (upperToDiskCayley z))) /
        (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z)) *
      (starRingEnd ℂ)
        ((((xiShiftNumeratorBlaschkeMultiplier homega).fn (upperToDiskCayley w) *
              xiShiftCoreTheta omega
                (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
                  (upperToDiskCayley w)))) /
          (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley w))
  have hcz : upperToDiskCayley z = lineCayley z := rfl
  have hcw : upperToDiskCayley w = lineCayley w := rfl
  rw [hcz, hcw,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hzI,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hwI]
  rw [hcz, hcw] at htail
  simp only [map_mul, map_div₀] at htail ⊢
  calc
    xiShiftExtremeTheta omega z * xiShiftCoreTheta omega z *
        ((starRingEnd ℂ) (xiShiftExtremeTheta omega w) *
          (starRingEnd ℂ) (xiShiftCoreTheta omega w)) =
      (xiShiftExtremeTheta omega z *
          (starRingEnd ℂ) (xiShiftExtremeTheta omega w)) *
        (xiShiftCoreTheta omega z *
          (starRingEnd ℂ) (xiShiftCoreTheta omega w)) := by ring
    _ = _ := by rw [htail]; ring

/-- Combined Cayley and infinite-denominator diagonal weight. -/
def xiShiftInfiniteUpperKernelWeight
    {omega : ℝ} (homega : 0 ≤ omega)
    (z : XiShiftRegularUpperNode omega) : ℂ :=
  upperToDiskKernelWeight z.1 *
    ((xiShiftPoleBlaschkeMultiplier homega).fn
      (upperToDiskCayley z.1))⁻¹

theorem xiShiftInfiniteUpperKernelWeight_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega)
    (z : XiShiftRegularUpperNode omega) :
    xiShiftInfiniteUpperKernelWeight homega z ≠ 0 := by
  have hext : xiShiftExtremeE omega z.1 ≠ 0 := by
    intro hzero
    apply z.property.2
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  exact mul_ne_zero
    (upperToDiskKernelWeight_ne_zero_of_im_pos z.property.1)
    (inv_ne_zero (xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
      homega z.property.1 hext))

theorem xiShiftRegularUpperKernel_eq_infiniteDiskValue_congruence
    {omega : ℝ} (homega : 0 ≤ omega)
    (z w : XiShiftRegularUpperNode omega) :
    xiShiftRegularUpperKernel omega z w =
      xiShiftInfiniteUpperKernelWeight homega z *
        generalizedSchurValueKernel
          (xiShiftInfiniteSchurNumerator homega)
          (xiShiftPoleBlaschkeMultiplier homega)
          (upperToDiskCayley z.1) (upperToDiskCayley w.1) *
        (starRingEnd ℂ) (xiShiftInfiniteUpperKernelWeight homega w) := by
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
  have hextz : xiShiftExtremeE omega z.1 ≠ 0 := by
    intro hzero
    apply z.property.2
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  have hextw : xiShiftExtremeE omega w.1 ≠ 0 := by
    intro hzero
    apply w.property.2
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero]
    ring
  have hbz := xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
    homega z.property.1 hextz
  have hbw := xiShiftPoleBlaschkeMultiplier_cayley_ne_zero
    homega w.property.1 hextw
  have hden : 1 - upperToDiskCayley z.1 *
      (starRingEnd ℂ) (upperToDiskCayley w.1) ≠ 0 :=
    one_sub_mul_conj_ne_zero_of_norm_lt_one hcz hcw
  have hcross :=
    suzukiCanonicalTheta_cross_eq_infiniteGeneralizedSchurQuotient_cross
      homega z.property.1 w.property.1 z.property.2 w.property.2
  have hdisk : diskSchurValueKernel
        (suzukiCanonicalTheta omega z.1)
        (suzukiCanonicalTheta omega w.1)
        (upperToDiskCayley z.1) (upperToDiskCayley w.1) =
      diskSchurValueKernel
        ((xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley z.1) /
          (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley z.1))
        ((xiShiftInfiniteSchurNumerator homega).fn (upperToDiskCayley w.1) /
          (xiShiftPoleBlaschkeMultiplier homega).fn (upperToDiskCayley w.1))
        (upperToDiskCayley z.1) (upperToDiskCayley w.1) := by
    rw [diskSchurValueKernel, diskSchurValueKernel, hcross]
  rw [xiShiftRegularUpperKernel,
    upperHalfPlaneSchurKernel_eq_cayley_congruence
      (suzukiCanonicalTheta omega) hzI hwI hzw,
    hdisk,
    diskSchurValueKernel_div_eq_generalized_congruence hbz hbw hden]
  simp only [xiShiftInfiniteUpperKernelWeight,
    generalizedSchurValueKernel, map_mul, map_inv₀]
  ring

theorem xiShiftRegularUpperKernel_negativeDimension_iff_infiniteDiskValue
    {omega : ℝ} (homega : 0 ≤ omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r ↔
      HasFiniteKernelNegativeDimension
        (fun z w : Metric.ball (0 : ℂ) 1 =>
          generalizedSchurValueKernel
            (xiShiftInfiniteSchurNumerator homega)
            (xiShiftPoleBlaschkeMultiplier homega) z.1 w.1) r := by
  let F := xiShiftInfiniteSchurNumerator homega
  let B := xiShiftPoleBlaschkeMultiplier homega
  let K : ℂ → ℂ → ℂ := generalizedSchurValueKernel F B
  constructor
  · intro hneg
    let e : XiShiftRegularUpperNode omega → Metric.ball (0 : ℂ) 1 := fun z =>
      ⟨upperToDiskCayley z.1,
        by
          rw [Metric.mem_ball, dist_zero_right]
          change ‖(z.1 - I) / (z.1 + I)‖ < 1
          exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk
            z.1 z.property.1⟩
    exact hasFiniteKernelNegativeDimension_of_diagonal_pullback
      (xiShiftRegularUpperKernel omega)
      (fun z w : Metric.ball (0 : ℂ) 1 => K z.1 w.1)
      e (xiShiftInfiniteUpperKernelWeight homega)
      (xiShiftInfiniteUpperKernelWeight_ne_zero homega)
      (fun z w => by
        simpa only [K, F, B, e] using
          xiShiftRegularUpperKernel_eq_infiniteDiskValue_congruence
            homega z w)
      hneg
  · intro hneg
    let invC : ℂ → ℂ :=
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
    have hcont : ContinuousAt
        (fun u : ℂ => suzukiCanonicalE omega (invC u)) 0 := by
      exact (((differentiable_suzukiCanonicalE omega) (invC 0)).comp 0
        (differentiableAt_suzukiUpperCayleyInv (by norm_num))).continuousAt
    have hanchor : suzukiCanonicalE omega (invC 0) ≠ 0 := by
      have hI : suzukiCanonicalE omega I ≠ 0 := by
        rw [suzukiCanonicalE]
        simpa [I_mul_I] using xi_ne_zero_of_real (1 / 2 + omega + 1)
      simpa [invC, GaloisForLFunctions.RHTower.suzukiUpperCayleyInv] using hI
    have hevent : ∀ᶠ u in 𝓝 (0 : ℂ),
        suzukiCanonicalE omega (invC u) ≠ 0 :=
      hcont.eventually_ne hanchor
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hevent
    let delta : ℝ := min epsilon (1 / 2)
    have hdelta : 0 < delta := by
      exact lt_min hepsilon (by norm_num)
    have hdeltaOne : delta < 1 := by
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    let V : Set ℂ := Metric.ball 0 delta
    have hopenV : IsOpen V := Metric.isOpen_ball
    have hsubV : V ⊆ Metric.ball (0 : ℂ) 1 := by
      intro u hu
      exact Metric.mem_ball.mpr
        ((Metric.mem_ball.mp hu).trans hdeltaOne)
    have hneV : V.Nonempty := by
      exact ⟨0, Metric.mem_ball_self hdelta⟩
    have hnonV : ∀ u : V, suzukiCanonicalE omega (invC u.1) ≠ 0 := by
      intro u
      apply hball
      exact Metric.mem_ball.mpr
        ((Metric.mem_ball.mp u.property).trans_le (min_le_left _ _))
    have hnegV : HasFiniteKernelNegativeDimension
        (fun z w : V => K z.1 w.1) r := by
      exact (generalizedSchurValueKernel_openRegion_negativeDimension_iff
        F B V hopenV hsubV hneV r).mpr hneg
    let e : V → XiShiftRegularUpperNode omega := fun u =>
      ⟨invC u.1,
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one
          (by
            have hu := hsubV u.property
            simpa [Metric.mem_ball, dist_zero_right] using hu),
        hnonV u⟩
    let a : V → ℂ := fun u =>
      (xiShiftInfiniteUpperKernelWeight homega (e u))⁻¹
    have ha : ∀ u, a u ≠ 0 := fun u =>
      inv_ne_zero (xiShiftInfiniteUpperKernelWeight_ne_zero homega (e u))
    apply hasFiniteKernelNegativeDimension_of_diagonal_pullback
      (fun z w : V => K z.1 w.1)
      (xiShiftRegularUpperKernel omega) e a ha
    · intro u v
      have huNorm : ‖u.1‖ < 1 := by
        have hu := hsubV u.property
        simpa [Metric.mem_ball, dist_zero_right] using hu
      have hvNorm : ‖v.1‖ < 1 := by
        have hv := hsubV v.property
        simpa [Metric.mem_ball, dist_zero_right] using hv
      have hu1 : u.1 ≠ 1 := by
        intro h
        rw [h, norm_one] at huNorm
        exact (lt_irrefl 1) huNorm
      have hv1 : v.1 ≠ 1 := by
        intro h
        rw [h, norm_one] at hvNorm
        exact (lt_irrefl 1) hvNorm
      have hcu := upperToDiskCayley_suzukiUpperCayleyInv hu1
      have hcv := upperToDiskCayley_suzukiUpperCayleyInv hv1
      have hcong :=
        xiShiftRegularUpperKernel_eq_infiniteDiskValue_congruence
          homega (e u) (e v)
      change K u.1 v.1 =
        (xiShiftInfiniteUpperKernelWeight homega (e u))⁻¹ *
          xiShiftRegularUpperKernel omega (e u) (e v) *
          (starRingEnd ℂ)
            ((xiShiftInfiniteUpperKernelWeight homega (e v))⁻¹)
      rw [hcong]
      change upperToDiskCayley (invC u.1) = u.1 at hcu
      change upperToDiskCayley (invC v.1) = v.1 at hcv
      rw [hcu, hcv]
      simp only [map_inv₀]
      field_simp [xiShiftInfiniteUpperKernelWeight_ne_zero homega (e u),
        xiShiftInfiniteUpperKernelWeight_ne_zero homega (e v),
        (map_ne_zero (starRingEnd ℂ)).mpr
          (xiShiftInfiniteUpperKernelWeight_ne_zero homega (e v))]
      rfl
    · exact hnegV

/-- Literal regular shifted-Xi kernel has exactly the arbitrary-inner restricted leakage rank,
including exceptional shifts with common numerator and denominator factors. -/
theorem xiShiftRegularUpperKernel_negativeDimension_iff_rankAtLeast
    {omega : ℝ} (homega : 0 ≤ omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r ↔
      RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
        (hardyMul (xiShiftInfiniteSchurNumerator homega)) r := by
  rw [xiShiftRegularUpperKernel_negativeDimension_iff_infiniteDiskValue
    homega r]
  exact generalizedSchurValueKernel_negativeDimension_iff_rankAtLeast
    (xiShiftInfiniteSchurNumerator homega)
    (xiShiftPoleBlaschkeMultiplier homega)
    (by rw [xiShiftInfiniteSchurNumerator_bd])
    (xiShiftPoleBlaschkeMultiplier_isometry homega) r

end

end RHTower

