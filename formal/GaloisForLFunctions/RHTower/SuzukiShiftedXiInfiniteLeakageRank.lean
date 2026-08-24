import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteBlaschkeDenominator
import GaloisForLFunctions.HTGeometry.AdjointFiniteRange
import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageDenseRank

open Complex Filter Topology Metric
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The strict-right shifted Xi numerator divisor also satisfies the disk Blaschke condition. -/
theorem summable_one_sub_norm_xiShiftNumeratorDiskCoordinate
    {omega : ℝ} (homega : 0 ≤ omega) :
    Summable (fun q : XiShiftRightZeroCopy omega =>
      1 - ‖xiShiftNumeratorDiskCoordinate omega q‖) := by
  have hbound : ∀ q : XiShiftRightZeroCopy omega,
      1 - ‖xiShiftNumeratorDiskCoordinate omega q‖ ≤
        36 / ‖xiSpectralPoint q.1‖ ^ 2 := by
    intro q
    let mu : ℂ := xiSpectralPoint q.1
    let n : ℂ := xiShiftNumeratorCoordinate omega q
    have hmuImSq : mu.im ^ 2 < 1 / 4 := by
      have hstrip := xi_divisor_support_centered_re_sq_lt_quarter q.1.1
      have him : mu.im = -(((q.1.1 : ℂ).re) - 1 / 2) := by
        simp [mu, xiSpectralPoint]
      rw [him, neg_sq]
      exact hstrip
    have hnim : 0 < n.im := xiShiftNumeratorCoordinate_im_pos homega q
    have homegaHalf : omega < 1 / 2 := by
      have hselected := q.2
      norm_num [mul_re] at hselected
      have hmuNeg : -mu.im < 1 / 2 := by
        nlinarith [sq_nonneg (mu.im + 1 / 2)]
      dsimp only [mu] at hmuNeg
      linarith
    have hnimOne : n.im < 1 := by
      have hmuNeg : -mu.im < 1 / 2 := by
        nlinarith [sq_nonneg (mu.im + 1 / 2)]
      dsimp only [n, xiShiftNumeratorCoordinate]
      simp only [add_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, mul_one, add_zero]
      linarith
    have hden : n + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith
    have hcoord : xiShiftNumeratorDiskCoordinate omega q = upperToDiskCayley n := rfl
    have hrlt : ‖upperToDiskCayley n‖ < 1 := by
      simpa [hcoord] using norm_xiShiftNumeratorDiskCoordinate_lt_one homega q
    have hdefect := one_sub_norm_upperToDiskCayley_sq hden
    have hdenOne : 1 ≤ ‖n + I‖ := by
      have hsq := Complex.sq_norm (n + I)
      rw [Complex.normSq_apply] at hsq
      have him : (n + I).im = n.im + 1 := by simp
      rw [him] at hsq
      nlinarith [sq_nonneg (n + I).re, norm_nonneg (n + I)]
    have hshiftNorm : ‖(((omega + 1 : ℝ) : ℂ) * I)‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), norm_I, mul_one]
      linarith
    have hmuEq : mu = -(n + I) + (((omega + 1 : ℝ) : ℂ) * I) := by
      dsimp only [mu, n, xiShiftNumeratorCoordinate]
      push_cast
      ring
    have hmuLe : ‖mu‖ ≤ 3 * ‖n + I‖ := by
      calc
        ‖mu‖ = ‖-(n + I) + (((omega + 1 : ℝ) : ℂ) * I)‖ := by rw [hmuEq]
        _ ≤ ‖-(n + I)‖ + ‖(((omega + 1 : ℝ) : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ ‖-(n + I)‖ + 2 := add_le_add le_rfl hshiftNorm
        _ = ‖n + I‖ + 2 := by rw [norm_neg]
        _ ≤ 3 * ‖n + I‖ := by linarith
    have hmuSqLe : ‖mu‖ ^ 2 ≤ 9 * ‖n + I‖ ^ 2 := by
      nlinarith [norm_nonneg mu, norm_nonneg (n + I)]
    have hmuPos : 0 < ‖mu‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q.1)
    have hdenPos : 0 < ‖n + I‖ := norm_pos_iff.mpr hden
    rw [hcoord]
    calc
      1 - ‖upperToDiskCayley n‖ ≤ 1 - ‖upperToDiskCayley n‖ ^ 2 := by
        nlinarith [norm_nonneg (upperToDiskCayley n)]
      _ = 4 * n.im / ‖n + I‖ ^ 2 := hdefect
      _ ≤ 36 / ‖mu‖ ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hdenPos) (sq_pos_of_pos hmuPos)).2
        have hleft : 4 * n.im * ‖mu‖ ^ 2 ≤ 4 * ‖mu‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖mu‖)
        have hright : 4 * ‖mu‖ ^ 2 ≤ 36 * ‖n + I‖ ^ 2 := by
          linarith
        exact hleft.trans hright
      _ = 36 / ‖xiSpectralPoint q.1‖ ^ 2 := rfl
  have hbase : Summable (fun q : XiShiftRightZeroCopy omega =>
      1 / ‖xiSpectralPoint q.1‖ ^ 2) :=
    xiSpectralPoint_inv_sq_summable.subtype
      (fun q => omega < (I * xiSpectralPoint q).re)
  have hmajor : Summable (fun q : XiShiftRightZeroCopy omega =>
      36 / ‖xiSpectralPoint q.1‖ ^ 2) := by
    refine (hbase.mul_left 36).congr fun q => ?_
    ring
  exact Summable.of_nonneg_of_le
    (fun q => sub_nonneg.mpr (norm_xiShiftNumeratorDiskCoordinate_lt_one homega q).le)
    hbound hmajor

/-- Literal disk Blaschke numerator over every strict-right shifted-Xi reflected zero copy. -/
def xiShiftNumeratorBlaschkeMultiplier
    {omega : ℝ} (homega : 0 ≤ omega) : DiskMultiplier :=
  indexedBlaschkeMultiplier
    (xiShiftNumeratorDiskCoordinate omega)
    (norm_xiShiftNumeratorDiskCoordinate_lt_one homega)
    (summable_one_sub_norm_xiShiftNumeratorDiskCoordinate homega)

/-- Full infinite shifted-Xi Schur numerator, up to its irrelevant unimodular Cayley scale. -/
def xiShiftInfiniteSchurNumerator
    {omega : ℝ} (homega : 0 ≤ omega) : DiskMultiplier :=
  (xiShiftNumeratorBlaschkeMultiplier homega).mul
    (xiShiftCoreDiskMultiplier omega)

private theorem suzukiCanonicalE_neg_numeratorCoordinate_eq_zero
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    suzukiCanonicalE omega (-xiShiftNumeratorCoordinate omega q) = 0 := by
  rw [suzukiCanonicalE_eq_XiC_shift, xiShiftNumeratorCoordinate]
  have harg : - -(-xiSpectralPoint q.1 + (omega : ℂ) * I) -
      (omega : ℂ) * I = -xiSpectralPoint q.1 := by ring
  rw [harg]
  have hreflect := XiC_xiSpectralPoint_eq_zero (xiZeroCopyReflectEquiv q.1)
  rw [xiSpectralPoint_reflect] at hreflect
  exact hreflect

/-- Pointwise source nonvanishing at one reflected pole makes the literal infinite Schur numerator
nonzero at that denominator coordinate, with no global separation or corona hypothesis. -/
theorem xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero_of_source
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0 →
    (xiShiftInfiniteSchurNumerator homega).fn
      (xiShiftPoleDiskCoordinate omega q) ≠ 0 := by
  intro hsource
  have hpden : xiShiftPoleCoordinate omega q + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith [xiShiftPoleCoordinate_im_pos omega q]
  have hpDisk : ‖xiShiftPoleDiskCoordinate omega q‖ < 1 :=
    norm_xiShiftPoleDiskCoordinate_lt_one omega q
  have haway : ∀ r : XiShiftRightZeroCopy omega,
      xiShiftPoleDiskCoordinate omega q ≠
        xiShiftNumeratorDiskCoordinate omega r := by
    intro r heq
    apply hsource
    have hrden : xiShiftNumeratorCoordinate omega r + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith [xiShiftNumeratorCoordinate_im_pos homega r]
    change lineCayley (xiShiftPoleCoordinate omega q) =
      lineCayley (xiShiftNumeratorCoordinate omega r) at heq
    have hinv := congrArg GaloisForLFunctions.RHTower.suzukiUpperCayleyInv heq
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpden,
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hrden] at hinv
    rw [hinv]
    exact suzukiCanonicalE_neg_numeratorCoordinate_eq_zero omega r
  have hnumBlaschke :
      (xiShiftNumeratorBlaschkeMultiplier homega).fn
        (xiShiftPoleDiskCoordinate omega q) ≠ 0 :=
    indexedBlaschkeProduct_ne_zero
      (xiShiftNumeratorDiskCoordinate omega)
      (norm_xiShiftNumeratorDiskCoordinate_lt_one homega)
      (summable_one_sub_norm_xiShiftNumeratorDiskCoordinate homega)
      hpDisk haway
  have hcoreNumerator : xiShiftCoreE omega (-xiShiftPoleCoordinate omega q) ≠ 0 := by
    intro hzero
    apply hsource
    rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE, hzero, mul_zero]
  have hcoreDenominator : xiShiftCoreE omega (xiShiftPoleCoordinate omega q) ≠ 0 :=
    xiShiftCoreE_ne_zero_upperHalfPlane (xiShiftPoleCoordinate_im_pos omega q)
  have hcoreTheta : xiShiftCoreTheta omega (xiShiftPoleCoordinate omega q) ≠ 0 := by
    exact div_ne_zero hcoreNumerator hcoreDenominator
  have hcoreDisk : (xiShiftCoreDiskMultiplier omega).fn
      (xiShiftPoleDiskCoordinate omega q) ≠ 0 := by
    change xiShiftCoreTheta omega
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
        (lineCayley (xiShiftPoleCoordinate omega q))) ≠ 0
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpden]
    exact hcoreTheta
  exact mul_ne_zero hnumBlaschke hcoreDisk

/-- Nonexceptionality makes the literal infinite Schur numerator nonzero at every denominator
zero, with no separation or corona hypothesis. -/
theorem xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega)
    (hnon : SuzukiShiftNonexceptional omega)
    (q : XiShiftRightZeroCopy omega) :
    (xiShiftInfiniteSchurNumerator homega).fn
      (xiShiftPoleDiskCoordinate omega q) ≠ 0 :=
  xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero_of_source
    homega q (hnon q)

/-- Literal projected Hardy leakage for the complete shifted-Xi Blaschke denominator. -/
def xiShiftInfiniteLeakageCore
    {omega : ℝ} (homega : 0 ≤ omega) :
    HardyDisk →L[ℂ]
      hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega) :=
  modelSpaceLeakageCore
    (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
    (hardyMul (xiShiftInfiniteSchurNumerator homega))

/-- A nonexceptional infinite shifted-Xi divisor gives genuinely infinite algebraic leakage rank. -/
theorem not_finiteDimensional_range_xiShiftInfiniteLeakageCore
    {omega : ℝ} (homega : 0 ≤ omega)
    [Infinite (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) :
    ¬ FiniteDimensional ℂ (xiShiftInfiniteLeakageCore homega).range := by
  apply not_finiteDimensional_range_of_adjoint
  intro hfinite
  letI : FiniteDimensional ℂ (xiShiftInfiniteLeakageCore homega).adjoint.range := hfinite
  let k := Module.finrank ℂ (xiShiftInfiniteLeakageCore homega).adjoint.range + 1
  obtain ⟨q, hq⟩ := exists_xiShiftPoleCoordinate_injective_packet omega k
  let a : Fin k → ℂ := fun i => xiShiftPoleDiskCoordinate omega (q i)
  have ha : ∀ i, ‖a i‖ < 1 := fun i => norm_xiShiftPoleDiskCoordinate_lt_one omega (q i)
  have hainj : Function.Injective a := by
    intro i j hij
    apply hq
    have hpi : xiShiftPoleCoordinate omega (q i) + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith [xiShiftPoleCoordinate_im_pos omega (q i)]
    have hpj : xiShiftPoleCoordinate omega (q j) + I ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      norm_num at him
      linarith [xiShiftPoleCoordinate_im_pos omega (q j)]
    change lineCayley (xiShiftPoleCoordinate omega (q i)) =
      lineCayley (xiShiftPoleCoordinate omega (q j)) at hij
    have hinv := congrArg GaloisForLFunctions.RHTower.suzukiUpperCayleyInv hij
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpi,
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpj] at hinv
    exact hinv
  let K := hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega)
  let v : Fin k → K := fun i =>
    ⟨hardyKernel (ha i),
      hardyKernel_mem_hardyMultiplierModelSpace
        (xiShiftPoleBlaschkeMultiplier homega) (ha i)
        (xiShiftPoleBlaschkeMultiplier_apply_zero homega (q i))⟩
  have hA : ∀ i, (xiShiftInfiniteSchurNumerator homega).fn (a i) ≠ 0 :=
    fun i => xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero
      homega hnon (q i)
  have hbase : LinearIndependent ℂ (fun i : Fin k => hardyKernel (ha i)) :=
    linearIndependent_hardyKernel_of_injective a ha hainj
  let c : Fin k → ℂˣ := fun i => Units.mk0
    ((starRingEnd ℂ) ((xiShiftInfiniteSchurNumerator homega).fn (a i)))
    ((map_ne_zero (starRingEnd ℂ)).mpr (hA i))
  have hscaled : LinearIndependent ℂ
      (fun i : Fin k => (c i : ℂ) • hardyKernel (ha i)) := by
    convert hbase.units_smul c using 1
    ext i
    rfl
  have hadj : ∀ i,
      (xiShiftInfiniteLeakageCore homega).adjoint (v i) =
        (c i : ℂ) • hardyKernel (ha i) := by
    intro i
    rw [xiShiftInfiniteLeakageCore,
      adjoint_modelSpaceLeakageCore_apply,
      adjoint_hardyMul_hardyKernel]
    rfl
  have himages : LinearIndependent ℂ (fun i : Fin k =>
      (xiShiftInfiniteLeakageCore homega).adjoint (v i)) := by
    rw [show (fun i : Fin k =>
      (xiShiftInfiniteLeakageCore homega).adjoint (v i)) =
        (fun i : Fin k => (c i : ℂ) • hardyKernel (ha i)) by
      funext i
      exact hadj i]
    exact hscaled
  have hrange : LinearIndependent ℂ (fun i : Fin k =>
      (⟨(xiShiftInfiniteLeakageCore homega).adjoint (v i), ⟨v i, rfl⟩⟩ :
        (xiShiftInfiniteLeakageCore homega).adjoint.range)) := by
    apply LinearIndependent.of_comp
      (xiShiftInfiniteLeakageCore homega).adjoint.range.subtype
    exact himages
  have hcard := hrange.fintype_card_le_finrank
  simp [k] at hcard

end

end RHTower
