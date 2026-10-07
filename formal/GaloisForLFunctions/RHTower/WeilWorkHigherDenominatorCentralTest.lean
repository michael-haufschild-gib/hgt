import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# A universal central mass bound for full Weil-positive systems

A smoothed convolution of two uniform densities has autocorrelation supported strictly below
`log 2`. Its Weil form is independent of every arithmetic coefficient. The absolute fourth
reciprocal moment of the actual Xi divisor bounds this form by `1/4`, without assuming RH.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace RHTower.WeilHigherDenominator

open Zeta23 WeilSpectral

/-- A probability density with support radius `103/300`. -/
def centralTest : ℝ → ℝ := WeilDeletion.phi (1 / 100) (by norm_num) (1 / 6) 1

abbrev centralTestC : ℝ → ℂ := fun u => (centralTest u : ℂ)

theorem centralTest_contDiff : ContDiff ℝ 2 centralTestC :=
  Complex.ofRealCLM.contDiff.comp (WeilDeletion.phi_contDiff _ _ _)

theorem centralTest_hasCompactSupport : HasCompactSupport centralTest :=
  WeilDeletion.phi_hasCompactSupport _ _ _

theorem centralTestC_hasCompactSupport : HasCompactSupport centralTestC :=
  centralTest_hasCompactSupport.comp_left Complex.ofReal_zero

theorem centralTest_eq_zero {t : ℝ} (ht : 103 / 300 < |t|) : centralTest t = 0 := by
  by_contra h
  have hm := WeilDeletion.support_phi_subset (r := 1 / 100) (by norm_num)
    (w := 1 / 6) (by norm_num) 1 h
  norm_num at hm
  have : |t| ≤ 103 / 300 := abs_le.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
  linarith

theorem paperFT_centralTest_zero : paperFT centralTestC 0 = 1 := by
  unfold paperFT
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, centralTest,
    WeilDeletion.integral_phi (r := 1 / 100) (by norm_num) (w := 1 / 6) (by norm_num) 1]
  simp

theorem atomPairing_centralTest (v : ℕ → ℝ) :
    atomPairing v (crossCorr centralTest centralTest) = 0 := by
  unfold atomPairing
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with hn
  · have hlog2 := Real.log_two_gt_d9
    have hlog : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hpos : 0 < Real.log n := by linarith
    rw [crossCorr_eq_zero (fun t ht => centralTest_eq_zero ht)
        (fun t ht => centralTest_eq_zero ht) (y := Real.log n)
        (by rw [abs_of_pos hpos]; linarith),
      crossCorr_eq_zero (fun t ht => centralTest_eq_zero ht)
        (fun t ht => centralTest_eq_zero ht) (y := -Real.log n)
        (by rw [abs_neg, abs_of_pos hpos]; linarith)]
    ring
  · ring

theorem toReal_lintegral_centralTest {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (∫⁻ r, (specDensity centralTestC r : ℝ≥0∞) ∂boundaryMeasure hW).toReal =
      (zetaZeroConfig.W centralTestC centralTestC).re := by
  obtain ⟨-, heq⟩ := weilFullFunctional_weilTest_eq_lintegral hW centralTest_contDiff
    centralTestC_hasCompactSupport
  have h := re_weilFullFunctional_add_eq (fun n => lam n - ArithmeticFunction.vonMangoldt n)
    (F := centralTest) centralTest_contDiff centralTest_hasCompactSupport
  simp only [add_sub_cancel] at h
  rw [atomPairing_centralTest, sub_zero] at h
  rw [← h, heq, Complex.ofReal_re]

private theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h₁ := Real.exp_le_exp.mpr (le_abs_self x)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- The transform decays quadratically throughout the critical spectral strip. -/
theorem norm_paperFT_centralTest_le {z : ℂ} (hz : z ≠ 0) (hi : |z.im| ≤ 1 / 2) :
    ‖paperFT centralTestC z‖ ≤ Real.exp (103 / 600) * 36 / ‖z‖ ^ 2 := by
  have h := WeilDeletion.norm_paperFT_phi_le (r := 1 / 100) (by norm_num)
    (w := 1 / 6) (by norm_num) 1 hz
  have hc : Real.cosh ((1 / 6) * z.im) ≤ Real.exp (1 / 12) := by
    refine (cosh_le_exp_abs _).trans (Real.exp_le_exp.mpr ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
    linarith
  have he : Real.exp ((1 / 100) * |z.im|) ≤ Real.exp (1 / 200) :=
    Real.exp_le_exp.mpr (by linarith)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  calc ‖paperFT centralTestC z‖
      ≤ Real.exp (1 / 200) * (Real.exp (1 / 12) / ((1 / 6) * ‖z‖)) ^ 2 := by
        refine h.trans ?_
        gcongr
    _ = Real.exp (103 / 600) * 36 / ‖z‖ ^ 2 := by
        rw [div_pow, ← Real.exp_nat_mul, ← mul_div_assoc, ← Real.exp_add]
        norm_num
        ring

theorem centralTest_pair_le {z : ℂ} (hz : z ≠ 0) (hi : |z.im| ≤ 1 / 2) :
    (paperFT centralTestC z * conj (paperFT centralTestC (conj z))).re ≤
      2592 * (1 / ‖z‖ ^ 4) := by
  have h₁ := norm_paperFT_centralTest_le hz hi
  have h₂ := norm_paperFT_centralTest_le (z := conj z) (by simpa using hz)
    (by simpa using hi)
  rw [RCLike.norm_conj] at h₂
  have he : Real.exp (103 / 300) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
  calc (paperFT centralTestC z * conj (paperFT centralTestC (conj z))).re
      ≤ ‖paperFT centralTestC z * conj (paperFT centralTestC (conj z))‖ :=
        Complex.re_le_norm _
    _ = ‖paperFT centralTestC z‖ * ‖paperFT centralTestC (conj z)‖ := by
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ (Real.exp (103 / 600) * 36 / ‖z‖ ^ 2) ^ 2 := by
        simpa only [pow_two] using mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = Real.exp (103 / 300) * 1296 * (1 / ‖z‖ ^ 4) := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul]
        norm_num
        ring
    _ ≤ 2592 * (1 / ‖z‖ ^ 4) := by
        calc Real.exp (103 / 300) * 1296 * (1 / ‖z‖ ^ 4)
            ≤ 2 * 1296 * (1 / ‖z‖ ^ 4) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right he (by norm_num)) (by positivity)
          _ = _ := by ring

/-- The zeta zero side of the central test is small even with off-line zeros retained. -/
theorem re_weil_centralTest_lt_quarter :
    (zetaZeroConfig.W centralTestC centralTestC).re < 1 / 4 := by
  let g : ℂ → ℝ := fun z => 2592 * (1 / ‖gammaOf z‖ ^ 4)
  have hg : ∀ q : XiZeroCopy, g (q.1 : ℂ) =
      2592 * ‖xiZeroCopyReciprocalSquare q‖ ^ 2 := by
    intro q
    simp only [g, WeilDeletion.gammaOf_eq_xiSpectralPoint, xiZeroCopyReciprocalSquare,
      norm_pow, norm_inv]
    ring
  have hsum : Summable (fun q : XiZeroCopy => g (q.1 : ℂ)) := by
    simpa only [hg] using (summable_xiShiftAbsoluteMass 1).mul_left 2592
  have hle := WeilDeletion.carrier_tsum_le zetaSeam g (fun q => by dsimp [g]; positivity)
    hsum (fun ρ => (zetaZeroConfig.Wsummand centralTestC centralTestC ρ).re) (fun ρ => by
      have h := centralTest_pair_le
        (WeilDeletion.gammaOf_ne_zero_of_nontrivialZero ρ.2)
        (WeilDeletion.abs_im_gammaOf_le_half_of_nontrivialZero ρ.2)
      simp only [ZeroConfig.Wsummand, mul_assoc]
      rw [Complex.mul_re]
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
  rw [ZeroConfig.W, Complex.re_tsum
    (WeilConditional.summable_Wsummand centralTest_contDiff centralTestC_hasCompactSupport)]
  have heq : (∑' q : XiZeroCopy, g (q.1 : ℂ)) = 2592 * xiShiftAbsoluteMass 1 := by
    simp only [hg, xiShiftAbsoluteMass, Nat.reduceAdd, tsum_mul_left]
  rw [heq] at hle
  change (∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.Wsummand centralTestC centralTestC ρ).re) ≤
      2592 * xiShiftAbsoluteMass 1 at hle
  have hb := xiShiftAbsoluteMass_one_lt_secondMomentBudget
  linarith

/-- Every full-positive system has central-test spectral mass less than `1/4`. -/
theorem lintegral_centralTest_lt_quarter {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    (∫⁻ r, (specDensity centralTestC r : ℝ≥0∞) ∂boundaryMeasure hW) < 1 / 4 := by
  have hfin := (weilFullFunctional_weilTest_eq_lintegral hW centralTest_contDiff
    centralTestC_hasCompactSupport).1
  apply (ENNReal.toReal_lt_toReal hfin.ne (by norm_num)).mp
  rw [toReal_lintegral_centralTest hW]
  norm_num
  exact re_weil_centralTest_lt_quarter

/-- A central atom of any full-positive system has mass strictly below `1/4`. -/
theorem boundaryMeasure_zero_lt_quarter {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    boundaryMeasure hW {0} < 1 / 4 := by
  have h : (∫⁻ r in ({0} : Set ℝ),
      (specDensity centralTestC r : ℝ≥0∞) ∂boundaryMeasure hW) ≤
      ∫⁻ r, (specDensity centralTestC r : ℝ≥0∞) ∂boundaryMeasure hW :=
    setLIntegral_le_lintegral _ _
  rw [lintegral_singleton] at h
  simp only [specDensity, Complex.ofReal_zero, paperFT_centralTest_zero,
    nnnorm_one, one_pow, ENNReal.coe_one, one_mul] at h
  exact h.trans_lt (lintegral_centralTest_lt_quarter hW)

/-- Third-integral counting gives one uniform open neighborhood without spectral mass. -/
theorem exists_uniform_central_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (lam : ℕ → ℝ) (hW : WeilPositiveFull lam),
      (∀ a b : ℝ, a < b → ∃ n : ℕ,
        (3 : ℝ≥0∞) * boundaryMeasure hW (Ioc a b) = n) →
      boundaryMeasure hW (Ioc (-δ) δ) = 0 := by
  have hd : Differentiable ℂ (paperFT centralTestC) :=
    WeilEF.differentiable_paperFT centralTest_contDiff.continuous
      centralTestC_hasCompactSupport
  have hc : Continuous (fun t : ℝ => ‖paperFT centralTestC (t : ℂ)‖ ^ 2) :=
    (hd.continuous.comp Complex.continuous_ofReal).norm.pow 2
  have hev : ∀ᶠ t : ℝ in 𝓝 0, (3 / 4 : ℝ) < ‖paperFT centralTestC (t : ℂ)‖ ^ 2 :=
    (isOpen_lt continuous_const hc).mem_nhds (by norm_num [paperFT_centralTest_zero])
  obtain ⟨a, ha, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨a / 2, by positivity, fun lam hW hcount => ?_⟩
  have hK : ∀ t ∈ Ioc (-(a / 2)) (a / 2),
      (3 / 4 : ℝ≥0∞) ≤ specDensity centralTestC t := by
    intro t ht
    have ht' : dist t 0 < a := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    rw [WeilConditional.coe_specDensity]
    convert ENNReal.ofReal_le_ofReal (hnear ht').le using 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hmass : (3 / 4 : ℝ≥0∞) * boundaryMeasure hW (Ioc (-(a / 2)) (a / 2)) < 1 / 4 := by
    calc (3 / 4 : ℝ≥0∞) * boundaryMeasure hW (Ioc (-(a / 2)) (a / 2))
        = ∫⁻ t in Ioc (-(a / 2)) (a / 2), 3 / 4 ∂boundaryMeasure hW :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ t in Ioc (-(a / 2)) (a / 2),
          (specDensity centralTestC t : ℝ≥0∞) ∂boundaryMeasure hW :=
        setLIntegral_mono' measurableSet_Ioc hK
      _ ≤ ∫⁻ t, (specDensity centralTestC t : ℝ≥0∞) ∂boundaryMeasure hW :=
        setLIntegral_le_lintegral _ _
      _ < 1 / 4 := lintegral_centralTest_lt_quarter hW
  have hsmall := ENNReal.mul_lt_mul_left (a := (4 : ℝ≥0∞)) (by norm_num)
    (by norm_num) hmass
  have hscale : (3 / 4 : ℝ≥0∞) * boundaryMeasure hW (Ioc (-(a / 2)) (a / 2)) * 4 =
      3 * boundaryMeasure hW (Ioc (-(a / 2)) (a / 2)) := by
    rw [mul_right_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  rw [hscale, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)] at hsmall
  obtain ⟨n, hn⟩ := hcount (-(a / 2)) (a / 2) (by linarith)
  rw [hn] at hsmall
  have hnlt : n < 1 := by exact_mod_cast hsmall
  have hnzero : n = 0 := Nat.lt_one_iff.mp hnlt
  rw [hnzero, Nat.cast_zero] at hn
  exact (mul_eq_zero.mp hn).resolve_left (by norm_num)

end RHTower.WeilHigherDenominator
