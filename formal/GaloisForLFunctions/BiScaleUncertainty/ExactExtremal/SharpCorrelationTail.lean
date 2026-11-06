import GaloisForLFunctions.BiScaleUncertainty.ExactExtremal.ExactBlindTest
import GaloisForLFunctions.BiScaleUncertainty.ExactExtremal.PowerDivisorCapacity
import GaloisForLFunctions.BiScaleUncertainty.PositiveSpectralXiDivisorCapacity
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheTwistedArcFamilyIsNearNull

/-!
# The exact blind correlation attains the squared-divisor boundary

Every positive arc mixture has a correlation tail with double-exponential exponent
one. Strip inversion transfers the full squared Xi divisor, excluding every larger
exponent. The annihilating arc measure therefore attains this boundary with exact
integer blindness.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Nat ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

open _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

noncomputable section

private theorem abs_crossCorr_shiftedGamma_le_tail (j : ℕ) (x : ℝ) :
    |crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x| ≤
      2 * absMass * (decayConst * gammaScale j) ^ 2 * doubleExpTail (|x| / 2 - 1) := by
  have h := abs_crossCorr_truncTest_sub_le j (|x| / 2) x
  rw [crossCorr_truncTest_eq_zero (xiShiftedGammaTest j) (L := |x| / 2) (y := x)
    (by linarith), zero_sub, abs_neg] at h
  exact h

/-- The truncation radius half the lag gives double-exponential exponent one. -/
theorem exists_doubleExp_crossCorr_arcSpectrum_bound (μ : ProbabilityMeasure ArcParam) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ x : ℝ,
      |crossCorr (stripTest (arcSpectrum μ)) (stripTest (arcSpectrum μ)) x| ≤
        C * Real.exp (-a * Real.exp |x|) := by
  let w := arcSpectralWeight (μ : Measure ArcParam)
  let S := ∑' j, w j * gammaScale j ^ 2
  have hw : ∀ j, 0 ≤ w j := arcSpectralWeight_nonneg _
  have hs : Summable fun j => w j * gammaScale j ^ 2 := summable_arcSpectralWeight _
  have hS : 0 ≤ S := tsum_nonneg fun j => mul_nonneg (hw j) (sq_nonneg _)
  have hMass : 0 ≤ absMass := absMass_nonneg
  let C := 2 * absMass * decayConst ^ 2 * S
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨Real.pi / 6 * Real.exp (-2), C + 1, by positivity, by positivity, fun x => ?_⟩
  let D := 2 * absMass * decayConst ^ 2 * doubleExpTail (|x| / 2 - 1)
  have hd : Summable fun j => D * (w j * gammaScale j ^ 2) := hs.mul_left D
  have hb (j : ℕ) : ‖w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x‖ ≤
      D * (w j * gammaScale j ^ 2) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw j), Real.norm_eq_abs]
    calc
      w j * |crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x| ≤
          w j * (2 * absMass * (decayConst * gammaScale j) ^ 2 *
            doubleExpTail (|x| / 2 - 1)) :=
        mul_le_mul_of_nonneg_left (abs_crossCorr_shiftedGamma_le_tail j x) (hw j)
      _ = _ := by dsimp only [D]; ring
  have hn : Summable fun j => ‖w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb hd
  have htail : doubleExpTail (|x| / 2 - 1) =
      Real.exp (-(Real.pi / 6 * Real.exp (-2)) * Real.exp |x|) := by
    unfold doubleExpTail
    rw [show 2 * (|x| / 2 - 1) = |x| + (-2) by ring, Real.exp_add]
    congr 1
    ring
  rw [crossCorr_arcSpectrum, ← Real.norm_eq_abs]
  calc
    ‖∑' j, w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x‖ ≤
        ∑' j, ‖w j * crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x‖ :=
      norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j, D * (w j * gammaScale j ^ 2) := Summable.tsum_le_tsum hb hn hd
    _ = C * doubleExpTail (|x| / 2 - 1) := by
      rw [tsum_mul_left]
      dsimp only [C, D, S]
      ring
    _ ≤ (C + 1) * Real.exp (-(Real.pi / 6 * Real.exp (-2)) * Real.exp |x|) := by
      rw [htail]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

private theorem abs_im_lt_half_of_XiC_zero {z : ℂ} (hz : XiC z = 0) : |z.im| < 1 / 2 := by
  have hxi : xi (1 / 2 + z * I) = 0 := hz
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hxi
  have hre : (1 / 2 + z * I).re = 1 / 2 - z.im := by simp [sub_eq_add_neg]
  rw [hre] at h0 h1
  rw [abs_lt]
  constructor <;> linarith

/-- Full multiplicities, including possible nonreal Xi zeros, exclude every faster tail. -/
theorem not_faster_crossCorr_arcSpectrum (μ : ProbabilityMeasure ArcParam)
    {a b M : ℝ} (ha : 0 < a) (hb : 1 < b) :
    ¬ ∀ x : ℝ, |crossCorr (stripTest (arcSpectrum μ)) (stripTest (arcSpectrum μ)) x| ≤
      M * Real.exp (-a * Real.exp (b * |x|)) := by
  intro hbound
  obtain ⟨C, hC, hΦ⟩ := exists_stripDecay_arcSpectrum μ
  let Φ := arcSpectrum μ
  let Ψ : ℂ → ℂ := fun z => Φ z * Φ (-z)
  let u : ℝ → ℂ := fun x => (stripTest Ψ x : ℂ)
  have hε : 0 < 2 * xiShiftedGammaRate := mul_pos (by norm_num) xiShiftedGammaRate_pos
  have hΨ : StripDecay Ψ (501 / 1000) (2 * xiShiftedGammaRate) (C ^ 2) :=
    stripDecay_reflectionProduct (by norm_num) hΦ
  have heven (z : ℂ) : Ψ (-z) = Ψ z := by dsimp only [Ψ]; rw [neg_neg, mul_comm]
  have hsym (r : ℝ) : Ψ (-(r : ℂ)) = conj (Ψ r) := by
    have hr : Ψ r = (‖Φ r‖ ^ 2 : ℝ) := by
      dsimp only [Ψ, Φ]
      rw [arcSpectrum_neg_ofReal, Complex.ofReal_pow, Complex.mul_conj']
    rw [heven, hr, Complex.conj_ofReal]
  have hu : Continuous u := Complex.continuous_ofReal.comp
    (continuous_stripTest (by norm_num) hε hΨ)
  have hcorr (x : ℝ) : stripTest Ψ x = crossCorr (stripTest Φ) (stripTest Φ) x :=
    stripTest_reflectionProduct (by norm_num) xiShiftedGammaRate_pos hΦ (arcSpectrum_neg_ofReal μ) x
  have htransform {z : ℂ} (hz : |z.im| < 501 / 1000) : sourceTransform u z = Ψ z := by
    have h := paperFT_stripTest (Φ := Ψ) (by norm_num) hε hΨ hsym
      (z := -z) (by simpa using hz)
    have heq : sourceTransform u z = Zeta23.paperFT u (-z) := by
      unfold sourceTransform Zeta23.paperFT
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show I * (-z) * (x : ℂ) = -I * z * x by ring]
      exact mul_comm _ _
    rw [heq, h, heven]
  have hfac {z : ℂ} (hz : |z.im| < 501 / 1000) :
      Ψ z = XiC z ^ 2 * arcSpectralMultiplier (μ : Measure ArcParam) z := by
    dsimp only [Ψ, Φ, arcSpectrum]
    rw [XiC_even, arcRoot_even, ← arcRoot_sq μ hz.le]
    ring
  have hdiv (z : ℂ) : analyticOrderAt (fun z => XiC z ^ 2) z ≤
      analyticOrderAt (sourceTransform u) z := by
    have hXiA : AnalyticAt ℂ (fun w => XiC w ^ 2) z := (XiC_differentiable.analyticAt z).pow 2
    by_cases hz : XiC z = 0
    · have hz' : |z.im| < 501 / 1000 := by linarith only [abs_im_lt_half_of_XiC_zero hz]
      have hopen : IsOpen {w : ℂ | |w.im| < 501 / 1000} :=
        isOpen_lt Complex.continuous_im.abs continuous_const
      have hEq : sourceTransform u =ᶠ[𝓝 z]
          (fun w => XiC w ^ 2 * arcSpectralMultiplier (μ : Measure ArcParam) w) := by
        filter_upwards [hopen.mem_nhds hz'] with w hw
        exact (htransform hw).trans (hfac hw)
      have hR : AnalyticAt ℂ (arcSpectralMultiplier (μ : Measure ArcParam)) z := by
        have hd : DifferentiableOn ℂ (arcSpectralMultiplier (μ : Measure ArcParam))
            {w : ℂ | |w.im| < 501 / 1000} := fun w hw =>
          (differentiableAt_arcSpectralMultiplier _
            (lt_trans (show |w.im| < 501 / 1000 from hw) (by norm_num))).differentiableWithinAt
        exact hd.analyticAt (hopen.mem_nhds hz')
      rw [analyticOrderAt_congr hEq]
      change analyticOrderAt (fun w => XiC w ^ 2) z ≤
        analyticOrderAt ((fun w => XiC w ^ 2) * arcSpectralMultiplier (μ : Measure ArcParam)) z
      rw [analyticOrderAt_mul hXiA hR]
      exact le_self_add
    · rw [hXiA.analyticOrderAt_eq_zero.mpr (pow_ne_zero _ hz)]
      exact zero_le _
  have hzero := ae_eq_zero_of_doubleExp_XiC_pow_divisor hu.aestronglyMeasurable ha
    (by linarith : 0 < b) (k := 2) (by norm_num; linarith) (C := M)
    (fun x => by simpa only [u, Complex.norm_real, Real.norm_eq_abs, hcorr, Φ] using hbound x) hdiv
  have hH0 : sourceTransform u 0 = 0 := by
    unfold sourceTransform
    calc (∫ x : ℝ, cexp (-I * 0 * x) * u x) = ∫ _ : ℝ, (0 : ℂ) := by
          apply integral_congr_ae
          filter_upwards [hzero] with x hx
          simp only [hx, Pi.zero_apply, mul_zero]
      _ = 0 := integral_zero _ _
  have hΦ0 : Φ 0 ≠ 0 := mul_ne_zero XiC_zero_ne (arcRoot_ofReal_ne_zero μ 0)
  have hΨ0 : Ψ 0 ≠ 0 := by
    dsimp only [Ψ]
    rw [neg_zero]
    exact mul_ne_zero hΦ0 hΦ0
  exact hΨ0 ((htransform (z := 0) (by norm_num)).symm.trans hH0)

/-- The named blind test attains, and cannot exceed, double-exponential exponent one. -/
theorem exactExtremalTest_sharp_correlation_tail :
    (∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ x : ℝ,
      |crossCorr exactExtremalTest exactExtremalTest x| ≤ C * Real.exp (-a * Real.exp |x|)) ∧
    (∀ a b M : ℝ, 0 < a → 1 < b → ¬ ∀ x : ℝ,
      |crossCorr exactExtremalTest exactExtremalTest x| ≤
        M * Real.exp (-a * Real.exp (b * |x|))) :=
  ⟨exists_doubleExp_crossCorr_arcSpectrum_bound blindArcMeasure,
    fun _ _ _ ha hb => not_faster_crossCorr_arcSpectrum blindArcMeasure ha hb⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal
