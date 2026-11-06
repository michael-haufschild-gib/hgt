import GaloisForLFunctions.BiScaleUncertainty.ExactExtremal.ArcSquareRoot
import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof

/-!
# A single exact Xi-divisible blind test

The annihilating arc measure defines a positive spectral mixture. Its analytic
square root gives one real exponentially decaying test, with exactly the same
autocorrelation at every lag. Every integer logarithm is a blind node, and the
pole-archimedean energy vanishes.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Nat ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty.ExactExtremal

open _root_.RHTower _root_.RHTower.WeilSpectral

noncomputable section

/-- The cosine pairing of the single spectrum equals the weighted family pairing. -/
theorem integral_arcSpectrum_cos (μ : ProbabilityMeasure ArcParam) (x : ℝ) :
    (∫ t : ℝ, ‖arcSpectrum μ t‖ ^ 2 * Real.cos (t * x)) =
      ∑' j, arcSpectralWeight (μ : Measure ArcParam) j *
        ∫ t : ℝ, ‖xiShiftedGamma j t‖ ^ 2 * Real.cos (t * x) := by
  let w := arcSpectralWeight (μ : Measure ArcParam)
  have hw := arcSpectralWeight_nonneg (μ : Measure ArcParam)
  have hsum := summable_arcSpectralWeight (μ : Measure ArcParam)
  obtain ⟨K, hK0, hK⟩ := exists_stripDecay_xiShiftedGamma
  let ε := xiShiftedGammaRate
  have hε : 0 < ε := xiShiftedGammaRate_pos
  have he1 (t : ℝ) : Real.exp (-(ε * |t|)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε.le (abs_nonneg t)))
  have hΦc : ∀ j, Continuous fun t : ℝ => xiShiftedGamma j t := fun j =>
    continuous_iff_continuousAt.mpr fun t =>
      ((hK j).diff (t : ℂ) (by norm_num)).continuousAt.comp Complex.continuous_ofReal.continuousAt
  have hterm (j : ℕ) (t : ℝ) : w j * ‖xiShiftedGamma j t‖ ^ 2 ≤
      K ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) * Real.exp (-(ε * |t|)) := by
    have hΦ : ‖xiShiftedGamma j t‖ ≤ K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (-(ε * |t|)) := by
      simpa using (hK j).bound (t : ℂ) (by norm_num)
    have hsq : ‖xiShiftedGamma j t‖ ^ 2 ≤
        (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|)) := by
      calc
        ‖xiShiftedGamma j t‖ ^ 2 ≤
            (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (-(ε * |t|))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hΦ 2
        _ = (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|)) *
            Real.exp (-(ε * |t|)) := by ring
        _ ≤ (K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|)) * 1 :=
          mul_le_mul_of_nonneg_left (he1 t) (by positivity)
        _ = _ := mul_one _
    calc
      w j * ‖xiShiftedGamma j t‖ ^ 2 ≤
          w j * ((K * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) ^ 2 * Real.exp (-(ε * |t|))) :=
        mul_le_mul_of_nonneg_left hsq (hw j)
      _ = _ := by ring
  let F : ℕ → ℝ → ℝ := fun j t => w j * (‖xiShiftedGamma j t‖ ^ 2 * Real.cos (t * x))
  have hFb (j : ℕ) (t : ℝ) : ‖F j t‖ ≤
      K ^ 2 * (w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2) * Real.exp (-(ε * |t|)) := by
    simp only [F, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (hw j), abs_of_nonneg (sq_nonneg _)]
    calc
      w j * (‖xiShiftedGamma j t‖ ^ 2 * |Real.cos (t * x)|) ≤
          w j * (‖xiShiftedGamma j t‖ ^ 2 * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)) (hw j)
      _ ≤ _ := by rw [mul_one]; exact hterm j t
  have hFint (j : ℕ) : Integrable (F j) :=
    ((integrable_rexp_neg_mul_abs hε).const_mul _).mono'
      (continuous_const.mul (((hΦc j).norm.pow 2).mul (by fun_prop))).aestronglyMeasurable
      (Eventually.of_forall fun t => hFb j t)
  have hFsum : Summable fun j => ∫ t, ‖F j t‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _)
      (fun j => ?_) ((hsum.mul_left (K ^ 2)).mul_right (∫ t, Real.exp (-(ε * |t|))))
    rw [← integral_const_mul]
    exact integral_mono (hFint j).norm ((integrable_rexp_neg_mul_abs hε).const_mul _) (hFb j)
  have hSF (t : ℝ) : (∑' j, F j t) = ‖arcSpectrum μ t‖ ^ 2 * Real.cos (t * x) := by
    rw [norm_arcSpectrum_sq, ← tsum_mul_right]
    apply tsum_congr
    intro j
    dsimp only [F, w]
    ring
  calc
    (∫ t : ℝ, ‖arcSpectrum μ t‖ ^ 2 * Real.cos (t * x)) = ∫ t, ∑' j, F j t := by
      simp_rw [hSF]
    _ = ∑' j, ∫ t, F j t := (integral_tsum_of_summable_integral_norm hFint hFsum).symm
    _ = _ := tsum_congr fun j => by dsimp only [F, w]; rw [integral_const_mul]

/-- The scalar test preserves the entire autocorrelation of every positive arc mixture. -/
theorem crossCorr_arcSpectrum (μ : ProbabilityMeasure ArcParam) (x : ℝ) :
    crossCorr (stripTest (arcSpectrum μ)) (stripTest (arcSpectrum μ)) x =
      ∑' j, arcSpectralWeight (μ : Measure ArcParam) j *
        crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) x := by
  obtain ⟨C, hC, hΦ⟩ := exists_stripDecay_arcSpectrum μ
  rw [crossCorr_stripTest (by norm_num) xiShiftedGammaRate_pos hΦ (arcSpectrum_neg_ofReal μ),
    integral_arcSpectrum_cos]
  simp_rw [crossCorr_xiShiftedGammaTest]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- The selected probability measure annihilates every twisted integer moment. -/
def blindArcMeasure : ProbabilityMeasure ArcParam :=
  Classical.choose (exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds)

theorem blindArcMeasure_annihilates (n : ℕ) :
    (∫ u, twArcMoment n u ∂(blindArcMeasure : Measure ArcParam)) = 0 :=
  Classical.choose_spec (exists_probabilityMeasure_twArc_annihilating twistedArcMinimumPrinciple_holds) n

def exactExtremalSpectrum : ℂ → ℂ := arcSpectrum blindArcMeasure

def exactExtremalTest : ℝ → ℝ := stripTest exactExtremalSpectrum

/-- Fourier inversion identifies the constructed test throughout the open strip. -/
theorem paperFT_exactExtremalTest {z : ℂ} (hz : |z.im| < 501 / 1000) :
    Zeta23.paperFT (fun u => (exactExtremalTest u : ℂ)) z = exactExtremalSpectrum z := by
  obtain ⟨C, hC, hΦ⟩ := exists_stripDecay_arcSpectrum blindArcMeasure
  exact paperFT_stripTest (by norm_num) xiShiftedGammaRate_pos hΦ
    (arcSpectrum_neg_ofReal blindArcMeasure) hz

/-- The constructed spectrum has precisely Xi's real zero set. -/
theorem exactExtremalSpectrum_real_zero_iff (r : ℝ) :
    exactExtremalSpectrum r = 0 ↔ XiC r = 0 := by
  change XiC r * arcRoot blindArcMeasure r = 0 ↔ XiC r = 0
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_right (arcRoot_ofReal_ne_zero blindArcMeasure r)
  · intro h
    rw [h, zero_mul]

/-- The factor adds no zeros throughout the open strip, including off the real axis. -/
theorem paperFT_exactExtremalTest_zero_iff {z : ℂ} (hz : |z.im| < 501 / 1000) :
    Zeta23.paperFT (fun u => (exactExtremalTest u : ℂ)) z = 0 ↔ XiC z = 0 := by
  rw [paperFT_exactExtremalTest hz]
  exact arcSpectrum_eq_zero_iff blindArcMeasure hz.le

theorem paperFT_exactExtremalTest_real_zero_iff (r : ℝ) :
    Zeta23.paperFT (fun u => (exactExtremalTest u : ℂ)) r = 0 ↔ XiC r = 0 := by
  rw [paperFT_exactExtremalTest (by norm_num)]
  exact exactExtremalSpectrum_real_zero_iff r

theorem exactExtremalSpectrum_blind (n : ℕ) (hn : 2 ≤ n) :
    (∫ t : ℝ, ‖exactExtremalSpectrum t‖ ^ 2 * Real.cos (t * Real.log n)) = 0 := by
  rw [exactExtremalSpectrum, integral_arcSpectrum_cos]
  exact shiftedGamma_blind_of_twistedArc (ν := (blindArcMeasure : Measure ArcParam))
    (g := fun _ => 1) (B := 1) measurable_const (fun _ => by norm_num)
    (fun k => by simpa using blindArcMeasure_annihilates k)
    (twArcEvenMoment_one_nonneg' _) n hn

/-- A single, unconditional Xi-divisible test is blind at every integer logarithm. -/
theorem xiDivisibleBlindTest_exactExtremalTest : XiDivisibleBlindTest exactExtremalTest := by
  obtain ⟨C, hC, hΦ⟩ := exists_stripDecay_arcSpectrum blindArcMeasure
  exact xiDivisibleBlindTest_stripTest (by norm_num) xiShiftedGammaRate_pos hΦ
    (arcSpectrum_neg_ofReal blindArcMeasure) (g := arcRoot blindArcMeasure)
    (fun z _ => rfl) (arcRoot_ofReal_ne_zero blindArcMeasure) exactExtremalSpectrum_blind

theorem exactExtremalTest_ne_zero : exactExtremalTest ≠ 0 := by
  have hFT := paperFT_exactExtremalTest (z := 0) (by norm_num)
  have hXi : XiC 0 ≠ 0 := by
    have he := XiC_I_mul (0 : ℝ)
    simp only [Complex.ofReal_zero, mul_zero] at he
    rw [he]
    exact_mod_cast (thetaSourceLaplace_pos 0).ne'
  have hne : arcSpectrum blindArcMeasure 0 ≠ 0 :=
    mul_ne_zero hXi (arcRoot_ofReal_ne_zero blindArcMeasure 0)
  intro hzero
  have hzFT : Zeta23.paperFT (fun u => (exactExtremalTest u : ℂ)) 0 = 0 := by
    rw [hzero]
    simp [Zeta23.paperFT]
  exact hne (hFT.symm.trans hzFT)

theorem exactExtremalTest_null : archPoleEnergy exactExtremalTest = 0 :=
  archPoleEnergy_eq_zero_of_xiDivisibleBlindTest xiDivisibleBlindTest_exactExtremalTest

/-- The exact blind null ray is nonempty, without a positivity or RH premise. -/
theorem exists_nonzero_xiDivisible_blind_null_test :
    ∃ F : ℝ → ℝ, F ≠ 0 ∧ XiDivisibleBlindTest F ∧ archPoleEnergy F = 0 :=
  ⟨exactExtremalTest, exactExtremalTest_ne_zero,
    xiDivisibleBlindTest_exactExtremalTest, exactExtremalTest_null⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ExactExtremal
