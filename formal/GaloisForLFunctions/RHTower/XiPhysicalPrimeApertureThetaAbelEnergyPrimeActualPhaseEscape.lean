import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeD2PhaseRigidity

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Abstract two-edge exponential mode in a real translation parameter. -/
def twoEdgeExponentialMode (w P Q : ℂ) (a : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * w) * P + Complex.exp (-(a : ℂ) * w) * Q

theorem complex_exp_ne_exp_neg_of_re_ne_zero
    {w : ℂ} (hwre : w.re ≠ 0) :
    Complex.exp w ≠ Complex.exp (-w) := by
  intro h
  have hn := congrArg norm h
  rw [Complex.norm_exp, Complex.norm_exp] at hn
  have hre : w.re = (-w).re := Real.exp_injective hn
  simp only [neg_re] at hre
  exact hwre (by linarith)

theorem twoEdgeExponentialMode_add_sub
    (w P Q : ℂ) (a h : ℝ) :
    twoEdgeExponentialMode w P Q (a + h) +
        twoEdgeExponentialMode w P Q (a - h) =
      (Complex.exp ((h : ℂ) * w) + Complex.exp (-(h : ℂ) * w)) *
        twoEdgeExponentialMode w P Q a := by
  have hpp : (((a + h : ℝ) : ℂ) * w) =
      (a : ℂ) * w + (h : ℂ) * w := by push_cast; ring
  have hpn : (-((a + h : ℝ) : ℂ)) * w =
      -(a : ℂ) * w + -(h : ℂ) * w := by push_cast; ring
  have hmp : (((a - h : ℝ) : ℂ) * w) =
      (a : ℂ) * w + -(h : ℂ) * w := by push_cast; ring
  have hmn : (-((a - h : ℝ) : ℂ)) * w =
      -(a : ℂ) * w + (h : ℂ) * w := by push_cast; ring
  rw [twoEdgeExponentialMode, twoEdgeExponentialMode,
    twoEdgeExponentialMode, hpp, hpn, hmp, hmn]
  simp only [Complex.exp_add]
  ring

theorem twoEdgeExponentialMode_ne_zero_or_succ
    {w P Q : ℂ} (hwre : w.re ≠ 0) (hP : P ≠ 0) (b : ℝ) :
    twoEdgeExponentialMode w P Q b ≠ 0 ∨
      twoEdgeExponentialMode w P Q (b + 1) ≠ 0 := by
  by_cases hb : twoEdgeExponentialMode w P Q b = 0
  · right
    have hbp : ((((b + 1 : ℝ) : ℂ) * w)) = (b : ℂ) * w + w := by
      push_cast
      ring
    have hbn : (-((b + 1 : ℝ) : ℂ)) * w = -(b : ℂ) * w + -w := by
      push_cast
      ring
    let X : ℂ := Complex.exp ((b : ℂ) * w) * P
    let Y : ℂ := Complex.exp (-(b : ℂ) * w) * Q
    have hXY : X + Y = 0 := by simpa [X, Y, twoEdgeExponentialMode] using hb
    have hY : Y = -X := by linear_combination hXY
    have hsucc : twoEdgeExponentialMode w P Q (b + 1) =
        (Complex.exp w - Complex.exp (-w)) * X := by
      rw [twoEdgeExponentialMode, hbp, hbn]
      simp only [Complex.exp_add]
      calc
        Complex.exp ((b : ℂ) * w) * Complex.exp w * P +
            Complex.exp (-(b : ℂ) * w) * Complex.exp (-w) * Q =
            Complex.exp w * X + Complex.exp (-w) * Y := by
              dsimp only [X, Y]
              ring
        _ = (Complex.exp w - Complex.exp (-w)) * X := by
              rw [hY]
              ring
    rw [hsucc]
    exact mul_ne_zero
      (sub_ne_zero.mpr (complex_exp_ne_exp_neg_of_re_ne_zero hwre))
      (mul_ne_zero (Complex.exp_ne_zero _) hP)
  · exact Or.inl hb

/-- Canonical phase step: its imaginary displacement is exactly one half. -/
def offAxisPhaseStep (w : ℂ) : ℝ :=
  1 / (2 * w.im)

theorem offAxisPhaseStep_mul_im {w : ℂ} (hwim : w.im ≠ 0) :
    (((offAxisPhaseStep w : ℝ) : ℂ) * w).im = 1 / 2 := by
  simp only [offAxisPhaseStep, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  field_simp

theorem exp_phaseStep_add_exp_neg_phaseStep_im_ne_zero
    {w : ℂ} (hwre : w.re ≠ 0) (hwim : w.im ≠ 0) :
    (Complex.exp (((offAxisPhaseStep w : ℝ) : ℂ) * w) +
      Complex.exp (-(((offAxisPhaseStep w : ℝ) : ℂ) * w))).im ≠ 0 := by
  let h : ℝ := offAxisPhaseStep w
  have hne : h ≠ 0 := by
    dsimp [h, offAxisPhaseStep]
    exact one_div_ne_zero (mul_ne_zero (by norm_num) hwim)
  have hxne : h * w.re ≠ 0 := mul_ne_zero hne hwre
  have him : (((h : ℝ) : ℂ) * w).im = 1 / 2 :=
    offAxisPhaseStep_mul_im hwim
  have hre : (((h : ℝ) : ℂ) * w).re = h * w.re := by
    simp [Complex.mul_re]
  have hsin : Real.sin (1 / 2) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by norm_num)
      (by nlinarith [Real.pi_gt_three])
  change (Complex.exp ((h : ℂ) * w) +
    Complex.exp (-((h : ℂ) * w))).im ≠ 0
  simp only [Complex.add_im, Complex.exp_im, Complex.neg_re, Complex.neg_im,
    hre, him, Real.sin_neg]
  rw [show Real.exp (h * w.re) * Real.sin (1 / 2) +
      Real.exp (-(h * w.re)) * -Real.sin (1 / 2) =
      (Real.exp (h * w.re) - Real.exp (-(h * w.re))) * Real.sin (1 / 2) by ring]
  exact mul_ne_zero (sub_ne_zero.mpr (by
    intro heq
    have he := Real.exp_injective heq
    exact hxne (by linarith))) hsin

/-- Two nonzero off-axis exponential edges cannot stay real at all late translations. -/
theorem twoEdgeExponentialMode_cofinally_nonreal
    {w P Q : ℂ} (hwre : w.re ≠ 0) (hwim : w.im ≠ 0)
    (hP : P ≠ 0) :
    ∀ R : ℝ, ∃ a : ℝ, R ≤ a ∧ (twoEdgeExponentialMode w P Q a).im ≠ 0 := by
  intro R
  by_contra hescape
  push Not at hescape
  let h : ℝ := offAxisPhaseStep w
  let b : ℝ := max R 0 + |h| + 1
  have hbR : R ≤ b := by
    dsimp [b]
    have := le_max_left R 0
    linarith [abs_nonneg h]
  have hbsubR : R ≤ b - h := by
    dsimp [b]
    have := le_max_left R 0
    linarith [le_abs_self h]
  have hbaddR : R ≤ b + h := by
    dsimp [b]
    have := le_max_left R 0
    linarith [neg_le_abs h]
  have hb1R : R ≤ b + 1 := by linarith
  obtain hbnz | hb1nz := twoEdgeExponentialMode_ne_zero_or_succ hwre hP b
  · have hreal := hescape b hbR
    have hrealSub := hescape (b - h) hbsubR
    have hrealAdd := hescape (b + h) hbaddR
    have hpair := twoEdgeExponentialMode_add_sub w P Q b h
    have himPair := congrArg Complex.im hpair
    simp only [Complex.add_im, hrealAdd, hrealSub, add_zero, Complex.mul_im,
      hreal, mul_zero, zero_add] at himPair
    have hprod :
        (Complex.exp ((h : ℂ) * w) + Complex.exp (-((h : ℂ) * w))).im *
          (twoEdgeExponentialMode w P Q b).re = 0 := by
      simpa [Complex.add_im] using himPair.symm
    exact (mul_ne_zero
      (exp_phaseStep_add_exp_neg_phaseStep_im_ne_zero hwre hwim)
      (by
        intro hre0
        apply hbnz
        apply Complex.ext
        · exact hre0
        · exact hreal)) hprod
  · have hb1subR : R ≤ (b + 1) - h := by linarith
    have hb1addR : R ≤ (b + 1) + h := by linarith
    have hreal := hescape (b + 1) hb1R
    have hrealSub := hescape ((b + 1) - h) hb1subR
    have hrealAdd := hescape ((b + 1) + h) hb1addR
    have hpair := twoEdgeExponentialMode_add_sub w P Q (b + 1) h
    have himPair := congrArg Complex.im hpair
    simp only [Complex.add_im, hrealAdd, hrealSub, add_zero, Complex.mul_im,
      hreal, mul_zero, zero_add] at himPair
    have hprod :
        (Complex.exp ((h : ℂ) * w) + Complex.exp (-((h : ℂ) * w))).im *
          (twoEdgeExponentialMode w P Q (b + 1)).re = 0 := by
      simpa [Complex.add_im] using himPair.symm
    exact (mul_ne_zero
      (exp_phaseStep_add_exp_neg_phaseStep_im_ne_zero hwre hwim)
      (by
        intro hre0
        apply hb1nz
        apply Complex.ext
        · exact hre0
        · exact hreal)) hprod

/-- The physical one-edge amplitude has no zero anywhere in the centered open strip,
away from the critical line. -/
theorem xiPhysicalThetaAbelEntireModeAmplitude_ne_zero_of_openStrip
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {w : ℂ} (hlower : -1 / 2 < w.re) (hupper : w.re < 1 / 2)
    (hwre : w.re ≠ 0) :
    xiPhysicalThetaAbelEntireModeAmplitude L A c w ≠ 0 := by
  rw [xiPhysicalThetaAbelEntireModeAmplitude]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · by_cases hpos : 0 < w.re
    · exact rectangularWindowAmplitude_ne_zero hL hpos
    · exact rectangularWindowAmplitude_ne_zero_of_re_neg hL
        (lt_of_le_of_ne (le_of_not_gt hpos) hwre)
  · intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  · exact rectangularWindowAmplitude_ne_zero hc (by
      norm_num
      linarith)
  · exact rectangularWindowAmplitude_ne_zero_of_re_neg hA (by
      norm_num
      linarith)

theorem I_mul_primeFluxContourCoordinate (s : ℂ) :
    I * primeFluxContourCoordinate s = s - 1 / 2 := by
  rw [primeFluxContourCoordinate]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_eq_twoEdgeExponentialMode
    (L A c a : ℝ) (s : ℂ) :
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a s =
      twoEdgeExponentialMode (I * s)
        (xiPhysicalThetaAbelEntireModeAmplitude L A c (I * s))
        (xiPhysicalThetaAbelEntireModeAmplitude L A c (-(I * s))) a := by
  rfl

/-- At every D2 contour point, the actual physical two-edge transform has nonreal
phase beyond every real translation bound. -/
theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_cofinally_nonreal_at_gaussianRatD2
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {q : ℚ × ℚ}
    (hre : 0 < (gaussianRatPoint q).re)
    (hhalf : (gaussianRatPoint q).re < 1 / 2)
    (hhigh : 233 / 20 < (gaussianRatPoint q).im) :
    ∀ R : ℝ, ∃ a : ℝ, R ≤ a ∧
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
        (primeFluxContourCoordinate (gaussianRatPoint q))).im ≠ 0 := by
  let s : ℂ := gaussianRatPoint q
  let z : ℂ := primeFluxContourCoordinate s
  let w : ℂ := s - 1 / 2
  have hwz : I * z = w := by
    dsimp only [z, w]
    exact I_mul_primeFluxContourCoordinate s
  have hwre_eq : w.re = s.re - 1 / 2 := by
    simp [w]
  have hwim_eq : w.im = s.im := by
    simp [w]
  have hwre : w.re ≠ 0 := by
    rw [hwre_eq]
    dsimp only [s]
    linarith
  have hwim : w.im ≠ 0 := by
    rw [hwim_eq]
    dsimp only [s]
    linarith
  have hlower : -1 / 2 < w.re := by
    rw [hwre_eq]
    dsimp only [s]
    linarith
  have hupper : w.re < 1 / 2 := by
    rw [hwre_eq]
    dsimp only [s]
    linarith
  have hP : xiPhysicalThetaAbelEntireModeAmplitude L A c w ≠ 0 :=
    xiPhysicalThetaAbelEntireModeAmplitude_ne_zero_of_openStrip
      hL hA hc hlower hupper hwre
  intro R
  obtain ⟨a, haR, haim⟩ :=
    twoEdgeExponentialMode_cofinally_nonreal hwre hwim hP R
  refine ⟨a, haR, ?_⟩
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform_eq_twoEdgeExponentialMode,
    hwz]
  exact haim

/-- Consequently, actual squared physical weights fail universal real-part
monotonicity cofinally in translation at every D2 point. -/
theorem physicalTwoEdgeSquare_cofinally_not_realPartMonotone_at_gaussianRatD2
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {q : ℚ × ℚ}
    (hre : 0 < (gaussianRatPoint q).re)
    (hhalf : (gaussianRatPoint q).re < 1 / 2)
    (hhigh : 233 / 20 < (gaussianRatPoint q).im) :
    ∀ R : ℝ, ∃ a : ℝ, R ≤ a ∧
      ¬ ComplexRealPartMonotoneMultiplier
        (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a
          (primeFluxContourCoordinate (gaussianRatPoint q)) ^ 2) := by
  intro R
  obtain ⟨a, haR, haim⟩ :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_cofinally_nonreal_at_gaussianRatD2
      hL hA hc hre hhalf hhigh R
  refine ⟨a, haR, ?_⟩
  rw [physicalTwoEdgeSquare_realPartMonotone_iff_realPhase]
  exact haim

end

end RHTower
