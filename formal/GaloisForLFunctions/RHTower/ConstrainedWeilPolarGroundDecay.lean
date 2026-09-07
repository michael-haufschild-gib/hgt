import GaloisForLFunctions.RHTower.ConstrainedWeilWeightedRayBounds

/-!
# Exponential decay of the pole-vanishing ground energy under an attained top excess

Let `Θ > 0` be the largest excess `|Re ρ − ½|` over the Xi zero copies, attained at `q₀` with
ordinate `γ₀`.  The pole-vanishing derivative test `D(cos(γ₀x)ψ_a)` has screw form equal to the
`(z_q² + ¼)²`-weighted ray energy of the twisted plateau test, and its primitive `DΦ_a` is a
pole-vanishing source at every aperture above `a`.  Averaging the normalised form
`e^{−2Θa} Re Q(D(cos(γ₀x)ψ_a))` over aperture windows isolates the top copies, whose weighted constant
terms are `−(1/4) κ(Θ)² (z² + ¼)²/z²` with real part `−c_D < 0`, where

`c_D = (1/4) κ(Θ)² ((γ₀² − Θ²) + 1/2 + (γ₀² − Θ²)/(16(γ₀² + Θ²)²))`.

Hence every window `[A, A + L]` with `A ≥ ½`, `L > 4D/c_D` contains an aperture `a` with
`Re Q(D(cos(γ₀x)ψ_a)) ≤ −(c_D/2) e^{2Θa}`, so that the pole-vanishing ground energy satisfies
`μ₀(a + 1) ‖DΦ_a‖² ≤ −(c_D/2) e^{2Θa}` with `‖DΦ_a‖² ≤ 2a(|γ₀| + 4K + (2a+1)/4)²`.  Since `μ₀` is
antitone in the aperture, the conclusion is

`μ₀(B) ≤ −c' e^{2ΘB} / B³`  for every aperture `B ≥ B₀`,

with explicit `c' > 0` and `B₀`.  Together with the corpus theorem that `μ₀` has at most one zero
aperture, this locates the degeneracy threshold and gives the exact rate of decay to `−∞`.
-/

open MeasureTheory Complex Set intervalIntegral
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The weighted normalised form -/

/-- `S_w(a) = Σ'_q Re eval(w_q · P_q)(a)`. -/
def weightedTwistedForm (Θ γ a : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, (ExpPoly.eval (weightedRayPoly Θ γ q) a).re

/-- The ray energy of the twisted odd test is the twisted ray term. -/
theorem rayEnergy_twistedOddTest_eq {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) (q : XiZeroCopy) :
    suzukiTestRayCoefBar (twistedOddTest ψ γ) q * suzukiTestRayCoef (twistedOddTest ψ γ) q
        / xiSpectralPoint q ^ 2
      = twistedRayTerm ψ γ q := by
  rw [suzukiTestRayCoef_twistedOddTest, suzukiTestRayCoefBar_twistedOddTest]
  unfold twistedRayTerm
  ring

theorem summable_dWeight_mul_twistedRayTerm {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) :
    Summable fun q : XiZeroCopy => dWeight q * twistedRayTerm ψ γ q := by
  refine (summable_suzukiTestRayEnergy (twistedOddTest ψ γ).polarDerivativeTest).congr fun q => ?_
  rw [suzukiTestRayCoef_polarDerivativeTest, suzukiTestRayCoefBar_polarDerivativeTest,
    ← rayEnergy_twistedOddTest_eq]
  unfold dWeight
  ring

/-- **The screw form of the derivative test is the weighted ray energy.** -/
theorem suzukiScrewSmoothForm_polarDerivativeTest_twistedOddTest {a : ℝ} (ψ : OddSmoothProfile a)
    (γ : ℝ) :
    suzukiScrewSmoothForm (twistedOddTest ψ γ).polarDerivativeTest
        (twistedOddTest ψ γ).polarDerivativeTest
      = ∑' q : XiZeroCopy, dWeight q * twistedRayTerm ψ γ q := by
  rw [suzukiScrewSmoothForm_polarDerivativeTest]
  refine tsum_congr fun q => ?_
  rw [rayEnergy_twistedOddTest_eq]
  rfl

/-- `S_w(a) = e^{−2Θa} Re Q(D(cos(γx)ψ_a))` for `a ≥ ½`. -/
theorem weightedTwistedForm_eq {a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) (Θ γ : ℝ) :
    weightedTwistedForm Θ γ a
      = Real.exp (-(2 * Θ) * a)
        * (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ).polarDerivativeTest
            (twistedOddTest (plateauProfile a ha0) γ).polarDerivativeTest).re := by
  unfold weightedTwistedForm
  rw [suzukiScrewSmoothForm_polarDerivativeTest_twistedOddTest,
    Complex.re_tsum (summable_dWeight_mul_twistedRayTerm _ γ), ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [eval_weightedRayPoly ha ha0, cexp_neg_two_theta]
  have : dWeight q * (((Real.exp (-(2 * Θ) * a) : ℝ) : ℂ)
      * twistedRayTerm (plateauProfile a ha0) γ q)
      = ((Real.exp (-(2 * Θ) * a) : ℝ) : ℂ) * (dWeight q * twistedRayTerm (plateauProfile a ha0) γ q) := by
    ring
  rw [this, Complex.re_ofReal_mul]

/-! ## Window integrals -/

section Bounds

variable {M Θ : ℝ}

theorem continuousOn_weightedTwistedForm (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2)
    (hΘ : 0 ≤ Θ) {γ A B : ℝ} (hA : 1 / 2 ≤ A)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ContinuousOn (weightedTwistedForm Θ γ) (Icc A B) := by
  unfold weightedTwistedForm
  refine continuousOn_tsum (f := fun q a => (ExpPoly.eval (weightedRayPoly Θ γ q) a).re)
    (u := rayMajorant M Θ γ) (fun q => ?_) (summable_rayMajorant M Θ γ) ?_
  · exact (Complex.continuous_re.comp (ExpPoly.continuous_eval _)).continuousOn
  · intro q a ha
    rw [mem_Icc] at ha
    exact norm_re_eval_weightedRayPoly_le hM hMb hΘ (hA.trans ha.1) γ (hall q)

theorem integrableOn_re_eval_weighted (Θ γ : ℝ) (q : XiZeroCopy) (A B : ℝ) :
    IntegrableOn (fun a : ℝ => (ExpPoly.eval (weightedRayPoly Θ γ q) a).re) (Ioc A B) :=
  ((Complex.continuous_re.comp (ExpPoly.continuous_eval _)).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self

theorem summable_integral_norm_re_eval_weighted (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2)
    (hΘ : 0 ≤ Θ) {γ A L : ℝ} (hA : 1 / 2 ≤ A) (hL : 0 ≤ L)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    Summable fun q : XiZeroCopy =>
      ∫ a in Ioc A (A + L), ‖(ExpPoly.eval (weightedRayPoly Θ γ q) a).re‖ := by
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
    ((summable_rayMajorant M Θ γ).mul_right L)
  calc ∫ a in Ioc A (A + L), ‖(ExpPoly.eval (weightedRayPoly Θ γ q) a).re‖
      ≤ ∫ a in Ioc A (A + L), rayMajorant M Θ γ q := by
        refine setIntegral_mono_on (integrableOn_re_eval_weighted Θ γ q A (A + L)).norm
          (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
          fun a ha => ?_
        rw [mem_Ioc] at ha
        exact norm_re_eval_weightedRayPoly_le hM hMb hΘ (hA.trans ha.1.le) γ (hall q)
    _ = rayMajorant M Θ γ q * L := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith)]
        ring

theorem integral_weightedTwistedForm_eq_tsum (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2)
    (hΘ : 0 ≤ Θ) {γ A L : ℝ} (hA : 1 / 2 ≤ A) (hL : 0 ≤ L)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ∫ a in A..(A + L), weightedTwistedForm Θ γ a
      = ∑' q : XiZeroCopy, ∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re := by
  have hAB : A ≤ A + L := by linarith
  unfold weightedTwistedForm
  simp_rw [intervalIntegral.integral_of_le hAB]
  exact (integral_tsum_of_summable_integral_norm (fun q => integrableOn_re_eval_weighted Θ γ q A (A + L))
    (summable_integral_norm_re_eval_weighted hM hMb hΘ hA hL hall)).symm

theorem summable_integral_re_eval_weighted (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2)
    (hΘ : 0 ≤ Θ) {γ A L : ℝ} (hA : 1 / 2 ≤ A) (hL : 0 ≤ L)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    Summable fun q : XiZeroCopy =>
      ∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re := by
  have hAB : A ≤ A + L := by linarith
  simp_rw [intervalIntegral.integral_of_le hAB]
  exact Summable.of_norm_bounded (summable_integral_norm_re_eval_weighted hM hMb hΘ hA hL hall)
    fun q => norm_integral_le_integral_norm _

theorem integral_re_eval_weighted_le (hΘ : 0 ≤ Θ) {γ A L : ℝ} (hA : 0 ≤ A) (hL : 0 < L)
    (q : XiZeroCopy) (hq : |(xiSpectralPoint q).im| ≤ Θ) :
    ∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re
      ≤ L * (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
        + 2 * ExpPoly.decayNorm (weightedRayPoly Θ γ q) := by
  have h := ExpPoly.abs_windowMean_re_sub_le _ (decaying_weightedRayPoly hΘ γ hq) hA hL
  have h2 := (abs_le.mp h).2
  have h3 : (∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re) / L
      ≤ (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
        + 2 * ExpPoly.decayNorm (weightedRayPoly Θ γ q) / L := by linarith
  rw [div_le_iff₀ hL] at h3
  calc ∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re
      ≤ ((ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (weightedRayPoly Θ γ q) / L) * L := h3
    _ = L * (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (weightedRayPoly Θ γ q) := by
        field_simp

end Bounds

/-! ## The weighted constant terms -/

/-- The constant term of a top-centre copy, as a complex number. -/
theorem constTerm_of_mem_topCentreSet {Θ γ : ℝ} (hΘ : 0 < Θ) (hγ : γ ≠ 0)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {q : XiZeroCopy}
    (hq : q ∈ topCentreSet Θ γ) :
    ExpPoly.constTerm (normalizedRayTermPoly Θ γ q)
      = -(1 / 4 : ℂ) / xiSpectralPoint q ^ 2 * ((topKappa Θ : ℝ) : ℂ) ^ 2 := by
  have hre := xiSpectralPoint_re_ne_zero q
  rw [constTerm_normalizedRayTermPoly hΘ γ (hall q) hre, if_pos hq.1]
  have hcase : (if (xiSpectralPoint q).re - γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
      + (if (xiSpectralPoint q).re + γ = 0 then plateauKappa (Θ : ℂ) ^ 2 else 0)
      = plateauKappa (Θ : ℂ) ^ 2 := by
    rcases hq.2 with h | h
    · rw [if_pos (by rw [h]; ring), if_neg (by rw [h]; intro h0; apply hγ; linarith), add_zero]
    · rw [if_neg (by rw [h]; intro h0; apply hγ; linarith), if_pos (by rw [h]; ring), zero_add]
  rw [hcase, plateauKappa_eq_ofReal]

/-- The constant `c_D = (1/4) κ(Θ)² ((γ² − Θ²) + 1/2 + (γ² − Θ²)/(16(γ² + Θ²)²))`. -/
def topConstantD (Θ γ : ℝ) : ℝ :=
  (1 / 4) * topKappa Θ ^ 2 * ((γ ^ 2 - Θ ^ 2) + 1 / 2 + (γ ^ 2 - Θ ^ 2) / (16 * (γ ^ 2 + Θ ^ 2) ^ 2))

theorem topConstantD_pos {Θ γ : ℝ} (hΘ : 0 < Θ) (hΘ' : Θ < 1 / 2) (hγ : 9 / 2 ≤ |γ|) :
    0 < topConstantD Θ γ := by
  unfold topConstantD
  have hk := topKappa_pos hΘ
  have hγ2 : (9 / 2 : ℝ) ^ 2 ≤ γ ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hγ 2
    rwa [sq_abs] at this
  have hΘ2 : Θ ^ 2 < (1 / 2) ^ 2 := pow_lt_pow_left₀ hΘ' hΘ.le two_ne_zero
  have hnum : 0 < γ ^ 2 - Θ ^ 2 := by nlinarith
  positivity

/-- `(z² + ¼)²/z² = z² + ½ + (1/16)(z²)⁻¹`. -/
theorem dWeight_div_sq (q : XiZeroCopy) :
    dWeight q / xiSpectralPoint q ^ 2
      = xiSpectralPoint q ^ 2 + ((1 / 2 : ℝ) : ℂ) + ((1 / 16 : ℝ) : ℂ) * (xiSpectralPoint q ^ 2)⁻¹ := by
  have hz : xiSpectralPoint q ^ 2 ≠ 0 := pow_ne_zero 2 (xiSpectralPoint_ne_zero q)
  unfold dWeight
  rw [div_eq_iff hz]
  have hinv : (xiSpectralPoint q ^ 2)⁻¹ * xiSpectralPoint q ^ 2 = 1 := inv_mul_cancel₀ hz
  push_cast
  linear_combination (-(1 / 16 : ℂ)) * hinv

theorem re_sq_of_sq_eq {z : ℂ} {X Y : ℝ} (hx : z.re ^ 2 = X) (hy : z.im ^ 2 = Y) :
    (z ^ 2).re = X - Y := by
  rw [pow_two, Complex.mul_re, ← pow_two, ← pow_two, hx, hy]

/-- The real part of the weighted constant term of a top-centre copy is `−c_D`. -/
theorem re_constTerm_weighted_of_mem_topCentreSet {Θ γ : ℝ} (hΘ : 0 < Θ) (hγ : γ ≠ 0)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {q : XiZeroCopy}
    (hq : q ∈ topCentreSet Θ γ) :
    (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re = -topConstantD Θ γ := by
  rw [constTerm_weightedRayPoly, constTerm_of_mem_topCentreSet hΘ hγ hall hq]
  have hX : (xiSpectralPoint q).re ^ 2 = γ ^ 2 := by
    rcases hq.2 with h | h
    · rw [h]
    · rw [h]; ring
  have hY : (xiSpectralPoint q).im ^ 2 = Θ ^ 2 := by
    rw [← sq_abs, hq.1]
  have hform : dWeight q * (-(1 / 4 : ℂ) / xiSpectralPoint q ^ 2 * ((topKappa Θ : ℝ) : ℂ) ^ 2)
      = ((-(1 / 4) * topKappa Θ ^ 2 : ℝ) : ℂ) * (dWeight q / xiSpectralPoint q ^ 2) := by
    push_cast
    ring
  rw [hform, Complex.re_ofReal_mul, dWeight_div_sq, Complex.add_re, Complex.add_re,
    re_sq_of_sq_eq hX hY, Complex.re_ofReal_mul, re_inv_sq_of_sq_eq hX hY, Complex.ofReal_re]
  unfold topConstantD
  have hpos : 0 < γ ^ 2 + Θ ^ 2 := by
    have := abs_pos.mpr hγ
    positivity
  field_simp

theorem constTerm_weighted_eq_zero_of_not_mem_topCentreSet {Θ γ : ℝ} (hΘ : 0 < Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {q : XiZeroCopy}
    (hq : q ∉ topCentreSet Θ γ) :
    ExpPoly.constTerm (weightedRayPoly Θ γ q) = 0 := by
  rw [constTerm_weightedRayPoly, constTerm_eq_zero_of_not_mem_topCentreSet hΘ hall hq, mul_zero]

/-- **The weighted constant-term sum is at most `−c_D`.** -/
theorem tsum_re_constTerm_weighted_le {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ∑' q : XiZeroCopy, (ExpPoly.constTerm (weightedRayPoly Θ (xiSpectralPoint q₀).re q)).re
      ≤ -topConstantD Θ (xiSpectralPoint q₀).re := by
  classical
  set γ := (xiSpectralPoint q₀).re with hγdef
  have hγ : γ ≠ 0 := xiSpectralPoint_re_ne_zero q₀
  have hT := finite_topCentreSet Θ γ
  have hzero : ∀ q ∉ hT.toFinset, (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re = 0 := by
    intro q hq
    rw [hT.mem_toFinset] at hq
    rw [constTerm_weighted_eq_zero_of_not_mem_topCentreSet hΘ hall hq, Complex.zero_re]
  rw [tsum_eq_sum hzero]
  have hval : ∀ q ∈ hT.toFinset,
      (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re = -topConstantD Θ γ := by
    intro q hq
    rw [hT.mem_toFinset] at hq
    exact re_constTerm_weighted_of_mem_topCentreSet hΘ hγ hall hq
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hmem : q₀ ∈ hT.toFinset := by
    rw [hT.mem_toFinset]
    exact ⟨hq₀, Or.inl rfl⟩
  have hcard : (1 : ℝ) ≤ (hT.toFinset.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨q₀, hmem⟩
  have hΘ' : Θ < 1 / 2 := by
    rw [← hq₀]; exact abs_im_xiSpectralPoint_lt_half q₀
  have hc := topConstantD_pos hΘ hΘ' (nine_halves_le_abs_re_xiSpectralPoint q₀)
  nlinarith

/-! ## The window bound and recurrent negativity -/

/-- The weighted total decay norm. -/
def decayTotalW (Θ γ : ℝ) : ℝ := ∑' q : XiZeroCopy, ExpPoly.decayNorm (weightedRayPoly Θ γ q)

theorem decayTotalW_nonneg (Θ γ : ℝ) : 0 ≤ decayTotalW Θ γ :=
  tsum_nonneg fun _ => ExpPoly.decayNorm_nonneg _

theorem integral_weightedTwistedForm_le {M Θ : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2)
    (hΘ : 0 < Θ) (q₀ : XiZeroCopy) (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {A L : ℝ} (hA : 1 / 2 ≤ A)
    (hL : 0 < L) :
    ∫ a in A..(A + L), weightedTwistedForm Θ (xiSpectralPoint q₀).re a
      ≤ -topConstantD Θ (xiSpectralPoint q₀).re * L
        + 2 * decayTotalW Θ (xiSpectralPoint q₀).re := by
  classical
  set γ := (xiSpectralPoint q₀).re with hγdef
  rw [integral_weightedTwistedForm_eq_tsum hM hMb hΘ.le hA hL.le hall]
  have hA0 : 0 ≤ A := by linarith
  have hsumL := summable_integral_re_eval_weighted hM hMb hΘ.le (γ := γ) hA hL.le hall
  have hT := finite_topCentreSet Θ γ
  have hsumC : Summable fun q : XiZeroCopy =>
      L * (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re := by
    refine summable_of_ne_finset_zero (s := hT.toFinset) fun q hq => ?_
    rw [hT.mem_toFinset] at hq
    rw [constTerm_weighted_eq_zero_of_not_mem_topCentreSet hΘ hall hq, Complex.zero_re, mul_zero]
  have hsumD := (summable_decayNorm_weightedRayPoly hΘ hM hMb hall
    (nine_halves_le_abs_re_xiSpectralPoint q₀)).mul_left 2
  have hterm : ∀ q : XiZeroCopy,
      ∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re
        ≤ L * (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (weightedRayPoly Θ γ q) :=
    fun q => integral_re_eval_weighted_le hΘ.le hA0 hL q (hall q)
  calc ∑' q : XiZeroCopy, ∫ a in A..(A + L), (ExpPoly.eval (weightedRayPoly Θ γ q) a).re
      ≤ ∑' q : XiZeroCopy, (L * (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
          + 2 * ExpPoly.decayNorm (weightedRayPoly Θ γ q)) :=
        hsumL.tsum_le_tsum hterm (hsumC.add hsumD)
    _ = L * ∑' q : XiZeroCopy, (ExpPoly.constTerm (weightedRayPoly Θ γ q)).re
          + 2 * decayTotalW Θ γ := by
        rw [hsumC.tsum_add hsumD, tsum_mul_left, tsum_mul_left]
        rfl
    _ ≤ L * (-topConstantD Θ γ) + 2 * decayTotalW Θ γ := by
        have := tsum_re_constTerm_weighted_le hΘ q₀ hq₀ hall
        nlinarith
    _ = -topConstantD Θ γ * L + 2 * decayTotalW Θ γ := by ring

theorem exists_weightedTwistedForm_le_of_attainedTop {M Θ : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ c : ℂ, c ≠ 0 → ‖plateauKappa c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2
      ∧ ‖plateauRho c‖ ≤ M * Real.exp (|c.re| / 4) / ‖c‖ ^ 2)
    (hΘ : 0 < Θ) (q₀ : XiZeroCopy) (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) {A L : ℝ} (hA : 1 / 2 ≤ A)
    (hL : 4 * decayTotalW Θ (xiSpectralPoint q₀).re / topConstantD Θ (xiSpectralPoint q₀).re < L) :
    ∃ a ∈ Icc A (A + L),
      weightedTwistedForm Θ (xiSpectralPoint q₀).re a
        ≤ -(topConstantD Θ (xiSpectralPoint q₀).re / 2) := by
  set γ := (xiSpectralPoint q₀).re with hγdef
  have hΘ' : Θ < 1 / 2 := by
    rw [← hq₀]; exact abs_im_xiSpectralPoint_lt_half q₀
  have hc := topConstantD_pos hΘ hΘ' (nine_halves_le_abs_re_xiSpectralPoint q₀)
  have hD := decayTotalW_nonneg Θ γ
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hL
  by_contra hcon
  push Not at hcon
  have hbound := integral_weightedTwistedForm_le hM hMb hΘ q₀ hq₀ hall hA hLpos
  have hcont : ContinuousOn (weightedTwistedForm Θ γ) (Icc A (A + L)) :=
    continuousOn_weightedTwistedForm hM hMb hΘ.le hA hall
  have hmono : ∫ a in A..(A + L), (-(topConstantD Θ γ / 2))
      ≤ ∫ a in A..(A + L), weightedTwistedForm Θ γ a := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (continuous_const.intervalIntegrable _ _)
      (hcont.intervalIntegrable_of_Icc (by linarith)) fun a ha => (hcon a ha).le
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hL' : 4 * decayTotalW Θ γ < L * topConstantD Θ γ := by
    rwa [div_lt_iff₀ hc] at hL
  nlinarith

/-! ## Transfer to the pole-vanishing ground energy -/

/-- The aperture `a + 1`. -/
def apertureSucc (a : ℝ) (ha0 : 0 ≤ a) : SuzukiPositiveAperture := ⟨a + 1, by linarith⟩

/-- At an aperture where the weighted form is `≤ −c_D/2`, the ground energy at `a + 1` is at most
`−(c_D/2) e^{2Θa} / (2a(|γ| + 4K + (2a+1)/4)²)`. -/
theorem polarGroundEnergy_apertureSucc_le {Θ γ a : ℝ} (ha : 1 / 2 ≤ a) (ha0 : 0 ≤ a) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ s : ℝ, |deriv plateauEdge s| ≤ K) {c : ℝ} (hc : 0 < c)
    (hneg : weightedTwistedForm Θ γ a ≤ -(c / 2)) :
    ccmRestrictedWeilPolarGroundEnergy (apertureSucc a ha0)
      ≤ -(c / 2 * Real.exp (2 * Θ * a)) / (2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2) := by
  have hA : a < (apertureSucc a ha0).1 := by show a < a + 1; linarith
  have h1 := polarGroundEnergy_mul_le_re_smoothForm_polarDerivativeTest
    (twistedOddTest (plateauProfile a ha0) γ) (apertureSucc a ha0) hA
  have h2 := norm_sq_twistedPlateau_polarDerivativeSource_le ha0 γ (apertureSucc a ha0) hA hK0 hK
  have heq := weightedTwistedForm_eq ha ha0 Θ γ
  rw [heq] at hneg
  have hE : 0 < Real.exp (-(2 * Θ) * a) := Real.exp_pos _
  have hE2 : 0 < Real.exp (2 * Θ * a) := Real.exp_pos _
  have hprod : Real.exp (-(2 * Θ) * a) * Real.exp (2 * Θ * a) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  -- the form itself is at most `−(c/2) e^{2Θa}`
  have hform : (suzukiScrewSmoothForm (twistedOddTest (plateauProfile a ha0) γ).polarDerivativeTest
      (twistedOddTest (plateauProfile a ha0) γ).polarDerivativeTest).re
      ≤ -(c / 2 * Real.exp (2 * Θ * a)) := by
    have := mul_le_mul_of_nonneg_left hneg hE2.le
    rw [← mul_assoc, mul_comm (Real.exp (2 * Θ * a)), hprod, one_mul] at this
    linarith
  set n : ℝ := ‖ccmArchimedeanFormToAperture (apertureSucc a ha0)
    ((twistedOddTest (plateauProfile a ha0) γ).polarDerivativeSource (apertureSucc a ha0) hA).toCCMFormVector‖ ^ 2
    with hn
  set N : ℝ := 2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2 with hN
  set μ : ℝ := ccmRestrictedWeilPolarGroundEnergy (apertureSucc a ha0) with hμ
  have hn0 : 0 ≤ n := by positivity
  have hN0 : 0 < N := by
    have : 0 < |γ| + 4 * K + (2 * a + 1) / 4 := by positivity
    positivity
  have hnN : n ≤ N := h2
  have hkey : μ * n ≤ -(c / 2 * Real.exp (2 * Θ * a)) := h1.trans hform
  have hε : 0 < c / 2 * Real.exp (2 * Θ * a) := by positivity
  have hμneg : μ < 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 ≤ μ * n := mul_nonneg hcon hn0
    linarith
  have hμN : μ * N ≤ μ * n := by nlinarith
  rw [le_div_iff₀ hN0]
  linarith

/-- **Exponential decay of the pole-vanishing ground energy.**  If the largest excess `Θ` is
attained, there are `c' > 0` and `B₀` such that `μ₀(B) ≤ −c' e^{2ΘB} / B³` for every aperture
`B ≥ B₀`. -/
theorem polarGroundEnergy_le_neg_exp_of_attainedTop {Θ : ℝ} (hΘ : 0 < Θ) (q₀ : XiZeroCopy)
    (hq₀ : |(xiSpectralPoint q₀).im| = Θ)
    (hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Θ) :
    ∃ c' : ℝ, 0 < c' ∧ ∃ B₀ : ℝ, 1 ≤ B₀ ∧ ∀ B : SuzukiPositiveAperture, B₀ ≤ B.1 →
      ccmRestrictedWeilPolarGroundEnergy B ≤ -(c' * Real.exp (2 * Θ * B.1)) / B.1 ^ 3 := by
  obtain ⟨M, hM, hMb⟩ := exists_plateau_coeff_bound₂
  obtain ⟨K, hK0, hK⟩ := exists_plateauEdge_deriv_global_bound
  set γ := (xiSpectralPoint q₀).re with hγdef
  have hΘ' : Θ < 1 / 2 := by
    rw [← hq₀]; exact abs_im_xiSpectralPoint_lt_half q₀
  have hc := topConstantD_pos hΘ hΘ' (nine_halves_le_abs_re_xiSpectralPoint q₀)
  have hD := decayTotalW_nonneg Θ γ
  set c := topConstantD Θ γ with hcdef
  set L₀ : ℝ := 4 * decayTotalW Θ γ / c + 1 with hL₀
  have hL₀pos : 0 < L₀ := by positivity
  set G : ℝ := |γ| + 4 * K + 1 with hG
  have hG1 : 1 ≤ G := by
    have := abs_nonneg γ
    linarith
  refine ⟨c / 2 * Real.exp (-(2 * Θ) * (1 + L₀)) / (2 * G ^ 2), by positivity,
    3 / 2 + L₀, by linarith, fun B hB => ?_⟩
  -- the window `[B − 1 − L₀, B − 1]`
  set A : ℝ := B.1 - 1 - L₀ with hA
  have hA12 : 1 / 2 ≤ A := by rw [hA]; linarith
  obtain ⟨a, ha, hle⟩ := exists_weightedTwistedForm_le_of_attainedTop hM hMb hΘ q₀ hq₀ hall hA12
    (show 4 * decayTotalW Θ γ / c < L₀ by rw [hL₀]; linarith)
  have ha12 : 1 / 2 ≤ a := hA12.trans ha.1
  have ha0 : 0 ≤ a := by linarith
  have haB : a + 1 ≤ B.1 := by
    have := ha.2
    rw [hA] at this
    linarith
  have hmono := ccmRestrictedWeilPolarGroundEnergy_antitone (a := apertureSucc a ha0) (b := B)
    (by show a + 1 ≤ B.1; exact haB)
  have hstep := polarGroundEnergy_apertureSucc_le (Θ := Θ) (γ := γ) ha12 ha0 hK0 hK hc hle
  refine hmono.trans (hstep.trans ?_)
  -- compare the two negative bounds
  have hB1 : 1 ≤ B.1 := by linarith
  have haB' : a ≤ B.1 := by linarith
  have hexp : Real.exp (-(2 * Θ) * (1 + L₀)) * Real.exp (2 * Θ * B.1) ≤ Real.exp (2 * Θ * a) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : A ≤ a := ha.1
    rw [hA] at this
    nlinarith
  have hNle : 2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2 ≤ 2 * G ^ 2 * B.1 ^ 3 := by
    have h1 : |γ| + 4 * K + (2 * a + 1) / 4 ≤ G * B.1 := by
      rw [hG]
      have := abs_nonneg γ
      nlinarith
    have h0 : 0 ≤ |γ| + 4 * K + (2 * a + 1) / 4 := by positivity
    have h2 : (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2 ≤ (G * B.1) ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc 2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2
        ≤ 2 * B.1 * (G * B.1) ^ 2 := by gcongr
      _ = 2 * G ^ 2 * B.1 ^ 3 := by ring
  have hNpos : 0 < 2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2 := by
    have : 0 < |γ| + 4 * K + (2 * a + 1) / 4 := by positivity
    positivity
  have hBpos : 0 < B.1 := B.2
  have hX : 0 < c / 2 * Real.exp (2 * Θ * a) := by positivity
  have hX' : c / 2 * Real.exp (-(2 * Θ) * (1 + L₀)) * Real.exp (2 * Θ * B.1)
      ≤ c / 2 * Real.exp (2 * Θ * a) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hX'pos : 0 < c / 2 * Real.exp (-(2 * Θ) * (1 + L₀)) * Real.exp (2 * Θ * B.1) := by
    positivity
  -- `−X/N ≤ −X'/N ≤ −X'/N'` for `X' ≤ X`, `N ≤ N'`
  rw [neg_div, neg_div, neg_le_neg_iff]
  calc c / 2 * Real.exp (-(2 * Θ) * (1 + L₀)) / (2 * G ^ 2) * Real.exp (2 * Θ * B.1) / B.1 ^ 3
      = (c / 2 * Real.exp (-(2 * Θ) * (1 + L₀)) * Real.exp (2 * Θ * B.1)) / (2 * G ^ 2 * B.1 ^ 3) := by
        field_simp
    _ ≤ (c / 2 * Real.exp (-(2 * Θ) * (1 + L₀)) * Real.exp (2 * Θ * B.1))
          / (2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2) :=
        div_le_div_of_nonneg_left hX'pos.le hNpos hNle
    _ ≤ (c / 2 * Real.exp (2 * Θ * a)) / (2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2) :=
        div_le_div_of_nonneg_right hX' hNpos.le

end

end RHTower
