import GaloisForLFunctions.RHTower.WeightedScrewPoleContradictionThreshold
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarBombieriYoshida
import GaloisForLFunctions.RHTower.ConstrainedWeilPolarDerivativeTest

/-!
# Quantitative Bombieri–Yoshida: exponential lower bounds on the ground energy cap all excesses

**Theorem.**  If the pole-vanishing ground energy of the CCM restricted Weil form satisfies
`μ₀(B) ≥ −C e^{εB}` at every aperture `B`, with `C ≥ 0` and `ε ≥ 0`, then every Xi zero satisfies
`|Re ρ − ½| ≤ ε`.  In particular, if `μ₀` is not exponentially negative at any positive rate, the
Riemann hypothesis holds.

Proof.  For the polar-translated two-bump tests `M∗(b_t − b_0)` (support radius `|t| + 2`, aperture
`|t| + 3`, enlarged to `|t| + 6` by the translate), the pole-vanishing source has `L²` norm at most
`200 (1 + cosh ½)² (|t| + 4)`, so the ground-energy bound gives `Re Q(M∗(b_t − b_0)) ≥ −K(t)` with
`K(t) = 200 C (1 + cosh ½)² e^{6ε} (t + 4) e^{εt}` for `t ≥ 0`.  Passing to the two-bump limit,
the polar-weighted screw divisor satisfies `Re Φ₁(t) ≥ −K(t)/2 ≥ −C₀ e^{(ε+δ)t}` for every
`δ ∈ (0, 1]`, and the threshold Widder–Landau engine caps every excess at `ε + δ`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The primitive is bounded by the `L¹` norm of the test -/

theorem norm_zeroMeanPrimitive_le_integral_norm {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (x : ℝ) :
    ‖φ.zeroMeanPrimitive x‖ ≤ ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
  unfold SuzukiSmoothZeroMeanTest.zeroMeanPrimitive
  have hint : Integrable (fun u : ℝ => ‖(φ : ℝ → ℂ) u‖) := φ.integrable.norm
  have hnn : 0 ≤ᵐ[volume] fun u : ℝ => ‖(φ : ℝ → ℂ) u‖ :=
    Filter.Eventually.of_forall fun u => norm_nonneg _
  refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
  rcases le_or_gt (-a - 1) x with hle | hlt
  · rw [intervalIntegral.integral_of_le hle, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact setIntegral_le_integral hint hnn
  · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hlt.le, abs_neg,
      abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact setIntegral_le_integral hint hnn

/-! ## The polar-translated two-bump source -/

/-- The aperture `|t| + 3` containing the two-bump test of support radius `|t| + 2`. -/
def twoBumpAperture (t : ℝ) : SuzukiPositiveAperture := ⟨|t| + 3, by positivity⟩

theorem twoBumpAperture_gt (t : ℝ) : |t| + 2 < (twoBumpAperture t).1 := by
  show |t| + 2 < |t| + 3
  linarith

/-- The polar-translated primitive source of the `n`-th two-bump test. -/
def twoBumpSource (t : ℝ) (n : ℕ) : CCMComplexSmoothInteriorSource ((twoBumpAperture t).enlarge 1 one_pos) :=
  ((twoBumpSeq t n).zeroMeanPrimitiveSource (twoBumpAperture t) (twoBumpAperture_gt t)).polarTranslate
    one_pos

theorem abs_polarMultiplierWeight_le (k : Fin 5) :
    |polarMultiplierWeight 1 k| ≤ 1 + Real.cosh (1 / 2) := by
  have hc : 1 ≤ Real.cosh (2⁻¹ : ℝ) := Real.one_le_cosh _
  have hc' : 1 ≤ Real.cosh (1 / 2 : ℝ) := Real.one_le_cosh _
  fin_cases k <;> simp [polarMultiplierWeight, abs_le] <;>
    first | (constructor <;> linarith) | linarith

/-- Pointwise bound on the translated source: `5 (1 + cosh ½) ∫|φ|`. -/
theorem norm_twoBumpSource_le (t : ℝ) (n : ℕ) (x : ℝ) :
    ‖(twoBumpSource t n : ℝ → ℂ) x‖ ≤ 5 * (1 + Real.cosh (1 / 2)) * 2 := by
  have hL1 := integral_norm_twoBumpSeq_le t n
  have hprim : ∀ y : ℝ, ‖(twoBumpSeq t n).zeroMeanPrimitive y‖ ≤ 2 :=
    fun y => (norm_zeroMeanPrimitive_le_integral_norm _ y).trans hL1
  change ‖translateCombo (polarMultiplierWeight 1) (polarMultiplierShift 1)
    (twoBumpSeq t n).zeroMeanPrimitive x‖ ≤ _
  unfold translateCombo
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k : Fin 5, ‖(polarMultiplierWeight 1 k : ℂ)
      * (twoBumpSeq t n).zeroMeanPrimitive (x - polarMultiplierShift 1 k)‖
      ≤ (1 + Real.cosh (1 / 2)) * 2 := by
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (abs_polarMultiplierWeight_le k) (hprim _) (norm_nonneg _) (by positivity)
  calc ∑ k : Fin 5, ‖(polarMultiplierWeight 1 k : ℂ)
        * (twoBumpSeq t n).zeroMeanPrimitive (x - polarMultiplierShift 1 k)‖
      ≤ ∑ _k : Fin 5, (1 + Real.cosh (1 / 2)) * 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = 5 * (1 + Real.cosh (1 / 2)) * 2 := by simp; ring

theorem twoBumpSource_support_subset (t : ℝ) (n : ℕ) :
    Function.support (twoBumpSource t n : ℝ → ℂ) ⊆ Icc (-(|t| + 2 + 2)) (|t| + 2 + 2) := by
  change Function.support (translateCombo (polarMultiplierWeight 1) (polarMultiplierShift 1)
    (twoBumpSeq t n).zeroMeanPrimitive) ⊆ _
  have h := support_translateCombo_subset (polarMultiplierWeight 1) (polarMultiplierShift 1)
    (twoBumpSeq t n).support_zeroMeanPrimitive_subset (polarMultiplierShift_abs_le one_pos)
  simpa using h

/-- **`L²` bound on the two-bump source**: `‖U‖² ≤ 200 (1 + cosh ½)² (|t| + 4)`. -/
theorem norm_sq_twoBumpSource_le (t : ℝ) (n : ℕ) :
    ‖ccmArchimedeanFormToAperture ((twoBumpAperture t).enlarge 1 one_pos)
        (twoBumpSource t n).toCCMFormVector‖ ^ 2
      ≤ 200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| + 4) := by
  rw [norm_sq_toAperture_eq_integral]
  set B : ℝ := 5 * (1 + Real.cosh (1 / 2)) * 2 with hB
  have hzero : ∀ x ∉ Icc (-(|t| + 2 + 2)) (|t| + 2 + 2), ‖(twoBumpSource t n : ℝ → ℂ) x‖ ^ 2 = 0 := by
    intro x hx
    have : (twoBumpSource t n : ℝ → ℂ) x = 0 := by
      by_contra h
      exact hx (twoBumpSource_support_subset t n h)
    rw [this]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcont : Continuous fun x : ℝ => ‖(twoBumpSource t n : ℝ → ℂ) x‖ ^ 2 :=
    ((twoBumpSource t n).smooth.continuous.norm).pow 2
  calc ∫ x in Icc (-(|t| + 2 + 2)) (|t| + 2 + 2), ‖(twoBumpSource t n : ℝ → ℂ) x‖ ^ 2
      ≤ ∫ x in Icc (-(|t| + 2 + 2)) (|t| + 2 + 2), B ^ 2 := by
        refine setIntegral_mono_on hcont.integrableOn_Icc continuous_const.integrableOn_Icc
          measurableSet_Icc fun x _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_twoBumpSource_le t n x) 2
    _ = 2 * (|t| + 4) * B ^ 2 := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith [abs_nonneg t])]
        ring
    _ = 200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| + 4) := by
        rw [hB]; ring

/-! ## Transfer of the ground-energy bound to the two-bump forms -/

theorem re_smoothForm_twoBump_ge {C ε : ℝ} (hC : 0 ≤ C)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (t : ℝ) (n : ℕ) :
    -(C * Real.exp (ε * (|t| + 6)) * (200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| + 4)))
      ≤ (suzukiScrewSmoothForm ((twoBumpSeq t n).polarTranslateTest one_pos)
          ((twoBumpSeq t n).polarTranslateTest one_pos)).re := by
  set A' := (twoBumpAperture t).enlarge 1 one_pos with hA'
  have hA'val : A'.1 = |t| + 6 := by
    show (twoBumpAperture t).1 + 2 * 1 + 1 = |t| + 6
    show |t| + 3 + 2 * 1 + 1 = |t| + 6
    ring
  have hpol := isPolarConstrained_polarTranslate
    ((twoBumpSeq t n).zeroMeanPrimitiveSource (twoBumpAperture t) (twoBumpAperture_gt t)) one_pos
  have h1 := ccmRestrictedWeilPolarGroundEnergy_mul_le A' _ hpol
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm,
    suzukiScrewSmoothForm_congr_coe _ ((twoBumpSeq t n).polarTranslateTest one_pos)
      (deriv_polarTranslate_zeroMeanPrimitiveSource (twoBumpSeq t n) (twoBumpAperture t)
        (twoBumpAperture_gt t) one_pos)] at h1
  set n' : ℝ := ‖ccmArchimedeanFormToAperture A' (twoBumpSource t n).toCCMFormVector‖ ^ 2 with hn'
  have hn'0 : 0 ≤ n' := by positivity
  have hn'le : n' ≤ 200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| + 4) := norm_sq_twoBumpSource_le t n
  have hμ := h A'
  rw [hA'val] at hμ
  have hE : 0 ≤ C * Real.exp (ε * (|t| + 6)) := by positivity
  calc -(C * Real.exp (ε * (|t| + 6)) * (200 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| + 4)))
      ≤ -(C * Real.exp (ε * (|t| + 6))) * n' := by nlinarith
    _ ≤ ccmRestrictedWeilPolarGroundEnergy A' * n' := mul_le_mul_of_nonneg_right hμ hn'0
    _ ≤ _ := h1

/-- The polar-weighted screw divisor inherits the exponential lower bound. -/
theorem re_weightedXiScrewDivisor_polar_ge {C ε : ℝ} (hC : 0 ≤ C)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B) (t : ℝ) :
    -(C * Real.exp (ε * (|t| + 6)) * (100 * (1 + Real.cosh (1 / 2)) ^ 2 * (|t| + 4)))
      ≤ (weightedXiScrewDivisor (polarSpectralWeight 1) t).re := by
  have hlim := (tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq t one_pos)
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hbound := ge_of_tendsto' hre (fun n => re_smoothForm_twoBump_ge hC h t n)
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hbound
  linarith

/-! ## Absorbing the polynomial factor and the final theorems -/

theorem one_add_le_exp_div {δ t : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + t ≤ Real.exp (δ * t) / δ := by
  rw [le_div_iff₀ hδ]
  have := Real.add_one_le_exp (δ * t)
  nlinarith

/-- **Quantitative Bombieri–Yoshida.**  If `μ₀(B) ≥ −C e^{εB}` at every aperture with
`0 ≤ ε < 1/2`, then every copy satisfies `|Im z_q| ≤ ε + δ` for every `δ ∈ (0, ½ − ε)`. -/
theorem abs_im_le_add_of_polarGroundEnergy_ge {C ε δ : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεδ : ε + δ < 1 / 2)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε + δ := by
  have hh : (0 : ℝ) < 1 := one_pos
  set K : ℝ := C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2) * 4 / δ with hK
  have hK0 : 0 ≤ K := by positivity
  have hlow : ∀ t : ℝ, 0 ≤ t →
      -(K * Real.exp ((ε + δ) * t)) ≤ (weightedXiScrewDivisor (polarSpectralWeight 1) t).re := by
    intro t ht
    have h1 := re_weightedXiScrewDivisor_polar_ge hC h t
    rw [abs_of_nonneg ht] at h1
    refine le_trans ?_ h1
    rw [neg_le_neg_iff]
    have hexp : Real.exp (ε * (t + 6)) = Real.exp (ε * 6) * Real.exp (ε * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp2 : Real.exp ((ε + δ) * t) = Real.exp (ε * t) * Real.exp (δ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have ht4 : t + 4 ≤ 4 * (1 + t) := by linarith
    have hone := one_add_le_exp_div (t := t) hδ hδ1
    have hpos : 0 ≤ C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2) := by positivity
    have hE : 0 ≤ Real.exp (ε * t) := (Real.exp_pos _).le
    calc C * Real.exp (ε * (t + 6)) * (100 * (1 + Real.cosh (1 / 2)) ^ 2 * (t + 4))
        = (C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2)) * Real.exp (ε * t) * (t + 4) := by
          rw [hexp]; ring
      _ ≤ (C * Real.exp (ε * 6) * (100 * (1 + Real.cosh (1 / 2)) ^ 2)) * Real.exp (ε * t)
            * (4 * (Real.exp (δ * t) / δ)) := by
          gcongr
          linarith
      _ = K * Real.exp ((ε + δ) * t) := by
          rw [hK, hexp2]
          field_simp
  exact abs_im_le_of_thr (polarSpectralWeight 1) K (ε + δ) (C := polarSymbolBound 1 ^ 2)
    (by positivity) (norm_polarSpectralWeight_le hh.le)
    (fun q q' hq => polarSpectralWeight_of_eq 1 hq)
    (fun q q' hq => polarSpectralWeight_of_neg 1 hq)
    (fun q him => polarSpectralWeight_ne_zero hh q him)
    hlow (fun t => weightedXiScrewDivisor_polar_im 1 t) (by linarith) hεδ q

/-- **Exponential lower bounds on the ground energy cap all excesses.** -/
theorem abs_im_xiSpectralPoint_le_of_polarGroundEnergy_ge {C ε : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (h : ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε := by
  rcases le_or_gt (1 / 2 : ℝ) ε with hε | hε
  · exact (abs_xiSpectralPoint_im_lt_half q).le.trans hε
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set δ' : ℝ := min δ (min 1 ((1 / 2 - ε) / 2)) with hδ'
    have hδ'pos : 0 < δ' := lt_min hδ (lt_min one_pos (by linarith))
    have hδ'1 : δ' ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ'half : ε + δ' < 1 / 2 := by
      have : δ' ≤ (1 / 2 - ε) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hδ'δ : δ' ≤ δ := min_le_left _ _
    exact (abs_im_le_add_of_polarGroundEnergy_ge hC hε0 hδ'pos hδ'1 hδ'half h q).trans
      (by linarith)

/-- **Sub-exponential negativity of the ground energy implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_polarGroundEnergy_subexponential
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ B : SuzukiPositiveAperture,
      -(C * Real.exp (ε * B.1)) ≤ ccmRestrictedWeilPolarGroundEnergy B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have him : (xiSpectralPoint q).im = 0 := by
    have hle : |(xiSpectralPoint q).im| ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨C, hC, hB⟩ := h ε hε
      have := abs_im_xiSpectralPoint_le_of_polarGroundEnergy_ge hC hε.le hB q
      linarith
    exact abs_nonpos_iff.mp hle
  exact ⟨(xiSpectralPoint q).re, by apply Complex.ext <;> simp [him]⟩

end

end RHTower
