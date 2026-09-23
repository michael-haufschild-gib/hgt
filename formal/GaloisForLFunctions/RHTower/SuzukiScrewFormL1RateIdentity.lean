import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarBombieriYoshidaSharp
import GaloisForLFunctions.RHTower.SuzukiScrewFormExcessLowerBound
import GaloisForLFunctions.RHTower.ScrewCurvatureSumOfSquares

/-!
# The exact `L¹` rate identity: `Θ_sup` is half the exponential rate of Weil negativity

Say the screw form has **`L¹` negativity rate `ε`** if `Re Q(φ) ≥ −C e^{ε|a|} ‖φ‖₁²` for every smooth
zero-mean test `φ` at every aperture `a`, with one constant `C`.  Two facts close the rate law:

* rate `2Θ_sup` holds, by the termwise bound `‖c_q‖ ≤ (e^{Θ_sup|a|}+1)‖φ‖₁` and `Σ'_q ‖z_q‖⁻² < ∞`;
* rate `ε < 1` forces every excess `|Im z_q| ≤ ε/2`: the centred polar-translated two-bump tests have
  `L¹` norm at most `10(1 + cosh ½)` and aperture `|t|/2 + 4`, so the polar-weighted screw divisor is
  bounded below by `−K e^{(ε/2) t}`, and the threshold Widder–Landau engine caps the excess.

Hence for `0 ≤ ε < 1`: the screw form has `L¹` rate `ε` iff `2 Θ_sup ≤ ε`, and the Riemann
hypothesis is exactly sub-exponential `L¹` negativity of the Weil form in the aperture.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- **`L¹` negativity rate `ε` of the screw form.** -/
def ScrewFormL1Rate (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (φ : SuzukiSmoothZeroMeanTest a),
    -(C * Real.exp (ε * |a|) * (∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ)) ≤ (suzukiScrewSmoothForm φ φ).re

theorem xiSpectralInvSqSum_nonneg : 0 ≤ xiSpectralInvSqSum :=
  tsum_nonneg fun _ => by positivity

/-- Rates are upward closed. -/
theorem ScrewFormL1Rate.mono {ε ε' : ℝ} (h : ScrewFormL1Rate ε) (hle : ε ≤ ε') :
    ScrewFormL1Rate ε' := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun a φ => le_trans ?_ (hb a φ)⟩
  rw [neg_le_neg_iff]
  have hI : 0 ≤ (∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ) := by positivity
  have hexp : Real.exp (ε * |a|) ≤ Real.exp (ε' * |a|) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hC) hI

/-- **Upper half of the rate identity.**  The screw form has `L¹` rate `2 Θ_sup`, with constant
`4 Σ'_q ‖z_q‖⁻²`. -/
theorem screwFormL1Rate_two_mul_topExcess : ScrewFormL1Rate (2 * xiTopExcess) := by
  refine ⟨4 * xiSpectralInvSqSum, by linarith [xiSpectralInvSqSum_nonneg], fun a φ => ?_⟩
  refine le_trans ?_ (re_suzukiScrewSmoothForm_ge_topExcess φ)
  rw [neg_le_neg_iff]
  set L : ℝ := ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ with hL
  have hL0 : 0 ≤ L := integral_nonneg fun u => norm_nonneg _
  have hx : 0 ≤ xiTopExcess * |a| := mul_nonneg xiTopExcess_nonneg (abs_nonneg _)
  have h1 : 1 ≤ Real.exp (xiTopExcess * |a|) := Real.one_le_exp hx
  have hsq : (Real.exp (xiTopExcess * |a|) + 1) ^ (2 : ℕ) ≤ 4 * Real.exp (2 * xiTopExcess * |a|) := by
    have : Real.exp (2 * xiTopExcess * |a|) = Real.exp (xiTopExcess * |a|) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    nlinarith
  have hS := xiSpectralInvSqSum_nonneg
  calc ((Real.exp (xiTopExcess * |a|) + 1) * L) ^ (2 : ℕ) * xiSpectralInvSqSum
      = (Real.exp (xiTopExcess * |a|) + 1) ^ (2 : ℕ) * L ^ (2 : ℕ) * xiSpectralInvSqSum := by ring
    _ ≤ 4 * Real.exp (2 * xiTopExcess * |a|) * L ^ (2 : ℕ) * xiSpectralInvSqSum := by gcongr
    _ = 4 * xiSpectralInvSqSum * Real.exp (2 * xiTopExcess * |a|) * L ^ (2 : ℕ) := by ring

/-- `L¹` norm of the polar translate of a test: at most `5 (1 + cosh ½)` times the `L¹` norm. -/
theorem integral_norm_polarTranslateTest_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    ∫ x : ℝ, ‖(φ.polarTranslateTest one_pos : ℝ → ℂ) x‖
      ≤ 5 * (1 + Real.cosh (1 / 2)) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
  have hint : ∀ k : Fin 5,
      Integrable (fun x : ℝ => ‖(φ : ℝ → ℂ) (x - polarMultiplierShift 1 k)‖) :=
    fun k => ((integrable_suzukiSmoothZeroMeanTest φ).comp_sub_right _).norm
  have hpt : ∀ x : ℝ, ‖(φ.polarTranslateTest one_pos : ℝ → ℂ) x‖
      ≤ ∑ k : Fin 5, (1 + Real.cosh (1 / 2)) * ‖(φ : ℝ → ℂ) (x - polarMultiplierShift 1 k)‖ := by
    intro x
    change ‖translateCombo (polarMultiplierWeight 1) (polarMultiplierShift 1) (φ : ℝ → ℂ) x‖ ≤ _
    unfold translateCombo
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_polarMultiplierWeight_le k) (norm_nonneg _)
  have hsumint : Integrable (fun x : ℝ => ∑ k : Fin 5,
      (1 + Real.cosh (1 / 2)) * ‖(φ : ℝ → ℂ) (x - polarMultiplierShift 1 k)‖) :=
    integrable_finsetSum _ fun k _ => (hint k).const_mul _
  calc ∫ x : ℝ, ‖(φ.polarTranslateTest one_pos : ℝ → ℂ) x‖
      ≤ ∫ x : ℝ, ∑ k : Fin 5,
          (1 + Real.cosh (1 / 2)) * ‖(φ : ℝ → ℂ) (x - polarMultiplierShift 1 k)‖ :=
        integral_mono (integrable_suzukiSmoothZeroMeanTest _).norm hsumint hpt
    _ = ∑ k : Fin 5, (1 + Real.cosh (1 / 2)) *
          ∫ x : ℝ, ‖(φ : ℝ → ℂ) (x - polarMultiplierShift 1 k)‖ := by
        rw [integral_finsetSum _ fun k _ => (hint k).const_mul _]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul]
    _ = ∑ _k : Fin 5, (1 + Real.cosh (1 / 2)) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_sub_right_eq_self (fun u => ‖(φ : ℝ → ℂ) u‖)]
    _ = 5 * (1 + Real.cosh (1 / 2)) * ∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The `L¹` rate bound controls the centred two-bump forms with a constant independent of `n`. -/
theorem re_smoothForm_twoBump_ge_of_l1Rate {C ε : ℝ} (hC : 0 ≤ C)
    (h : ∀ (a : ℝ) (φ : SuzukiSmoothZeroMeanTest a),
      -(C * Real.exp (ε * |a|) * (∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ)) ≤ (suzukiScrewSmoothForm φ φ).re)
    (t : ℝ) (n : ℕ) :
    -(C * Real.exp (ε * (|t| / 2 + 4)) * (10 * (1 + Real.cosh (1 / 2))) ^ (2 : ℕ))
      ≤ (suzukiScrewSmoothForm ((twoBumpSeq t n).polarTranslateTest one_pos)
          ((twoBumpSeq t n).polarTranslateTest one_pos)).re := by
  rw [← suzukiScrewSmoothForm_twoBumpSeqC]
  set ψ := (twoBumpSeqC t n).polarTranslateTest one_pos with hψ
  have hL1 : ∫ x : ℝ, ‖(ψ : ℝ → ℂ) x‖ ≤ 10 * (1 + Real.cosh (1 / 2)) := by
    calc ∫ x : ℝ, ‖(ψ : ℝ → ℂ) x‖
        ≤ 5 * (1 + Real.cosh (1 / 2)) * ∫ u : ℝ, ‖(twoBumpSeqC t n : ℝ → ℂ) u‖ :=
          integral_norm_polarTranslateTest_le _
      _ ≤ 5 * (1 + Real.cosh (1 / 2)) * 2 :=
          mul_le_mul_of_nonneg_left (integral_norm_twoBumpSeqC_le t n) (by positivity)
      _ = 10 * (1 + Real.cosh (1 / 2)) := by ring
  have h1 := h _ ψ
  have habs : |(|t| / 2 + 2 + 2 * 1 : ℝ)| = |t| / 2 + 4 := by
    rw [abs_of_nonneg (by positivity)]
    ring
  rw [habs] at h1
  refine le_trans ?_ h1
  rw [neg_le_neg_iff]
  have hL0 : 0 ≤ ∫ x : ℝ, ‖(ψ : ℝ → ℂ) x‖ := integral_nonneg fun _ => norm_nonneg _
  have hsq := pow_le_pow_left₀ hL0 hL1 2
  have hE : 0 ≤ C * Real.exp (ε * (|t| / 2 + 4)) := by positivity
  exact mul_le_mul_of_nonneg_left hsq hE

/-- The polar-weighted screw divisor inherits the `L¹` rate bound at half the aperture. -/
theorem re_weightedXiScrewDivisor_polar_ge_of_l1Rate {C ε : ℝ} (hC : 0 ≤ C)
    (h : ∀ (a : ℝ) (φ : SuzukiSmoothZeroMeanTest a),
      -(C * Real.exp (ε * |a|) * (∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ)) ≤ (suzukiScrewSmoothForm φ φ).re)
    (t : ℝ) :
    -(C * Real.exp (ε * (|t| / 2 + 4)) * (10 * (1 + Real.cosh (1 / 2))) ^ (2 : ℕ) / 2)
      ≤ (weightedXiScrewDivisor (polarSpectralWeight 1) t).re := by
  have hlim := (tendsto_suzukiScrewSmoothForm_polarTranslateTest_twoBumpSeq t one_pos)
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hbound := ge_of_tendsto' hre (fun n => re_smoothForm_twoBump_ge_of_l1Rate hC h t n)
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hbound
  linarith

/-- **Lower half of the rate identity.**  An `L¹` rate `ε < 1` caps every excess by `ε/2`. -/
theorem abs_im_xiSpectralPoint_le_half_of_l1Rate {C ε : ℝ} (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1)
    (h : ∀ (a : ℝ) (φ : SuzukiSmoothZeroMeanTest a),
      -(C * Real.exp (ε * |a|) * (∫ u : ℝ, ‖(φ : ℝ → ℂ) u‖) ^ (2 : ℕ)) ≤ (suzukiScrewSmoothForm φ φ).re)
    (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ ε / 2 := by
  have hh : (0 : ℝ) < 1 := one_pos
  set K : ℝ := C * Real.exp (ε * 4) * (10 * (1 + Real.cosh (1 / 2))) ^ (2 : ℕ) / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hlow : ∀ t : ℝ, 0 ≤ t →
      -(K * Real.exp (ε / 2 * t)) ≤ (weightedXiScrewDivisor (polarSpectralWeight 1) t).re := by
    intro t ht
    have h1 := re_weightedXiScrewDivisor_polar_ge_of_l1Rate hC h t
    rw [abs_of_nonneg ht] at h1
    refine le_trans (le_of_eq ?_) h1
    rw [hK]
    have hexp : Real.exp (ε * (t / 2 + 4)) = Real.exp (ε * 4) * Real.exp (ε / 2 * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]
    ring
  exact abs_im_le_of_thr (polarSpectralWeight 1) K (ε / 2) (C := polarSymbolBound 1 ^ (2 : ℕ))
    (by positivity) (norm_polarSpectralWeight_le hh.le)
    (fun q q' hq => polarSpectralWeight_of_eq 1 hq)
    (fun q q' hq => polarSpectralWeight_of_neg 1 hq)
    (fun q him => polarSpectralWeight_ne_zero hh q him)
    hlow (fun t => weightedXiScrewDivisor_polar_im 1 t) (by linarith) (by linarith) q

/-- An `L¹` rate `ε < 1` bounds the top excess by `ε/2`. -/
theorem xiTopExcess_le_half_of_screwFormL1Rate {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h : ScrewFormL1Rate ε) : xiTopExcess ≤ ε / 2 := by
  obtain ⟨C, hC, hb⟩ := h
  exact Real.iSup_le (fun q => abs_im_xiSpectralPoint_le_half_of_l1Rate hC hε0 hε1 hb q)
    (by linarith)

/-- **Exact `L¹` rate identity.**  For `0 ≤ ε < 1`, the screw form has `L¹` negativity rate `ε` if
and only if `2 Θ_sup ≤ ε`: the top excess of the Xi zeros is exactly half the exponential rate of
the `L¹`-normalised negative part of the Weil form. -/
theorem screwFormL1Rate_iff {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ScrewFormL1Rate ε ↔ 2 * xiTopExcess ≤ ε :=
  ⟨fun h => by linarith [xiTopExcess_le_half_of_screwFormL1Rate hε0 hε1 h],
    fun h => screwFormL1Rate_two_mul_topExcess.mono h⟩

/-- Under the Riemann hypothesis the top excess vanishes. -/
theorem xiTopExcess_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) : xiTopExcess = 0 := by
  apply le_antisymm _ xiTopExcess_nonneg
  refine Real.iSup_le (fun q => ?_) le_rfl
  rw [xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q, abs_zero]

/-- **RH is sub-exponential `L¹` negativity of the Weil form.**  The Riemann hypothesis holds if and
only if the screw form has `L¹` negativity rate `ε` for every `ε > 0`. -/
theorem riemannHypothesis_iff_screwFormL1Rate_subexponential :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ScrewFormL1Rate ε := by
  constructor
  · intro hRH ε hε
    refine screwFormL1Rate_two_mul_topExcess.mono ?_
    rw [xiTopExcess_eq_zero_of_riemannHypothesis hRH]
    linarith
  · intro h
    have hzero : xiTopExcess = 0 := by
      apply le_antisymm _ xiTopExcess_nonneg
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      set ε : ℝ := min δ (1 / 2) with hε
      have hεpos : 0 < ε := lt_min hδ (by norm_num)
      have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have := xiTopExcess_le_half_of_screwFormL1Rate hεpos.le hε1 (h ε hεpos)
      have : ε ≤ δ := min_le_left _ _
      linarith
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him : (xiSpectralPoint q).im = 0 := by
      have h1 := abs_im_xiSpectralPoint_le_xiTopExcess q
      rw [hzero] at h1
      exact abs_nonpos_iff.mp h1
    exact ⟨(xiSpectralPoint q).re, by apply Complex.ext <;> simp [him]⟩

end

end RHTower
