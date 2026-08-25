import GaloisForLFunctions.RHTower.GammaVerticalPolar
import GaloisForLFunctions.RHTower.DigammaVerticalLogAsymptotic

/-!
# Reciprocal-Gamma phase in Kapustin's universal gauge obstruction

This file isolates the exact smooth unimodular phase used in the Makarov--Poltoratski
Toeplitz-kernel argument.  It proves the logarithmic derivative asymptotic and both endpoint
orientations, including the `η(x) - x` phase required after extracting one exponential inner
factor.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- Continuous reciprocal-Gamma phase in Kapustin's upper-half-plane rotation. -/
def kapustinReciprocalGammaPhase (x : ℝ) : ℝ :=
  gammaVerticalPhase (1 / 2) x - x * Real.log (2 * Real.pi)

/-- Phase after adjoining the fourth power of the conjugate standard Blaschke factor. -/
def kapustinToeplitzPhase (x : ℝ) : ℝ :=
  2 * kapustinReciprocalGammaPhase x - 8 * Real.arctan x

/-- Smooth unimodular symbol `U₀ · conjugate(b₀)^4` from the universal sign proof. -/
def kapustinToeplitzSymbol (x : ℝ) : ℂ :=
  Complex.exp ((kapustinToeplitzPhase x : ℂ) * I)

/-- Exact derivative of the reciprocal-Gamma Toeplitz phase. -/
def kapustinToeplitzPhaseSlope (x : ℝ) : ℝ :=
  2 * ((Complex.digamma (((1 / 2 : ℝ) : ℂ) + (x : ℂ) * I)).re -
    Real.log (2 * Real.pi)) - 8 / (1 + x ^ 2)

theorem norm_kapustinToeplitzSymbol (x : ℝ) : ‖kapustinToeplitzSymbol x‖ = 1 := by
  simp [kapustinToeplitzSymbol]

theorem kapustinReciprocalGammaPhase_zero : kapustinReciprocalGammaPhase 0 = 0 := by
  simp [kapustinReciprocalGammaPhase, gammaVerticalPhase]

@[simp] theorem kapustinReciprocalGammaPhase_neg (x : ℝ) :
    kapustinReciprocalGammaPhase (-x) = -kapustinReciprocalGammaPhase x := by
  rw [kapustinReciprocalGammaPhase, kapustinReciprocalGammaPhase,
    gammaVerticalPhase_neg (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

@[simp] theorem kapustinToeplitzPhase_neg (x : ℝ) :
    kapustinToeplitzPhase (-x) = -kapustinToeplitzPhase x := by
  rw [kapustinToeplitzPhase, kapustinToeplitzPhase,
    kapustinReciprocalGammaPhase_neg, Real.arctan_neg]
  ring

theorem hasDerivAt_kapustinReciprocalGammaPhase (x : ℝ) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _ kapustinReciprocalGammaPhase
      ((Complex.digamma (((1 / 2 : ℝ) : ℂ) + (x : ℂ) * I)).re -
        Real.log (2 * Real.pi)) x := by
  let h :=
    (hasDerivAt_gammaVerticalPhase (by norm_num : (0 : ℝ) < 1 / 2) x).sub
      ((hasDerivAt_id x).mul_const (Real.log (2 * Real.pi)))
  convert h using 1
  · ext y
    rfl
  · ring

theorem hasDerivAt_kapustinToeplitzPhase (x : ℝ) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _ kapustinToeplitzPhase
      (2 * ((Complex.digamma (((1 / 2 : ℝ) : ℂ) + (x : ℂ) * I)).re -
        Real.log (2 * Real.pi)) - 8 / (1 + x ^ 2)) x := by
  let h := (hasDerivAt_kapustinReciprocalGammaPhase x).const_mul 2 |>.sub
    ((Real.hasDerivAt_arctan x).const_mul 8)
  convert h using 1
  · ext y
    rfl
  · simp [div_eq_mul_inv]

theorem hasDerivAt_kapustinToeplitzPhase_eq_slope (x : ℝ) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _ kapustinToeplitzPhase
        (kapustinToeplitzPhaseSlope x) x := by
  exact hasDerivAt_kapustinToeplitzPhase x

theorem tendsto_kapustinToeplitzPhaseSlope_sub_two_log :
    Tendsto (fun x : ℝ => kapustinToeplitzPhaseSlope x - 2 * Real.log x)
      atTop (nhds (-2 * Real.log (2 * Real.pi))) := by
  have hpsi := re_digamma_vertical_sub_log_tendsto_zero (1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hinv : Tendsto (fun x : ℝ => 8 / (1 + x ^ 2)) atTop (nhds 0) := by
    have hsq : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop := by
      have hx2 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
        simpa [pow_two] using Filter.Tendsto.atTop_mul_atTop₀ tendsto_id tendsto_id
      simpa [add_comm] using tendsto_atTop_add_const_right atTop 1 hx2
    exact hsq.const_div_atTop 8
  have h := (hpsi.const_mul 2).sub hinv |>.sub_const (2 * Real.log (2 * Real.pi))
  convert h using 1
  · funext x
    rw [kapustinToeplitzPhaseSlope]
    ring
  · ring

theorem tendsto_kapustinToeplitzPhaseSlope_atTop :
    Tendsto kapustinToeplitzPhaseSlope atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => 2 * Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have herr := tendsto_kapustinToeplitzPhaseSlope_sub_two_log
  rw [tendsto_atTop]
  intro b
  have herrLower : ∀ᶠ x in atTop,
      -2 * Real.log (2 * Real.pi) - 1 ≤
        kapustinToeplitzPhaseSlope x - 2 * Real.log x :=
    herr.eventually (Ici_mem_nhds (by linarith))
  have hlogLarge : ∀ᶠ x in atTop,
      b - (-2 * Real.log (2 * Real.pi) - 1) ≤ 2 * Real.log x :=
    (tendsto_atTop.1 hlog) _
  filter_upwards [herrLower, hlogLarge] with x he hl
  linarith

theorem eventually_one_lt_kapustinToeplitzPhaseSlope :
    ∀ᶠ x in atTop, 1 < kapustinToeplitzPhaseSlope x :=
  tendsto_kapustinToeplitzPhaseSlope_atTop.eventually (eventually_gt_atTop 1)

theorem tendsto_kapustinReciprocalGammaPhase_ratio :
    Tendsto (fun x => kapustinReciprocalGammaPhase x / (x * Real.log x))
      atTop (nhds 1) := by
  have hgamma := tendsto_gammaVerticalPhase_ratio
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hcorr : Tendsto (fun x : ℝ => Real.log (2 * Real.pi) / Real.log x)
      atTop (nhds 0) := hlog.const_div_atTop _
  have hsub := hgamma.sub hcorr
  convert hsub using 1
  · funext x
    by_cases hx0 : x = 0
    · simp [hx0, kapustinReciprocalGammaPhase]
    · by_cases hlog0 : Real.log x = 0
      · simp [hlog0]
      · rw [kapustinReciprocalGammaPhase]
        field_simp
  · norm_num

theorem tendsto_kapustinToeplitzPhase_ratio :
    Tendsto (fun x => kapustinToeplitzPhase x / (x * Real.log x))
      atTop (nhds 2) := by
  have hmain := tendsto_kapustinReciprocalGammaPhase_ratio.const_mul 2
  have hden : Tendsto (fun x : ℝ => x * Real.log x) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id Real.tendsto_log_atTop
  have hatan : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hsmall : Tendsto (fun x : ℝ => 8 * Real.arctan x / (x * Real.log x))
      atTop (nhds 0) := (hatan.const_mul 8).div_atTop hden
  have hsub := hmain.sub hsmall
  convert hsub using 1
  · funext x
    simp only [kapustinToeplitzPhase]
    ring
  · norm_num

theorem tendsto_kapustinToeplitzPhase_atTop :
    Tendsto kapustinToeplitzPhase atTop atTop := by
  have hratio := tendsto_kapustinToeplitzPhase_ratio
  have hden : Tendsto (fun x : ℝ => x * Real.log x) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id Real.tendsto_log_atTop
  rw [tendsto_atTop]
  intro b
  have hratioOne : ∀ᶠ x in atTop,
      1 ≤ kapustinToeplitzPhase x / (x * Real.log x) :=
    hratio.eventually (Ici_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hdenLarge : ∀ᶠ x in atTop, max b 0 ≤ x * Real.log x :=
    (tendsto_atTop.1 hden) (max b 0)
  filter_upwards [hratioOne, hdenLarge] with x hr hd
  have hden0 : 0 ≤ x * Real.log x := le_trans (le_max_right b 0) hd
  have hprod : x * Real.log x ≤
      (kapustinToeplitzPhase x / (x * Real.log x)) * (x * Real.log x) := by
    simpa using mul_le_mul_of_nonneg_right hr hden0
  have hdenne : x * Real.log x ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    norm_num at hr
  calc
    b ≤ max b 0 := le_max_left _ _
    _ ≤ x * Real.log x := hd
    _ ≤ (kapustinToeplitzPhase x / (x * Real.log x)) *
        (x * Real.log x) := hprod
    _ = kapustinToeplitzPhase x := div_mul_cancel₀ _ hdenne

theorem tendsto_kapustinToeplitzPhase_atBot :
    Tendsto kapustinToeplitzPhase atBot atBot := by
  rw [tendsto_atBot]
  intro b
  have ha : ∀ᶠ x in atTop, -b ≤ kapustinToeplitzPhase x :=
    (tendsto_atTop.1 tendsto_kapustinToeplitzPhase_atTop) (-b)
  have hneg : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  have ha' := hneg.eventually ha
  filter_upwards [ha'] with x hx
  simpa using hx

theorem tendsto_kapustinToeplitzPhase_sub_id_ratio :
    Tendsto (fun x => (kapustinToeplitzPhase x - x) / (x * Real.log x))
      atTop (nhds 2) := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hsmall : Tendsto (fun x : ℝ => x / (x * Real.log x)) atTop (nhds 0) := by
    have hzero := hlog.const_div_atTop 1
    convert hzero using 1
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  have h := tendsto_kapustinToeplitzPhase_ratio.sub hsmall
  convert h using 1
  · funext x
    ring
  · norm_num

theorem tendsto_kapustinToeplitzPhase_sub_id_atTop :
    Tendsto (fun x => kapustinToeplitzPhase x - x) atTop atTop := by
  have hratio := tendsto_kapustinToeplitzPhase_sub_id_ratio
  have hden : Tendsto (fun x : ℝ => x * Real.log x) atTop atTop :=
    Filter.Tendsto.atTop_mul_atTop₀ tendsto_id Real.tendsto_log_atTop
  rw [tendsto_atTop]
  intro b
  have hratioOne : ∀ᶠ x in atTop,
      1 ≤ (kapustinToeplitzPhase x - x) / (x * Real.log x) :=
    hratio.eventually (Ici_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hdenLarge : ∀ᶠ x in atTop, max b 0 ≤ x * Real.log x :=
    (tendsto_atTop.1 hden) (max b 0)
  filter_upwards [hratioOne, hdenLarge] with x hr hd
  have hden0 : 0 ≤ x * Real.log x := le_trans (le_max_right b 0) hd
  have hprod : x * Real.log x ≤
      ((kapustinToeplitzPhase x - x) / (x * Real.log x)) *
        (x * Real.log x) := by
    simpa using mul_le_mul_of_nonneg_right hr hden0
  have hdenne : x * Real.log x ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    norm_num at hr
  calc
    b ≤ max b 0 := le_max_left _ _
    _ ≤ x * Real.log x := hd
    _ ≤ ((kapustinToeplitzPhase x - x) / (x * Real.log x)) *
        (x * Real.log x) := hprod
    _ = kapustinToeplitzPhase x - x := div_mul_cancel₀ _ hdenne

theorem tendsto_kapustinToeplitzPhase_sub_id_atBot :
    Tendsto (fun x => kapustinToeplitzPhase x - x) atBot atBot := by
  rw [tendsto_atBot]
  intro b
  have ha : ∀ᶠ x in atTop, -b ≤ kapustinToeplitzPhase x - x :=
    (tendsto_atTop.1 tendsto_kapustinToeplitzPhase_sub_id_atTop) (-b)
  have hneg : Tendsto (fun x : ℝ => -x) atBot atTop := tendsto_neg_atBot_atTop
  have ha' := hneg.eventually ha
  filter_upwards [ha'] with x hx
  have hodd : kapustinToeplitzPhase (-x) - (-x) =
      -(kapustinToeplitzPhase x - x) := by
    rw [kapustinToeplitzPhase_neg]
    ring
  rw [hodd] at hx
  linarith

end RHTower
