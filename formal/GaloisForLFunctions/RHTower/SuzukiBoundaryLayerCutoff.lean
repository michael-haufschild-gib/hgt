import GaloisForLFunctions.RHTower.SuzukiBoundaryLayerFourierIntegrationByParts
import GaloisForLFunctions.HTGeometry.SmoothWeight

/-!
# Suzuki's explicit smooth boundary cutoff

This module formalizes the cutoff used in Suzuki's proof of equation (3.2).  For aperture `a > 0`
and width `ε > 0`,

`η(x) = smoothTransition ((x+a)/ε) * smoothTransition ((a-x)/ε)`

is smooth, supported in `[-a,a]`, and identically one on `[-a+ε,a-ε]`.  Multiplying a unit
exponential mode by `η` produces the required compactly supported smooth approximant.  The error
is confined to the two endpoint strips and has pointwise norm at most one.
-/

open MeasureTheory Set Complex
open scoped ENNReal FourierTransform ContDiff

noncomputable section

namespace RHTower

/-- A boundary width which is positive for every index, fits in the aperture, and has total
boundary length at most `1/(m+1)`. -/
def suzukiBoundaryWidth (a : ℝ) (m : ℕ) : ℝ :=
  a / (2 * (1 + a) * ((m : ℝ) + 1))

theorem suzukiBoundaryWidth_pos {a : ℝ} (ha : 0 < a) (m : ℕ) :
    0 < suzukiBoundaryWidth a m := by
  unfold suzukiBoundaryWidth
  positivity

theorem suzukiBoundaryWidth_lt_aperture {a : ℝ} (ha : 0 < a) (m : ℕ) :
    suzukiBoundaryWidth a m < a := by
  have hden : (1 : ℝ) < 2 * (1 + a) * ((m : ℝ) + 1) := by
    have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    nlinarith
  unfold suzukiBoundaryWidth
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem two_mul_suzukiBoundaryWidth_le_inv_succ {a : ℝ} (ha : 0 < a) (m : ℕ) :
    2 * suzukiBoundaryWidth a m ≤ 1 / ((m : ℝ) + 1) := by
  have ha1 : 0 < 1 + a := by linarith
  have hm : 0 < (m : ℝ) + 1 := by positivity
  unfold suzukiBoundaryWidth
  rw [div_eq_mul_inv]
  field_simp
  nlinarith

/-- Product cutoff which rises smoothly at the left endpoint and falls smoothly at the right. -/
def suzukiBoundaryCutoff (a ε x : ℝ) : ℝ :=
  Real.smoothTransition ((x + a) / ε) *
    Real.smoothTransition ((a - x) / ε)

theorem contDiff_suzukiBoundaryCutoff (a ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiBoundaryCutoff a ε) := by
  unfold suzukiBoundaryCutoff
  fun_prop

theorem suzukiBoundaryCutoff_nonneg (a ε x : ℝ) :
    0 ≤ suzukiBoundaryCutoff a ε x := by
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem suzukiBoundaryCutoff_le_one (a ε x : ℝ) :
    suzukiBoundaryCutoff a ε x ≤ 1 := by
  unfold suzukiBoundaryCutoff
  nlinarith [Real.smoothTransition.nonneg ((x + a) / ε),
    Real.smoothTransition.le_one ((x + a) / ε),
    Real.smoothTransition.nonneg ((a - x) / ε),
    Real.smoothTransition.le_one ((a - x) / ε)]

theorem suzukiBoundaryCutoff_eq_zero_of_le_neg {a ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ -a) : suzukiBoundaryCutoff a ε x = 0 := by
  unfold suzukiBoundaryCutoff
  have hleft : (x + a) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [Real.smoothTransition.zero_of_nonpos hleft, zero_mul]

theorem suzukiBoundaryCutoff_eq_zero_of_aperture_le {a ε x : ℝ} (hε : 0 < ε)
    (hx : a ≤ x) : suzukiBoundaryCutoff a ε x = 0 := by
  unfold suzukiBoundaryCutoff
  have hright : (a - x) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [Real.smoothTransition.zero_of_nonpos hright, mul_zero]

theorem suzukiBoundaryCutoff_eq_one_of_mem_inner {a ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Icc (-a + ε) (a - ε)) : suzukiBoundaryCutoff a ε x = 1 := by
  unfold suzukiBoundaryCutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · exact (le_div_iff₀ hε).2 (by linarith [hx.2])
  · exact (le_div_iff₀ hε).2 (by linarith [hx.1])

theorem hasCompactSupport_suzukiBoundaryCutoff {a ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (suzukiBoundaryCutoff a ε) := by
  refine HasCompactSupport.intro (K := Icc (-a) a) isCompact_Icc ?_
  intro x hx
  rw [mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · exact suzukiBoundaryCutoff_eq_zero_of_le_neg hε (le_of_not_ge hx)
  · exact suzukiBoundaryCutoff_eq_zero_of_aperture_le hε (le_of_not_ge hx)

/-- Arbitrary real-frequency exponential mode.  Suzuki's basis corresponds to
`κ = π n / a`. -/
def suzukiApertureMode (κ x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (κ : ℂ) * (x : ℂ))

theorem norm_suzukiApertureMode (κ x : ℝ) : ‖suzukiApertureMode κ x‖ = 1 := by
  rw [suzukiApertureMode, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem contDiff_suzukiApertureMode (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiApertureMode κ) := by
  unfold suzukiApertureMode
  exact Complex.contDiff_exp.comp
    (((contDiff_const.mul contDiff_const).mul
      (contDiff_id.continuousLinearMap_comp Complex.ofRealCLM)))

theorem hasDerivAt_suzukiApertureMode (κ x : ℝ) :
    HasDerivAt (suzukiApertureMode κ)
      (Complex.I * (κ : ℂ) * suzukiApertureMode κ x) x := by
  unfold suzukiApertureMode
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  convert ((hid.const_mul (Complex.I * (κ : ℂ))).cexp) using 1 <;> ring

/-- Smooth compactly supported approximation to an aperture exponential. -/
def suzukiBoundaryApproximant (a ε κ x : ℝ) : ℂ :=
  suzukiApertureMode κ x * (suzukiBoundaryCutoff a ε x : ℂ)

theorem contDiff_suzukiBoundaryApproximant (a ε κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiBoundaryApproximant a ε κ) := by
  unfold suzukiBoundaryApproximant
  exact (contDiff_suzukiApertureMode κ).mul
    ((contDiff_suzukiBoundaryCutoff a ε).continuousLinearMap_comp Complex.ofRealCLM)

theorem hasCompactSupport_suzukiBoundaryApproximant {a ε κ : ℝ} (hε : 0 < ε) :
    HasCompactSupport (suzukiBoundaryApproximant a ε κ) := by
  unfold suzukiBoundaryApproximant
  exact ((hasCompactSupport_suzukiBoundaryCutoff hε).comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by simp)).mul_left

/-- Zero-extended aperture mode. -/
def suzukiApertureModeCutoff (a κ : ℝ) : ℝ → ℂ :=
  (Icc (-a) a).indicator (suzukiApertureMode κ)

/-- Boundary-layer error between the aperture mode and its smooth cutoff. -/
def suzukiBoundaryError (a ε κ : ℝ) : ℝ → ℂ :=
  (Icc (-a) a).indicator fun x =>
    suzukiApertureMode κ x * (1 - suzukiBoundaryCutoff a ε x : ℂ)

theorem suzukiApertureModeCutoff_sub_approximant {a ε κ : ℝ} (hε : 0 < ε) :
    suzukiApertureModeCutoff a κ - suzukiBoundaryApproximant a ε κ =
      suzukiBoundaryError a ε κ := by
  funext x
  change (suzukiApertureModeCutoff a κ) x - suzukiBoundaryApproximant a ε κ x =
    suzukiBoundaryError a ε κ x
  by_cases hx : x ∈ Icc (-a) a
  · rw [suzukiApertureModeCutoff, suzukiBoundaryError,
      indicator_of_mem hx, indicator_of_mem hx]
    unfold suzukiBoundaryApproximant
    ring
  · rw [suzukiApertureModeCutoff, suzukiBoundaryError,
      indicator_of_notMem hx, indicator_of_notMem hx, zero_sub]
    have hout : x ≤ -a ∨ a ≤ x := by
      rw [mem_Icc, not_and_or] at hx
      exact hx.imp le_of_not_ge le_of_not_ge
    rcases hout with hout | hout
    · rw [suzukiBoundaryApproximant,
        suzukiBoundaryCutoff_eq_zero_of_le_neg hε hout]
      simp
    · rw [suzukiBoundaryApproximant,
        suzukiBoundaryCutoff_eq_zero_of_aperture_le hε hout]
      simp

theorem norm_suzukiBoundaryError_le_one (a ε κ x : ℝ) :
    ‖suzukiBoundaryError a ε κ x‖ ≤ 1 := by
  unfold suzukiBoundaryError
  by_cases hx : x ∈ Icc (-a) a
  · rw [indicator_of_mem hx, norm_mul, norm_suzukiApertureMode, one_mul]
    have hnonneg : 0 ≤ 1 - suzukiBoundaryCutoff a ε x := by
      linarith [suzukiBoundaryCutoff_le_one a ε x]
    have hnorm : ‖(1 - suzukiBoundaryCutoff a ε x : ℂ)‖ =
        1 - suzukiBoundaryCutoff a ε x := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnonneg]
    rw [hnorm]
    linarith [suzukiBoundaryCutoff_nonneg a ε x]
  · simp [hx]

theorem suzukiBoundaryError_eq_zero_of_mem_inner {a ε κ x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Icc (-a + ε) (a - ε)) :
    suzukiBoundaryError a ε κ x = 0 := by
  unfold suzukiBoundaryError
  by_cases hxa : x ∈ Icc (-a) a
  · rw [indicator_of_mem hxa, suzukiBoundaryCutoff_eq_one_of_mem_inner hε hx]
    simp
  · rw [indicator_of_notMem hxa]

theorem continuous_suzukiBoundaryErrorProfile (a ε κ : ℝ) : Continuous (fun x : ℝ =>
    suzukiApertureMode κ x * (1 - suzukiBoundaryCutoff a ε x : ℂ)) := by
  exact (contDiff_suzukiApertureMode κ).continuous.mul
    (continuous_const.sub
      ((contDiff_suzukiBoundaryCutoff a ε).continuousLinearMap_comp
        Complex.ofRealCLM).continuous)

theorem integrable_suzukiBoundaryError (a ε κ : ℝ) :
    Integrable (suzukiBoundaryError a ε κ) := by
  unfold suzukiBoundaryError
  exact ((continuous_suzukiBoundaryErrorProfile a ε κ).integrableOn_Icc).integrable_indicator
    measurableSet_Icc

def suzukiBoundaryShellMajorant (a ε x : ℝ) : ℝ :=
  (Icc (-a) (-a + ε)).indicator (fun _ => (1 : ℝ)) x +
    (Icc (a - ε) a).indicator (fun _ => (1 : ℝ)) x

theorem integrable_suzukiBoundaryShellMajorant (a ε : ℝ) :
    Integrable (suzukiBoundaryShellMajorant a ε) := by
  unfold suzukiBoundaryShellMajorant
  exact ((integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc).add
    ((integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)

theorem integral_suzukiBoundaryShellMajorant {a ε : ℝ} (hε : 0 ≤ ε) :
    (∫ x : ℝ, suzukiBoundaryShellMajorant a ε x) = 2 * ε := by
  unfold suzukiBoundaryShellMajorant
  rw [integral_add
    ((integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)
    ((integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc),
    integral_indicator_const (1 : ℝ) measurableSet_Icc,
    integral_indicator_const (1 : ℝ) measurableSet_Icc]
  simp [measureReal_def, Real.volume_Icc, hε]
  ring

theorem norm_suzukiBoundaryError_le_shellMajorant {a ε κ x : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ a) :
    ‖suzukiBoundaryError a ε κ x‖ ≤ suzukiBoundaryShellMajorant a ε x := by
  by_cases hleft : x ∈ Icc (-a) (-a + ε)
  · unfold suzukiBoundaryShellMajorant
    rw [indicator_of_mem hleft]
    exact (norm_suzukiBoundaryError_le_one a ε κ x).trans (le_add_of_nonneg_right (by
      by_cases hx : x ∈ Icc (a - ε) a <;> simp [hx]))
  by_cases hright : x ∈ Icc (a - ε) a
  · unfold suzukiBoundaryShellMajorant
    rw [indicator_of_mem hright]
    exact (norm_suzukiBoundaryError_le_one a ε κ x).trans (le_add_of_nonneg_left (by
      by_cases hx : x ∈ Icc (-a) (-a + ε) <;> simp [hx]))
  have hzero : suzukiBoundaryError a ε κ x = 0 := by
    by_cases haper : x ∈ Icc (-a) a
    · apply suzukiBoundaryError_eq_zero_of_mem_inner hε
      rw [mem_Icc] at haper ⊢
      constructor
      · by_contra hx
        apply hleft
        exact ⟨haper.1, le_of_not_ge hx⟩
      · by_contra hx
        apply hright
        exact ⟨le_of_not_ge hx, haper.2⟩
    · unfold suzukiBoundaryError
      rw [indicator_of_notMem haper]
  rw [hzero, norm_zero]
  unfold suzukiBoundaryShellMajorant
  by_cases hl : x ∈ Icc (-a) (-a + ε) <;>
    by_cases hr : x ∈ Icc (a - ε) a <;> simp [hl, hr]

/-- Source equation (3.3), before Fourier transformation: the endpoint error has `L¹` norm at
most the total boundary width. -/
theorem integral_norm_suzukiBoundaryError_le_two_mul {a ε κ : ℝ}
    (hε : 0 < ε) (hεa : ε ≤ a) :
    (∫ x : ℝ, ‖suzukiBoundaryError a ε κ x‖) ≤ 2 * ε := by
  rw [← integral_suzukiBoundaryShellMajorant hε.le]
  exact integral_mono (integrable_suzukiBoundaryError a ε κ).norm
    (integrable_suzukiBoundaryShellMajorant a ε)
    (fun x => norm_suzukiBoundaryError_le_shellMajorant hε hεa)

end RHTower

end
