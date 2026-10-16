import GaloisForLFunctions.RHTower.CHMDStripFourierReadout
import GaloisForLFunctions.RHTower.CHMDThetaTranslateGraph
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Translated cosine samples separate both Fourier directions

A local interval of translations detects both samples at a nonzero frequency.
Only the scalar exponential is differentiated; no graph generator is assumed.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDTranslation

theorem graphFourierReadout_add (p q : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    graphFourierReadout (p+q) z = graphFourierReadout p z + graphFourierReadout q z := by
  simpa only [graphFourierReadoutCLM_apply] using (graphFourierReadoutCLM z hz).map_add p q

theorem graphFourierReadout_sub (p q : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    graphFourierReadout (p-q) z = graphFourierReadout p z - graphFourierReadout q z := by
  simpa only [graphFourierReadoutCLM_apply] using (graphFourierReadoutCLM z hz).map_sub p q

theorem graphFourierReadout_smul (c : ℝ) (p : SourceGraph) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    graphFourierReadout (c • p) z = (c : ℂ) * graphFourierReadout p z := by
  simpa only [graphFourierReadoutCLM_apply, Complex.real_smul] using
    (graphFourierReadoutCLM z hz).map_smul c p

theorem paperFT_translate_real (f : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    paperFT (fun x => (CHMDTranslation.translate f t x : ℂ)) z =
      exp (I*z*t) * paperFT (fun x => (f x : ℂ)) z :=
  RHTower.paperFT_comp_sub (fun x => (f x : ℂ)) t z

def shiftedCosineReadout (p : SourceGraph) (z : ℂ) (t : ℝ) : ℂ :=
  (exp (-(I*z)*(t : ℂ)) * graphFourierReadout p z +
    exp ((I*z)*(t : ℂ)) * graphFourierReadout p (-z))/2

theorem continuous_shiftedCosineReadout {z : ℂ} (hz : |z.im| ≤ 1/2) (t : ℝ) :
    Continuous (fun p => shiftedCosineReadout p z t) := by
  have hn : |(-z).im| ≤ 1/2 := by simpa using hz
  exact ((continuous_const.mul (continuous_graphFourierReadout hz)).add
    (continuous_const.mul (continuous_graphFourierReadout hn))).div_const 2

theorem graphCosineReadout_translate_test {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {z : ℂ} (hz : |z.im| ≤ 1/2) (t : ℝ) :
    graphCosineReadout (testLift (translate f (-t))
      (contDiff_translate hf (-t)) (compact_translate hc (-t))) z =
      shiftedCosineReadout (testLift f hf hc) z t := by
  rw [graphCosineReadout_eq_half_fourier _ hz]
  simp only [graphFourierReadout_testLift, paperFT_translate_real, shiftedCosineReadout,
    Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

/-- Vanishing on a genuine interval, not an assumed nonresonant discrete shift. -/
theorem exponential_pair_separation {z A B : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℝ, |t| ≤ r → exp (-(I*z)*(t : ℂ))*A + exp ((I*z)*(t : ℂ))*B = 0) :
    A = 0 ∧ B = 0 := by
  have hs : A+B = 0 := by simpa using h 0 (by simpa using hr.le)
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hd : HasDerivAt
      (fun t : ℝ => exp (-(I*z)*(t : ℂ))*A + exp ((I*z)*(t : ℂ))*B)
      (-(I*z)*A + (I*z)*B) 0 := by
    simpa only [Pi.add_apply, Complex.ofReal_zero, mul_zero, exp_zero, one_mul, mul_one] using!
      ((hid.const_mul (-(I*z))).cexp.mul_const A).add
      ((hid.const_mul (I*z)).cexp.mul_const B)
  have he : (fun t : ℝ => exp (-(I*z)*(t : ℂ))*A + exp ((I*z)*(t : ℂ))*B) =ᶠ[𝓝 0]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
    have ht' : |t| < r := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    exact h t ht'.le
  have hd0 := hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq he)
  have hm : (2*(I*z))*A = 0 := by linear_combination (I*z)*hs - hd0
  have hA : A = 0 := (mul_eq_zero.mp hm).resolve_left
    (mul_ne_zero (by norm_num) (mul_ne_zero I_ne_zero hz))
  exact ⟨hA, by simpa only [hA, zero_add] using hs⟩

theorem shiftedCosineReadout_separates (p : SourceGraph) {z : ℂ} (hz : z ≠ 0)
    {r : ℝ} (hr : 0 < r) (h : ∀ t : ℝ, |t| ≤ r → shiftedCosineReadout p z t = 0) :
    graphFourierReadout p z = 0 ∧ graphFourierReadout p (-z) = 0 := by
  apply exponential_pair_separation hz hr
  intro t ht
  have he := h t ht
  simpa only [shiftedCosineReadout, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using he

end RHTower.CHMDDoobGraph
