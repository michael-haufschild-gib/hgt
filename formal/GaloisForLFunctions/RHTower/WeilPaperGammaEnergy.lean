import GaloisForLFunctions.RHTower.WeilPaperGammaBoundary
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Finite and recoverable Gamma reflection energy for WP05

The native decay theorem supplies every integrability premise. Gamma reflection
splits the actual remainder's squared-norm integral exactly. The odd energy is
pole-free, and its boundary function is recoverable in L2 from the interior.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

/-- Squared-norm integral; all uses below on actual traces have integrability proofs. -/
def paperGammaEnergy (f : ℝ → ℂ) : ℝ := ∫ y : ℝ, ‖f y‖ ^ 2

theorem paperGammaEnergy_nonneg (f : ℝ → ℂ) : 0 ≤ paperGammaEnergy f :=
  integral_nonneg fun _ => sq_nonneg _

theorem paperGamma_projection_parallelogram (f : ℝ → ℂ) (y : ℝ) :
    ‖paperGammaEven f y‖ ^ 2 + ‖paperGammaOdd f y‖ ^ 2 =
      (‖f y‖ ^ 2 + ‖f (-y)‖ ^ 2) / 2 := by
  have h := parallelogram_law_with_norm ℂ (f y) (paperGammaReflection f y)
  rw [norm_paperGammaReflection] at h
  simp only [paperGammaEven, paperGammaOdd, norm_div, Complex.norm_ofNat]
  nlinarith only [h]

private theorem projection_norm_sq_le (f : ℝ → ℂ) (y : ℝ) :
    ‖paperGammaEven f y‖ ^ 2 ≤ (‖f y‖ ^ 2 + ‖f (-y)‖ ^ 2) / 2 ∧
      ‖paperGammaOdd f y‖ ^ 2 ≤ (‖f y‖ ^ 2 + ‖f (-y)‖ ^ 2) / 2 := by
  have h := paperGamma_projection_parallelogram f y
  constructor <;> nlinarith only [h, sq_nonneg ‖paperGammaEven f y‖,
    sq_nonneg ‖paperGammaOdd f y‖]

theorem integrable_paperGammaEven_norm_sq {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : Integrable (fun y => ‖f y‖ ^ 2)) :
    Integrable (fun y => ‖paperGammaEven f y‖ ^ 2) := by
  refine ((h2.add h2.comp_neg).div_const 2).mono'
    ((integrable_paperGammaEven hf).aestronglyMeasurable.norm.pow 2) ?_
  exact Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖paperGammaEven f y‖), Pi.add_apply] using
      (projection_norm_sq_le f y).1

theorem integrable_paperGammaOdd_norm_sq {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : Integrable (fun y => ‖f y‖ ^ 2)) :
    Integrable (fun y => ‖paperGammaOdd f y‖ ^ 2) := by
  refine ((h2.add h2.comp_neg).div_const 2).mono'
    ((integrable_paperGammaOdd hf).aestronglyMeasurable.norm.pow 2) ?_
  exact Eventually.of_forall fun y => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖paperGammaOdd f y‖), Pi.add_apply] using
      (projection_norm_sq_le f y).2

/-- Exact energy decomposition, with both integrals finite. -/
theorem paperGammaEnergy_decomposition {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : Integrable (fun y => ‖f y‖ ^ 2)) :
    paperGammaEnergy (paperGammaEven f) + paperGammaEnergy (paperGammaOdd f) =
      paperGammaEnergy f := by
  unfold paperGammaEnergy
  rw [← integral_add (integrable_paperGammaEven_norm_sq hf h2)
    (integrable_paperGammaOdd_norm_sq hf h2)]
  simp_rw [paperGamma_projection_parallelogram]
  rw [integral_div, integral_add h2 h2.comp_neg,
    integral_neg_eq_self (fun y => ‖f y‖ ^ 2) volume]
  ring

theorem paperGammaEnergy_odd_le {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : Integrable (fun y => ‖f y‖ ^ 2)) :
    paperGammaEnergy (paperGammaOdd f) ≤ paperGammaEnergy f := by
  have he := paperGammaEnergy_decomposition hf h2
  linarith only [he, paperGammaEnergy_nonneg (paperGammaEven f)]

theorem paperGammaEnergy_even_le {f : ℝ → ℂ} (hf : Integrable f)
    (h2 : Integrable (fun y => ‖f y‖ ^ 2)) :
    paperGammaEnergy (paperGammaEven f) ≤ paperGammaEnergy f := by
  have he := paperGammaEnergy_decomposition hf h2
  linarith only [he, paperGammaEnergy_nonneg (paperGammaOdd f)]

private theorem norm_sq_le_of_bound {z : ℂ} {C : ℝ} (h : ‖z‖ ≤ C) :
    ‖z‖ ^ 2 ≤ C * ‖z‖ := by
  nlinarith only [mul_le_mul_of_nonneg_right h (norm_nonneg z)]

theorem integrable_paperGamma_norm_sq_of_bound {f : ℝ → ℂ} (hf : Integrable f)
    {C : ℝ} (hB : ∀ᵐ y, ‖f y‖ ≤ C) : Integrable (fun y => ‖f y‖ ^ 2) := by
  refine (hf.norm.const_mul C).mono' (hf.aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards [hB] with y hy
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f y‖)] using norm_sq_le_of_bound hy

theorem paperGammaEnergy_le_integral_norm {f : ℝ → ℂ} (hf : Integrable f)
    {C : ℝ} (hB : ∀ᵐ y, ‖f y‖ ≤ C) :
    paperGammaEnergy f ≤ C * ∫ y : ℝ, ‖f y‖ := by
  rw [← integral_const_mul]
  exact integral_mono_ae (integrable_paperGamma_norm_sq_of_bound hf hB)
    (hf.norm.const_mul C) (hB.mono fun _ hy => norm_sq_le_of_bound hy)

/-- Native Weil decay supplies finite energy without an additional analytic premise. -/
theorem integrable_paperGamma_remainderTrace_norm_sq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) : Integrable (fun y => ‖remainderTrace hW y‖ ^ 2) := by
  obtain ⟨C, hC, _, hB⟩ := exists_decay_sourceRemainder_and_trace hW
  apply integrable_paperGamma_norm_sq_of_bound (integrable_remainderTrace hW)
  filter_upwards [hB] with y hy
  exact hy.trans (div_le_self hC (by nlinarith only [sq_nonneg y]))

/-- The odd summand is exactly the pole-free part of the unsubtracted actual source. -/
theorem paperGammaEnergy_native_decomposition {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    paperGammaEnergy (paperGammaEven (remainderTrace hW)) +
      paperGammaEnergy (paperGammaOdd (paperUnsubtractedTrace hW)) =
        paperGammaEnergy (remainderTrace hW) := by
  rw [← paperGammaOdd_remainderTrace hW]
  exact paperGammaEnergy_decomposition (integrable_remainderTrace hW)
    (integrable_paperGamma_remainderTrace_norm_sq hW)

private theorem eventually_native_error_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝[>] (0 : ℝ),
      Integrable (fun y => sourceRemainder hW (tracePoint x y) - remainderTrace hW y) ∧
      ∀ᵐ y, ‖sourceRemainder hW (tracePoint x y) - remainderTrace hW y‖ ≤ C := by
  obtain ⟨C, hC, hE, he⟩ := exists_decay_sourceRemainder_and_trace hW
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x (hx : 0 < x) hx1
  refine ⟨(integrable_paperGamma_native_slice hW hx hx1.le).sub
    (integrable_remainderTrace hW), ?_⟩
  filter_upwards [he] with y hy
  have hb := hE (tracePoint x y) (by simp; linarith) (by simp; linarith)
  have hb' : ‖sourceRemainder hW (tracePoint x y)‖ ≤ C / (1 + y ^ 2) :=
    by simpa [tracePoint] using hb
  have hdiv : C / (1 + y ^ 2) ≤ C :=
    div_le_self hC (by nlinarith only [sq_nonneg y])
  exact (norm_sub_le _ _).trans (by linarith)

/-- Actual interior-to-boundary recovery holds in L2 as well as L1. -/
theorem tendsto_paperGammaEnergy_native_error {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => paperGammaEnergy
      (fun y => sourceRemainder hW (tracePoint x y) - remainderTrace hW y))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := eventually_native_error_bound hW
  apply squeeze_zero' (Eventually.of_forall fun _ => paperGammaEnergy_nonneg _) ?_
    (by simpa using (tendsto_integral_norm_remainderTrace_sub hW).const_mul C)
  exact hC.mono fun _ hx => paperGammaEnergy_le_integral_norm hx.1 hx.2

/-- The pole-free phase discrepancy is recovered globally in squared norm. -/
theorem tendsto_paperGammaEnergy_odd_recovery {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => paperGammaEnergy (fun y =>
      paperGammaOdd (fun t => sourceRemainder hW (tracePoint x t)) y -
        paperGammaOdd (paperUnsubtractedTrace hW) y)) (𝓝[>] 0) (𝓝 0) := by
  rw [← paperGammaOdd_remainderTrace hW]
  obtain ⟨C, _, hC⟩ := eventually_native_error_bound hW
  apply squeeze_zero' (Eventually.of_forall fun _ => paperGammaEnergy_nonneg _) ?_
    (tendsto_paperGammaEnergy_native_error hW)
  filter_upwards [hC] with x hx
  simpa only [paperGammaOdd_sub] using
    paperGammaEnergy_odd_le hx.1 (integrable_paperGamma_norm_sq_of_bound hx.1 hx.2)

theorem tendsto_paperGammaEnergy_even_recovery {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => paperGammaEnergy (fun y =>
      paperGammaEven (fun t => sourceRemainder hW (tracePoint x t)) y -
        paperGammaEven (remainderTrace hW) y)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := eventually_native_error_bound hW
  apply squeeze_zero' (Eventually.of_forall fun _ => paperGammaEnergy_nonneg _) ?_
    (tendsto_paperGammaEnergy_native_error hW)
  filter_upwards [hC] with x hx
  simpa only [paperGammaEven_sub] using
    paperGammaEnergy_even_le hx.1 (integrable_paperGamma_norm_sq_of_bound hx.1 hx.2)

/-- The norm of the odd component is even, despite the nonconstant Gamma phase. -/
@[simp] theorem norm_paperGammaOdd_neg (f : ℝ → ℂ) (y : ℝ) :
    ‖paperGammaOdd f (-y)‖ = ‖paperGammaOdd f y‖ := by
  have h := congrArg norm (congrFun (paperGammaReflection_odd f) y)
  simpa only [norm_paperGammaReflection, norm_neg] using h

theorem paperGammaEnergy_odd_eq_positive_half (f : ℝ → ℂ) :
    paperGammaEnergy (paperGammaOdd f) =
      2 * ∫ y in Ioi (0 : ℝ), ‖paperGammaOdd f y‖ ^ 2 := by
  have ha : (fun y : ℝ => ‖paperGammaOdd f |y|‖ ^ 2) =
      fun y => ‖paperGammaOdd f y‖ ^ 2 := by
    funext y
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_nonpos hy, norm_paperGammaOdd_neg]
  calc
    _ = ∫ y : ℝ, ‖paperGammaOdd f |y|‖ ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => (congrFun ha y).symm
    _ = _ := integral_comp_abs (f := fun y => ‖paperGammaOdd f y‖ ^ 2)

/-- Exact positive-height formula for the pole-free energy: squared phase mismatch,
weighted by the actual source amplitude, with no pole coefficient remaining. -/
theorem paperGammaEnergy_native_phase_formula {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    paperGammaEnergy (paperGammaOdd (remainderTrace hW)) =
      (1 / 2 : ℝ) * ∫ y in Ioi (0 : ℝ),
        ‖cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) -
          paperGammaPhase y‖ ^ 2 * ‖paperUnsubtractedTrace hW (-y)‖ ^ 2 := by
  rw [paperGammaEnergy_odd_eq_positive_half, ← integral_const_mul,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  rw [norm_paperGammaOdd_phase_discrepancy hW hy]
  ring

/-- Exact kernel: zero odd component means an even Gamma-normalized trace. -/
theorem paperGammaOdd_eq_zero_iff (f : ℝ → ℂ) (y : ℝ) :
    paperGammaOdd f y = 0 ↔
      f y / paperPoleGamma y = f (-y) / paperPoleGamma (-y) := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  simp only [paperGammaOdd, paperGammaReflection, paperGammaPhase,
    div_eq_zero_iff, h2, or_false, sub_eq_zero]
  rw [show paperPoleGamma y / paperPoleGamma (-y) * f (-y) =
    f (-y) * paperPoleGamma y / paperPoleGamma (-y) by ring,
    eq_div_iff (paperPoleGamma_ne_zero (-y)),
    div_eq_div_iff (paperPoleGamma_ne_zero y) (paperPoleGamma_ne_zero (-y))]

/-- The finite native energy detects precisely failure of normalized reflection symmetry. -/
theorem paperGammaEnergy_native_eq_zero_iff {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    paperGammaEnergy (paperGammaOdd (remainderTrace hW)) = 0 ↔
      ∀ᵐ y : ℝ, remainderTrace hW y / paperPoleGamma y =
        remainderTrace hW (-y) / paperPoleGamma (-y) := by
  unfold paperGammaEnergy
  rw [integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) 
    (integrable_paperGammaOdd_norm_sq (integrable_remainderTrace hW)
      (integrable_paperGamma_remainderTrace_norm_sq hW))]
  change (∀ᵐ y : ℝ, ‖paperGammaOdd (remainderTrace hW) y‖ ^ 2 = 0) ↔ _
  apply Filter.eventually_congr
  exact Eventually.of_forall fun y => by
    rw [sq_eq_zero_iff, norm_eq_zero, paperGammaOdd_eq_zero_iff]

end RHTower.WeilWorkSettledPhase
