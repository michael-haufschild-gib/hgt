import GaloisForLFunctions.RHTower.WeilPaperGammaReflection

/-!
# Stable recovery of the Gamma pole-free Weil boundary

The paper's norm-one multiplier mechanism gives L1 contractions for both
Gamma reflection projections. They inherit the native global boundary
recovery, and the odd component is an exact weighted discrepancy between
the cumulative Weil phase and the explicit Gamma phase.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

theorem integrable_paperGammaReflection {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (paperGammaReflection f) := by
  exact hf.comp_neg.bdd_mul continuous_paperGammaPhase.aestronglyMeasurable
    (Eventually.of_forall fun y => (norm_paperGammaPhase y).le)

theorem integral_norm_paperGammaReflection (f : ℝ → ℂ) :
    (∫ y : ℝ, ‖paperGammaReflection f y‖) = ∫ y : ℝ, ‖f y‖ := by
  simp only [norm_paperGammaReflection]
  exact integral_neg_eq_self (fun y : ℝ => ‖f y‖) volume

theorem norm_paperGammaEven_le (f : ℝ → ℂ) (y : ℝ) :
    ‖paperGammaEven f y‖ ≤ (‖f y‖ + ‖f (-y)‖) / 2 := by
  simp only [paperGammaEven, norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right
    ((norm_add_le _ _).trans_eq (by rw [norm_paperGammaReflection])) (by positivity)

theorem norm_paperGammaOdd_le (f : ℝ → ℂ) (y : ℝ) :
    ‖paperGammaOdd f y‖ ≤ (‖f y‖ + ‖f (-y)‖) / 2 := by
  simp only [paperGammaOdd, norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right
    ((norm_sub_le _ _).trans_eq (by rw [norm_paperGammaReflection])) (by positivity)

theorem integrable_paperGammaEven {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (paperGammaEven f) :=
  (hf.add (integrable_paperGammaReflection hf)).div_const 2

theorem integrable_paperGammaOdd {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (paperGammaOdd f) :=
  (hf.sub (integrable_paperGammaReflection hf)).div_const 2

theorem integral_norm_paperGammaEven_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ y : ℝ, ‖paperGammaEven f y‖) ≤ ∫ y : ℝ, ‖f y‖ := by
  calc
    _ ≤ ∫ y : ℝ, (‖f y‖ + ‖f (-y)‖) / 2 :=
      integral_mono (integrable_paperGammaEven hf).norm
        ((hf.norm.add hf.comp_neg.norm).div_const 2) (norm_paperGammaEven_le f)
    _ = _ := by
      rw [integral_div, integral_add hf.norm hf.comp_neg.norm,
        integral_neg_eq_self (fun y => ‖f y‖) volume]
      ring

theorem integral_norm_paperGammaOdd_le {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ y : ℝ, ‖paperGammaOdd f y‖) ≤ ∫ y : ℝ, ‖f y‖ := by
  calc
    _ ≤ ∫ y : ℝ, (‖f y‖ + ‖f (-y)‖) / 2 :=
      integral_mono (integrable_paperGammaOdd hf).norm
        ((hf.norm.add hf.comp_neg.norm).div_const 2) (norm_paperGammaOdd_le f)
    _ = _ := by
      rw [integral_div, integral_add hf.norm hf.comp_neg.norm,
        integral_neg_eq_self (fun y => ‖f y‖) volume]
      ring

theorem paperGammaEven_sub (f g : ℝ → ℂ) :
    paperGammaEven (fun y => f y - g y) =
      fun y => paperGammaEven f y - paperGammaEven g y := by
  funext y
  simp only [paperGammaEven, paperGammaReflection_sub]
  ring

theorem paperGammaOdd_sub (f g : ℝ → ℂ) :
    paperGammaOdd (fun y => f y - g y) =
      fun y => paperGammaOdd f y - paperGammaOdd g y := by
  funext y
  simp only [paperGammaOdd, paperGammaReflection_sub]
  ring

/-- Neither projection amplifies global L1 recovery error. -/
theorem integral_norm_paperGammaOdd_sub_le {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ y : ℝ, ‖paperGammaOdd f y - paperGammaOdd g y‖) ≤
      ∫ y : ℝ, ‖f y - g y‖ := by
  simpa only [Pi.sub_def, paperGammaOdd_sub] using integral_norm_paperGammaOdd_le (hf.sub hg)

theorem integral_norm_paperGammaEven_sub_le {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ y : ℝ, ‖paperGammaEven f y - paperGammaEven g y‖) ≤
      ∫ y : ℝ, ‖f y - g y‖ := by
  simpa only [Pi.sub_def, paperGammaEven_sub] using integral_norm_paperGammaEven_le (hf.sub hg)

theorem integrable_paperGamma_native_slice {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Integrable (fun y : ℝ => sourceRemainder hW (tracePoint x y)) := by
  obtain ⟨C, _, hB, _⟩ := exists_decay_sourceRemainder_and_trace hW
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_sourceRemainder_slice hW hx).aestronglyMeasurable ?_
  exact Eventually.of_forall fun y => by
    have h := hB (tracePoint x y) (by simp; linarith) (by simp; linarith)
    simpa [tracePoint, div_eq_mul_inv] using h

/-- The pole-free boundary quantity is recovered from actual interior data in L1. -/
theorem tendsto_integral_norm_paperGammaOdd_recovery {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => ∫ y : ℝ,
      ‖paperGammaOdd (fun t => sourceRemainder hW (tracePoint x t)) y -
        paperGammaOdd (paperUnsubtractedTrace hW) y‖) (𝓝[>] 0) (𝓝 0) := by
  rw [← paperGammaOdd_remainderTrace hW]
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _)
    ?_ (tendsto_integral_norm_remainderTrace_sub hW)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x (hx : 0 < x) hx1
  exact integral_norm_paperGammaOdd_sub_le (integrable_paperGamma_native_slice hW hx hx1.le)
    (integrable_remainderTrace hW)

theorem tendsto_integral_norm_paperGammaEven_recovery {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => ∫ y : ℝ,
      ‖paperGammaEven (fun t => sourceRemainder hW (tracePoint x t)) y -
        paperGammaEven (remainderTrace hW) y‖) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _)
    ?_ (tendsto_integral_norm_remainderTrace_sub hW)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x (hx : 0 < x) hx1
  exact integral_norm_paperGammaEven_sub_le (integrable_paperGamma_native_slice hW hx hx1.le)
    (integrable_remainderTrace hW)

/-- The pole-free component measures the actual cumulative phase against the Gamma phase. -/
theorem paperGammaOdd_phase_discrepancy {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) :
    paperGammaOdd (remainderTrace hW) y =
      (cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) -
        paperGammaPhase y) * paperUnsubtractedTrace hW (-y) / 2 := by
  rw [paperGammaOdd_remainderTrace]
  have hd : tracePoint 0 (-y) * (tracePoint 0 (-y) - 1) =
      tracePoint 0 y * (tracePoint 0 y - 1) := by
    unfold tracePoint
    push_cast
    ring
  dsimp [paperGammaOdd, paperGammaReflection, paperUnsubtractedTrace]
  rw [sourceTrace_reflection hW hy, hd]
  ring

theorem norm_paperGammaOdd_phase_discrepancy {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) :
    ‖paperGammaOdd (remainderTrace hW) y‖ =
      ‖cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) -
        paperGammaPhase y‖ * ‖paperUnsubtractedTrace hW (-y)‖ / 2 := by
  rw [paperGammaOdd_phase_discrepancy hW hy, norm_div, norm_mul, Complex.norm_ofNat]

end RHTower.WeilWorkSettledPhase
