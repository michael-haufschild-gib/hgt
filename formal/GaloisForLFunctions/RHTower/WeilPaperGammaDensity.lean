import GaloisForLFunctions.RHTower.WeilPaperGammaEnergy
import Mathlib.MeasureTheory.Group.Integral

/-!
# L1 recovery of the actual Gamma phase-energy density

Uniform bounds already supplied by the native Weil producer upgrade the
proved L1 recovery of its pole-free component to L1 recovery of its squared
norm. This is the density needed for stable simultaneous Cauchy sampling.
-/

open Complex Set Filter MeasureTheory Topology

noncomputable section
namespace RHTower.WeilWorkSettledPhase

open WeilSpectral IntegerMassRigidity PhaseLockRigidity

theorem paperGamma_abs_sq_norm_sub_le (z w : ℂ) :
    |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w))]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le z w)
    (add_nonneg (norm_nonneg z) (norm_nonneg w))

/-- Squared-norm densities vary Lipschitz-continuously on a uniformly bounded family. -/
theorem integral_abs_paperGamma_sq_norm_sub_le {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) {C : ℝ}
    (hB : ∀ᵐ y, ‖f y‖ ≤ C ∧ ‖g y‖ ≤ C) :
    (∫ y, |‖f y‖ ^ 2 - ‖g y‖ ^ 2|) ≤ (2 * C) * ∫ y, ‖f y - g y‖ := by
  have hf2 := integrable_paperGamma_norm_sq_of_bound hf (hB.mono fun _ h => h.1)
  have hg2 := integrable_paperGamma_norm_sq_of_bound hg (hB.mono fun _ h => h.2)
  rw [← integral_const_mul]
  apply integral_mono_ae (hf2.sub hg2).abs ((hf.sub hg).norm.const_mul _)
  filter_upwards [hB] with y hy
  exact (paperGamma_abs_sq_norm_sub_le _ _).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hy.1, hy.2]) (norm_nonneg _))

/-- Squared magnitude of the actual pole-free boundary component. -/
def paperGammaOddDensity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) : ℝ :=
  ‖paperGammaOdd (remainderTrace hW) y‖ ^ 2

/-- Squared magnitude recovered from an interior vertical line. -/
def paperGammaOddInteriorDensity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (x y : ℝ) : ℝ :=
  ‖paperGammaOdd (fun t => sourceRemainder hW (tracePoint x t)) y‖ ^ 2

theorem paperGammaOddDensity_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    0 ≤ paperGammaOddDensity hW y := sq_nonneg _

theorem integrable_paperGammaOddDensity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (paperGammaOddDensity hW) :=
  integrable_paperGammaOdd_norm_sq (integrable_remainderTrace hW)
    (integrable_paperGamma_remainderTrace_norm_sq hW)

@[simp] theorem paperGammaOddDensity_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (y : ℝ) :
    paperGammaOddDensity hW (-y) = paperGammaOddDensity hW y := by
  simp only [paperGammaOddDensity, norm_paperGammaOdd_neg]

theorem paperGammaOddDensity_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {y : ℝ} (hy : 0 < y) :
    paperGammaOddDensity hW y =
      ‖cexp (((Real.pi * (boundaryMeasure hW).real (Ioc (-y) y) : ℝ) : ℂ) * I) -
        paperGammaPhase y‖ ^ 2 * ‖paperUnsubtractedTrace hW (-y)‖ ^ 2 / 4 := by
  unfold paperGammaOddDensity
  rw [norm_paperGammaOdd_phase_discrepancy hW hy]
  ring

/-- Both boundary and nearby interior odd traces share a bound from native decay. -/
theorem exists_bound_paperGammaOdd_traces {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᵐ y, ‖paperGammaOdd (remainderTrace hW) y‖ ≤ C) ∧
      ∀ x : ℝ, 0 < x → x ≤ 1 → ∀ y : ℝ,
        ‖paperGammaOdd (fun t => sourceRemainder hW (tracePoint x t)) y‖ ≤ C := by
  obtain ⟨C, hC, hE, he⟩ := exists_decay_sourceRemainder_and_trace hW
  have hb : ∀ᵐ y, ‖remainderTrace hW y‖ ≤ C := he.mono fun y hy =>
    hy.trans (div_le_self hC (by nlinarith only [sq_nonneg y]))
  have hbn : ∀ᵐ y : ℝ, ‖remainderTrace hW (-y)‖ ≤ C :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hb
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hb, hbn] with y hy hyn
    exact (norm_paperGammaOdd_le _ y).trans (by linarith)
  · intro x hx hx1 y
    have hb' (t : ℝ) : ‖sourceRemainder hW (tracePoint x t)‖ ≤ C := by
      have h := hE (tracePoint x t) (by simp; linarith) (by simp; linarith)
      have h' : ‖sourceRemainder hW (tracePoint x t)‖ ≤ C / (1 + t ^ 2) :=
        by simpa [tracePoint] using h
      exact h'.trans (div_le_self hC (by nlinarith only [sq_nonneg t]))
    exact (norm_paperGammaOdd_le _ y).trans (by linarith only [hb' y, hb' (-y)])

theorem integrable_paperGammaOddInteriorDensity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) : Integrable (paperGammaOddInteriorDensity hW x) := by
  obtain ⟨C, _, _, hB⟩ := exists_bound_paperGammaOdd_traces hW
  exact integrable_paperGamma_norm_sq_of_bound
    (integrable_paperGammaOdd (integrable_paperGamma_native_slice hW hx hx1))
    (Eventually.of_forall (hB x hx hx1))

/-- All energy-density mass is recovered, not merely pointwise values or total energy. -/
theorem tendsto_integral_abs_paperGammaOddDensity_sub {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    Tendsto (fun x : ℝ => ∫ y,
      |paperGammaOddInteriorDensity hW x y - paperGammaOddDensity hW y|)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, _, hG, hF⟩ := exists_bound_paperGammaOdd_traces hW
  have ht := tendsto_integral_norm_paperGammaOdd_recovery hW
  rw [← paperGammaOdd_remainderTrace hW] at ht
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) ?_
    (by simpa using ht.const_mul (2 * C))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with x (hx : 0 < x) hx1
  apply integral_abs_paperGamma_sq_norm_sub_le
    (integrable_paperGammaOdd (integrable_paperGamma_native_slice hW hx hx1.le))
    (integrable_paperGammaOdd (integrable_remainderTrace hW))
  exact hG.mono fun y hy => ⟨hF x hx hx1.le y, hy⟩

end RHTower.WeilWorkSettledPhase
