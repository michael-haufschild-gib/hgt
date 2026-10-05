import GaloisForLFunctions.RHTower.CCMNilpotentContractionSine
import GaloisForLFunctions.RHTower.CCMApertureCorrelationKernel
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell

/-!
# The actual aperture translation is a finite nilpotent chain

Compression powers equal translated representatives with the original aperture
cutoff. Once the accumulated displacement exceeds the diameter, the power is
zero. The general sine bound is therefore discharged on the actual aperture
operator, for every complex source vector.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct
noncomputable section
namespace RHTower

def ccmApertureForwardTranslation (a : SuzukiPositiveAperture) (h : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmApertureCompression a (logTranslationCLM h)

theorem norm_ccmApertureForwardTranslation_le_one (a : SuzukiPositiveAperture) (h : ℝ) :
    ‖ccmApertureForwardTranslation a h‖ ≤ 1 :=
  (norm_ccmApertureCompression_le a _).trans (norm_logTranslationCLM_le_one h)

theorem ccmApertureForwardTranslation_coeFn (a : SuzukiPositiveAperture) (h : ℝ)
    (f : suzukiApertureHilbert a) :
    ((ccmApertureForwardTranslation a h f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => f.1 (x + h)) := by
  rw [ccmApertureForwardTranslation, ccmApertureCompression_val]
  have ht : (logTranslationCLM h f.1 : ℝ → ℂ) =ᵐ[volume] fun x => f.1 (x + h) :=
    (Lp.coeFn_compMeasurePreserving f.1
      (MellinL2.realTranslation_measurePreserving h)).trans
        (Eventually.of_forall fun _ => rfl)
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) (logTranslationCLM h f.1), ht] with x hc ht
  rw [hc]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, ht]
  · simp only [indicator_of_notMem hx]

/-- Convexity of the aperture keeps every intermediate step inside the chain. -/
theorem ccmApertureForwardTranslation_pow_coeFn (a : SuzukiPositiveAperture)
    (h : Ioi (0 : ℝ)) (n : ℕ) (f : suzukiApertureHilbert a) :
    (((ccmApertureForwardTranslation a h.1 ^ n) f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => f.1 (x + (n : ℝ) * h.1)) := by
  let T := ccmApertureForwardTranslation a h.1
  induction n with
  | zero =>
    have hc := indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) f.1
    rw [indicatorCutoff_suzukiApertureHilbert] at hc
    simpa only [pow_zero, one_apply_eq_self, Nat.cast_zero, zero_mul, add_zero] using hc
  | succ n ih =>
    have hs := ih.comp_tendsto
      (MellinL2.realTranslation_measurePreserving h.1).quasiMeasurePreserving.tendsto_ae
    have hz := (MellinL2.realTranslation_measurePreserving
      ((n + 1 : ℕ) * h.1)).quasiMeasurePreserving.tendsto_ae.eventually
        (suzukiApertureHilbert_ae_zero_outside a f)
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [ccmApertureForwardTranslation_coeFn a h.1 ((T ^ n) f), hs, hz]
      with x ht hs hz
    change ((T ^ n) f : SoninL2) (x + h.1) =
      (centralInterval a.1).indicator (fun y => f.1 (y + (n : ℝ) * h.1)) (x + h.1) at hs
    change a.1 < |x + ((n + 1 : ℕ) : ℝ) * h.1| →
      f.1 (x + ((n + 1 : ℕ) : ℝ) * h.1) = 0 at hz
    rw [ht]
    by_cases hx : x ∈ centralInterval a.1
    · simp only [indicator_of_mem hx]
      rw [hs]
      have hxlo : -a.1 ≤ x := hx.1
      have hp : 0 < h.1 := h.property
      by_cases hxh : x + h.1 ∈ centralInterval a.1
      · rw [indicator_of_mem hxh]
        congr 1
        push_cast
        ring
      · rw [indicator_of_notMem hxh]
        have hgt : a.1 < x + h.1 := by
          by_contra hn
          apply hxh
          change -a.1 ≤ x + h.1 ∧ x + h.1 ≤ a.1
          exact ⟨by linarith only [hxlo, hp], le_of_not_gt hn⟩
        have hn : 0 ≤ (n : ℝ) * h.1 := mul_nonneg (Nat.cast_nonneg _) h.property.le
        have hlarge : a.1 < x + ((n + 1 : ℕ) : ℝ) * h.1 := by
          push_cast
          nlinarith only [hgt, hn]
        exact (hz (lt_of_lt_of_le hlarge (le_abs_self _))).symm
    · simp only [indicator_of_notMem hx]

/-- Nilpotence is an actual support consequence, with no spectral premise. -/
theorem ccmApertureForwardTranslation_pow_eq_zero (a : SuzukiPositiveAperture)
    (h : Ioi (0 : ℝ)) (n : ℕ) (hn : 2 * a.1 < (n : ℝ) * h.1) :
    ccmApertureForwardTranslation a h.1 ^ n = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change ((ccmApertureForwardTranslation a h.1 ^ n) f : SoninL2) = (0 : SoninL2)
  apply Lp.ext
  have hz := (MellinL2.realTranslation_measurePreserving
    ((n : ℝ) * h.1)).quasiMeasurePreserving.tendsto_ae.eventually
      (suzukiApertureHilbert_ae_zero_outside a f)
  filter_upwards [ccmApertureForwardTranslation_pow_coeFn a h n f, hz,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x ht hz h0
  change a.1 < |x + (n : ℝ) * h.1| → f.1 (x + (n : ℝ) * h.1) = 0 at hz
  rw [ht, h0]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    have hxlo : -a.1 ≤ x := hx.1
    exact hz (lt_of_lt_of_le (by linarith only [hxlo, hn]) (le_abs_self _))
  · rw [indicator_of_notMem hx]
    rfl

/-- Sharp full-complex source correlation bound for every admissible finite chain. -/
theorem norm_ccmApertureCorrelation_le_chain (a : SuzukiPositiveAperture)
    (h : Ioi (0 : ℝ)) (n : ℕ) (hn : 2 * a.1 < (n : ℝ) * h.1)
    (f : suzukiApertureHilbert a) :
    ‖ccmApertureCorrelation a f h.1‖ ≤
      Real.cos (Real.pi / ((n : ℝ) + 1)) * ‖f‖ ^ 2 := by
  have hb := norm_inner_nilpotent_contraction_le_sine
    (ccmApertureForwardTranslation a h.1)
    (norm_ccmApertureForwardTranslation_le_one a h.1) n
    (ccmApertureForwardTranslation_pow_eq_zero a h n hn) f
  simpa only [ccmApertureForwardTranslation, inner_ccmApertureCompression,
    ccmApertureCorrelation] using hb

theorem norm_ccmApertureCorrelation_neg (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (h : ℝ) :
    ‖ccmApertureCorrelation a f (-h)‖ = ‖ccmApertureCorrelation a f h‖ := by
  unfold ccmApertureCorrelation
  rw [inner_logTranslationCLM (-h), neg_neg]
  exact norm_inner_symm (𝕜 := ℂ) f.1 (logTranslationCLM h f.1)

end RHTower
