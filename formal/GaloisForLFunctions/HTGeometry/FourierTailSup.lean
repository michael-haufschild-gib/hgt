import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The tail supremum of a Fourier transform

Decay statements speak of one frequency tending to infinity; an estimate valid across a whole band
needs a single number controlling every frequency outside it.  The supremum of the transform's
magnitude outside a symmetric band is that number, and it is always finite: the transform of a
function is bounded by that function's mass, whatever the frequency.

Nothing here is about any particular profile.  Which suprema actually *vanish* as the band grows is
a decay question, decided profile by profile.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped FourierTransform

/-- **The tail supremum.**  The largest transform magnitude outside a symmetric band. -/
def fourierTailSup (f : ℝ → ℂ) (u : ℝ) : ℝ :=
  ⨆ v : ℝ, if u ≤ |v| then ‖𝓕 f v‖ else 0

/-- The transform is bounded by the mass, at every frequency. -/
theorem norm_fourierIntegral_le_mass (f : ℝ → ℂ) (v : ℝ) : ‖𝓕 f v‖ ≤ ∫ y : ℝ, ‖f y‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem bddAbove_fourierTail (f : ℝ → ℂ) (u : ℝ) :
    BddAbove (Set.range fun v : ℝ => if u ≤ |v| then ‖𝓕 f v‖ else 0) := by
  refine ⟨∫ y : ℝ, ‖f y‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  by_cases h : u ≤ |v|
  · simp only [h, if_true]
    exact norm_fourierIntegral_le_mass f v
  · simp only [h, if_false]
    exact integral_nonneg fun y => norm_nonneg _

/-- Outside the band, the transform is bounded by the tail supremum. -/
theorem le_fourierTailSup (f : ℝ → ℂ) {u v : ℝ} (h : u ≤ |v|) :
    ‖𝓕 f v‖ ≤ fourierTailSup f u := by
  have hle := le_ciSup (bddAbove_fourierTail f u) v
  simpa only [fourierTailSup, h, if_true] using hle

theorem fourierTailSup_nonneg (f : ℝ → ℂ) (u : ℝ) : 0 ≤ fourierTailSup f u := by
  refine le_trans (norm_nonneg (𝓕 f (|u| + 1))) ?_
  refine le_fourierTailSup f ?_
  rw [abs_of_pos (by positivity : (0 : ℝ) < |u| + 1)]
  exact le_trans (le_abs_self u) (by linarith)

/-- A uniform bound outside the band bounds the tail supremum. -/
theorem fourierTailSup_le {f : ℝ → ℂ} {u c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : ℝ, u ≤ |v| → ‖𝓕 f v‖ ≤ c) : fourierTailSup f u ≤ c := by
  refine ciSup_le fun v => ?_
  by_cases hv : u ≤ |v|
  · simpa only [hv, if_true] using h v hv
  · simpa only [hv, if_false] using hc

/-- **The tail supremum shrinks as the band grows.** -/
theorem fourierTailSup_antitone (f : ℝ → ℂ) : Antitone (fourierTailSup f) := by
  intro u₁ u₂ hu
  exact fourierTailSup_le (fourierTailSup_nonneg f u₁)
    fun v hv => le_fourierTailSup f (le_trans hu hv)

end GaloisForLFunctions.HTGeometry
