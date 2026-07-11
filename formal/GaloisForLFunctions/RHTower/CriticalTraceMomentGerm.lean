import GaloisForLFunctions.RHTower.CriticalDiscEulerOrbitDensity
import GaloisForLFunctions.RHTower.TraceHankelAnalyticInstability
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Odd-to-even normalized trace germs

The normalized trace-moment passage is the divided difference `dslope` at the
functional-equation centre.  This file records the exact odd/even algebra and
the Schwarz-lemma estimate which makes division continuous only after passing
from a larger disc to a strictly smaller one.
-/

noncomputable section

namespace RHTower

open Complex Set Metric ComplexConjugate

/-- Normalized division of a centred odd trace germ. -/
def normalizedTraceMomentGerm (T : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ -dslope T 0 z

/-- The canonical odd preimage of an even trace-moment germ. -/
def oddTracePreimage (g : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ -z * g z

theorem dslope_odd_even
    (T : ℂ → ℂ) (hodd : ∀ z, T (-z) = -T z) (h0 : T 0 = 0) :
    ∀ z, dslope T 0 (-z) = dslope T 0 z := by
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [dslope_of_ne _ hnz, dslope_of_ne _ hz,
      slope_def_module, slope_def_module, h0, hodd]
    simp [smul_eq_mul]

theorem normalizedTraceMomentGerm_even
    (T : ℂ → ℂ) (hodd : ∀ z, T (-z) = -T z) (h0 : T 0 = 0) :
    ∀ z, normalizedTraceMomentGerm T (-z) = normalizedTraceMomentGerm T z := by
  intro z
  rw [normalizedTraceMomentGerm, normalizedTraceMomentGerm,
    dslope_odd_even T hodd h0]

theorem oddTracePreimage_odd
    (g : ℂ → ℂ) (heven : ∀ z, g (-z) = g z) :
    ∀ z, oddTracePreimage g (-z) = -oddTracePreimage g z := by
  intro z
  simp [oddTracePreimage, heven]

theorem oddTracePreimage_schwarz
    (g : ℂ → ℂ) (hschwarz : ∀ z, conj (g (conj z)) = g z) :
    ∀ z, conj (oddTracePreimage g (conj z)) = oddTracePreimage g z := by
  intro z
  simp [oddTracePreimage, map_mul, hschwarz]

/-- Divided difference is a left inverse to multiplication by the centred
coordinate, including at the centre where it reads the derivative. -/
theorem dslope_mul_self
    (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) :
    ∀ z, dslope (fun z ↦ z * g z) 0 z = g z := by
  intro z
  by_cases hz : z = 0
  · subst z
    rw [dslope_same]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt).deriv
  · rw [dslope_of_ne _ hz, slope_def_module]
    simp [hz, smul_eq_mul]

/-- Exact inverse identity for the normalized odd-to-even passage. -/
theorem normalizedTraceMomentGerm_oddTracePreimage
    (g : ℂ → ℂ) (hg : DifferentiableAt ℂ g 0) :
    normalizedTraceMomentGerm (oddTracePreimage g) = g := by
  funext z
  unfold normalizedTraceMomentGerm oddTracePreimage
  by_cases hz : z = 0
  · subst z
    rw [dslope_same]
    have hder := ((hasDerivAt_id (0 : ℂ)).mul hg.hasDerivAt).neg.deriv
    simpa using congrArg Neg.neg hder
  · rw [dslope_of_ne _ hz, slope_def_module]
    simp [hz, smul_eq_mul]

/-- The larger-disc/smaller-disc bound governing normalized division.  A
uniform error `R₂` on a disc of radius `R₁` becomes at most `R₂/R₁`
after division by the centred coordinate, uniformly throughout that disc. -/
theorem norm_normalizedTraceMomentGerm_le_div_of_mapsTo_ball
    {T : ℂ → ℂ} {R₁ R₂ : ℝ}
    (hT : DifferentiableOn ℂ T (ball 0 R₁))
    (hmaps : MapsTo T (ball 0 R₁) (closedBall (T 0) R₂))
    {z : ℂ} (hz : z ∈ ball 0 R₁) :
    ‖normalizedTraceMomentGerm T z‖ ≤ R₂ / R₁ := by
  rw [normalizedTraceMomentGerm, norm_neg]
  exact norm_dslope_le_div_of_mapsTo_ball hT hmaps hz

/-- Analyticity at the centre survives normalized division. -/
theorem analyticAt_normalizedTraceMomentGerm
    {T : ℂ → ℂ} (hT : AnalyticAt ℂ T 0) :
    AnalyticAt ℂ (normalizedTraceMomentGerm T) 0 := by
  rcases hT with ⟨p, hp⟩
  have hs := hp.has_fpower_series_dslope_fslope
  have hneg : HasFPowerSeriesAt
      ((-1 : ℂ) • dslope T 0) ((-1 : ℂ) • p.fslope) 0 :=
    hs.const_smul
  exact ⟨-p.fslope, by
    simpa [normalizedTraceMomentGerm] using hneg⟩

end RHTower
