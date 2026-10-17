import GaloisForLFunctions.BiScaleUncertainty.SignedGridEnergySources

/-!
# Signed logarithmic traces and continuum tails

Uniform decay of the signed logarithmic samples is equivalent to uniform decay
of the full normalized correlations. The energy ceiling supplies the sampling
modulus; neither direction imposes grid blindness.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

variable {K : ℝ}

/-- Uniform decay of the actual signed logarithmic trace over a source family. -/
def UniformSignedGridTail (S : Set (LevyEnergySource K)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 2 ≤ N ∧ ∀ f ∈ S, ∀ n : ℕ,
    N ≤ n → |f.correlation (Real.log (n : ℝ))| < ε

/-- Uniform two-sided decay of the full normalized correlation family. -/
def UniformCorrelationTail (S : Set (LevyEnergySource K)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧ ∀ f ∈ S, ∀ x : ℝ,
    A ≤ |x| → |f.correlation x| < ε

/-- Continuum decay controls every sufficiently distant logarithmic sample. -/
theorem uniformSignedGridTail_of_correlationTail {S : Set (LevyEnergySource K)}
    (h : UniformCorrelationTail S) : UniformSignedGridTail S := by
  intro ε hε
  obtain ⟨A, _, hA⟩ := h ε hε
  refine ⟨max 2 (logarithmicCeilNode A), le_max_left _ _, ?_⟩
  intro f hf n hn
  have hceil : logarithmicCeilNode A ≤ n := (le_max_right _ _).trans hn
  have he : Real.exp A ≤ (n : ℝ) :=
    (Nat.le_ceil (Real.exp A)).trans (by exact_mod_cast hceil)
  have hl := Real.log_le_log (Real.exp_pos A) he
  rw [Real.log_exp] at hl
  exact hA f hf _ (hl.trans (le_abs_self _))

/-- The logarithmic mesh and the energy modulus upgrade signed trace decay to full tails. -/
theorem uniformCorrelationTail_of_signedGridTail {S : Set (LevyEnergySource K)}
    (h : UniformSignedGridTail S) : UniformCorrelationTail S := by
  intro ε hε
  obtain ⟨N, _, hN⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨A, hA, he⟩ := exists_uniform_signed_sample_radius K (half_pos hε)
  refine ⟨max A (N : ℝ), hA.trans_le (le_max_left _ _), ?_⟩
  intro f hf x hx
  have hxA : A ≤ |x| := (le_max_left _ _).trans hx
  have hxN : (N : ℝ) ≤ |x| := (le_max_right _ _).trans hx
  have hn : N ≤ logarithmicCeilNode |x| := by
    have he' := Real.add_one_le_exp |x|
    have hc : Real.exp |x| ≤ (logarithmicCeilNode |x| : ℝ) := Nat.le_ceil _
    have hh : (N : ℝ) ≤ (logarithmicCeilNode |x| : ℝ) := by linarith only [hxN, he', hc]
    exact_mod_cast hh
  have hsample := he f |x| hxA
  rw [f.correlation_abs] at hsample
  have hnode := hN f hf _ hn
  have ht := abs_add_le
    (f.correlation |x| - f.correlation (Real.log (logarithmicCeilNode |x| : ℝ)))
    (f.correlation (Real.log (logarithmicCeilNode |x| : ℝ)))
  rw [sub_add_cancel, f.correlation_abs] at ht
  linarith only [ht, hsample, hnode]

/-- Signed-grid and continuum tail tightness are exactly equivalent for actual sources. -/
theorem uniformSignedGridTail_iff_correlationTail (S : Set (LevyEnergySource K)) :
    UniformSignedGridTail S ↔ UniformCorrelationTail S :=
  ⟨uniformCorrelationTail_of_signedGridTail, uniformSignedGridTail_of_correlationTail⟩

end

end GaloisForLFunctions.BiScaleUncertainty
