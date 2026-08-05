import GaloisForLFunctions.HTGeometry.KleinGordonMultiplierAnnulus

/-!
# A clock cannot drift without a potential

The annulus of statement 392 confines every Floquet multiplier to `e^{−b|T|} ≤ |k| ≤ e^{b|T|}`. Both
extreme branches of the trichotomy need a multiplier off the unit circle, and the annulus says how much
of a potential that costs:

* decay needs a multiplier inside the unit disc, hence `e^{−b|T|} < 1`;
* instability needs one outside it, hence `1 < e^{b|T|}`.

Either way `b·|T| > 0`: **a free clock, or one whose period is instantaneous, can neither decay nor
break.** The drift of a clock is bought entirely with the strength of its background and the length of
its period — which is what the estimate the card began with says, read through the spectrum.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section NoDrift

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **A spectral radius below one is witnessed by a multiplier inside the unit disc.** -/
theorem exists_multiplier_lt_one_of_spectralRadius_lt_one (hb0 : 0 ≤ b)
    (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hlt : spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) < 1) :
    ∃ k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T), ‖k‖ < 1 := by
  obtain ⟨k₀, hk₀⟩ := spectrum_kgMonodromy_nonempty (T := T) hb0 hWb hWs
  refine ⟨k₀, hk₀, ?_⟩
  have hmem : ((‖k₀‖₊ : ℝ≥0∞))
      ≤ ⨆ k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T), (‖k‖₊ : ℝ≥0∞) :=
    le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) =>
      ((‖k‖₊ : ℝ≥0∞))) k₀ hk₀
  have hlt' : ((‖k₀‖₊ : ℝ≥0∞)) < 1 := lt_of_le_of_lt hmem hlt
  have hone : (1 : ℝ≥0∞) = ((1 : NNReal) : ℝ≥0∞) := rfl
  rw [hone, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hlt'
  simpa using hlt'

/-- **Decay costs a potential.** A clock whose spectral radius is below one has `b·|T| > 0`. -/
theorem zero_lt_of_spectralRadius_lt_one (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r)
    (hlt : spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) < 1) : 0 < b * |T| := by
  obtain ⟨k, hk, hk1⟩ := exists_multiplier_lt_one_of_spectralRadius_lt_one hb0 hWb hWs hlt
  have hge := exp_neg_le_norm_of_mem_spectrum_kgMonodromy hb0 hWb hWs hper hk
  have hexp : Real.exp (-(b * |T|)) < 1 := lt_of_le_of_lt hge hk1
  have hneg : -(b * |T|) < 0 := by
    by_contra hcon
    push Not at hcon
    have := Real.one_le_exp hcon
    linarith
  linarith

/-- **Instability costs a potential.** A multiplier outside the closed unit disc forces
`b·|T| > 0`. -/
theorem zero_lt_of_one_lt_norm_spectrum (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) (hk1 : 1 < ‖k‖) : 0 < b * |T| := by
  have hle := norm_le_of_mem_spectrum_kgMonodromy hb0 hWb hWs hk
  have hexp : 1 < Real.exp (b * |T|) := lt_of_lt_of_le hk1 hle
  by_contra hcon
  push Not at hcon
  have hle' : Real.exp (b * |T|) ≤ 1 := Real.exp_le_one_iff.mpr hcon
  linarith

end NoDrift

end GaloisForLFunctions.HTGeometry
