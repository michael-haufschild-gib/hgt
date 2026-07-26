/-
Reciprocity for the across-class sum, and the critical point it lands on.

Poisson summation applied to `Σ_(d ≤ D) e(β√d)` produces, for each frequency `h`, a stationary point
at `d = β²/(4h²)`, present when `h ≥ h₀ := β/(2√D)`.  The stationary contribution has amplitude
`β/h^(3/2)` and phase `β²/(4h)`, so

    Σ_(d ≤ D) e(β√d)  ≈  Σ_(h ≥ h₀) (β / h^(3/2)) e(β² / (4h)) .

Two readings of this dual sum at the frontier's parameters `β ≍ N`, `D ≍ N^(2/3)`.

* **The stationary-phase count reproduces the trivial bound exactly.**  Summing the amplitudes over
  `h ≍ h₀` gives `β / h₀^(1/2) = β^(1/2) D^(1/4) = N^(1/2) N^(1/6) = N^(2/3)`.  This is an *upper*
  bound only — it counts amplitudes without using the dual phase.

* **The dual phase sits at the same critical point.**  With `h₀ ≍ N^(2/3)` the dual amplitude is
  `β/h₀^(3/2) ≍ 1`, the dual length is `≍ N^(2/3)`, and the dual second derivative is
  `g''(h) = β²/(2h³) ≍ N²/N² ≍ 1`.

So reciprocity maps the across-class sum to another sum with `|g''| ≍ 1` — **the same critical point
the original occupies**, and the same one at which the second-derivative test is vacuous.  Any saving
must come from the dual sum's own cancellation, and the transform does not move the problem off its
critical point.
-/
import GaloisForLFunctions.HTGeometry.AcrossClassExponentPair

namespace HTGeometry

/-! ### The stationary-phase count -/

/-- Exponent of the stationary-phase amplitude count `β^(1/2) D^(1/4)`. -/
def stationaryCountExponent : ℚ := acrossPhaseExponent / 2 + acrossRangeExponent / 4

/-- **It reproduces the trivial bound exactly.** -/
@[simp] theorem stationaryCount_is_trivial :
    stationaryCountExponent = acrossRangeExponent := by
  unfold stationaryCountExponent acrossPhaseExponent acrossRangeExponent; norm_num

/-- Numerically `2/3`. -/
theorem stationaryCount_eq : stationaryCountExponent = 2 / 3 := by
  rw [stationaryCount_is_trivial]; unfold acrossRangeExponent; rfl

/-! ### The dual sum -/

/-- Exponent of the smallest frequency carrying a stationary point, `h₀ = β/(2√D)`. -/
def dualFrequencyExponent : ℚ := acrossPhaseExponent - acrossRangeExponent / 2

/-- **It is `2/3`, equal to the summation range.** -/
@[simp] theorem dualFrequency_eq : dualFrequencyExponent = 2 / 3 := by
  unfold dualFrequencyExponent acrossPhaseExponent acrossRangeExponent; norm_num

/-- Exponent of the dual amplitude `β / h₀^(3/2)`. -/
def dualAmplitudeExponent : ℚ := acrossPhaseExponent - 3 * dualFrequencyExponent / 2

/-- **The dual amplitude is bounded: exponent `0`.** -/
@[simp] theorem dualAmplitude_eq : dualAmplitudeExponent = 0 := by
  unfold dualAmplitudeExponent acrossPhaseExponent
  rw [dualFrequency_eq]; norm_num

/-- Exponent of the dual second derivative `g'' = β²/(2h³)`. -/
def dualSecondDerivExponent : ℚ := 2 * acrossPhaseExponent - 3 * dualFrequencyExponent

/-- **It is `0` — the dual sum sits at `|g''| ≍ 1`, the critical point.** -/
@[simp] theorem dualSecondDeriv_eq : dualSecondDerivExponent = 0 := by
  unfold dualSecondDerivExponent acrossPhaseExponent
  rw [dualFrequency_eq]; norm_num

/-- **And that is the same critical point the original sum occupies.** -/
theorem dual_matches_original :
    dualSecondDerivExponent = acrossDerivExponent 2 := by
  rw [dualSecondDeriv_eq, acrossDeriv_second]

/-! ### The transform does not move the problem -/

/-- The dual sum's trivial bound: amplitude times length. -/
def dualTrivialExponent : ℚ := dualAmplitudeExponent + dualFrequencyExponent

/-- **It is `2/3` — the same trivial bound as before the transform.** -/
@[simp] theorem dualTrivial_eq : dualTrivialExponent = 2 / 3 := by
  unfold dualTrivialExponent
  rw [dualAmplitude_eq, dualFrequency_eq]; norm_num

/-- **Reciprocity is exponent-neutral**: trivial bound, second-derivative parameter and all. -/
theorem reciprocity_neutral :
    dualTrivialExponent = acrossRangeExponent ∧
      dualSecondDerivExponent = acrossDerivExponent 2 ∧
      stationaryCountExponent = acrossRangeExponent := by
  refine ⟨?_, dual_matches_original, stationaryCount_is_trivial⟩
  rw [dualTrivial_eq]; unfold acrossRangeExponent; rfl

/-- **What survives.**  The exponent-pair bound of the previous file remains the best available, and
reciprocity supplies no improvement: it returns a sum with the same length, the same trivial bound and
the same critical second derivative. -/
theorem reciprocity_gives_nothing :
    acrossPairBound (17 / 21) < dualTrivialExponent ∧
      dualTrivialExponent = acrossRangeExponent := by
  rw [dualTrivial_eq, bourgain_across_bound]
  refine ⟨by norm_num, ?_⟩
  unfold acrossRangeExponent; rfl

/-- **The conjugation principle, once more.**  Poisson on the across-class sum returns a sum at the
same critical point — the fourth independent confirmation, after the length reflection, the scale
reflection, and the chirp. -/
theorem conjugation_principle_again :
    dualSecondDerivExponent = 0 ∧ acrossDerivExponent 2 = 0 ∧
      dualTrivialExponent = acrossRangeExponent :=
  ⟨dualSecondDeriv_eq, acrossDeriv_second, reciprocity_neutral.1⟩

end HTGeometry
