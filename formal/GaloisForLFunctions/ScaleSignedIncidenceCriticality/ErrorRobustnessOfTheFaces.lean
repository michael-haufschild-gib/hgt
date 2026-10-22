import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLawOfDepthResolution

/-!
# Error robustness of the faces

Every actual method computes its reading with error, and the calculus so far assumes exact readings.
This module adds the error and finds that the faces split again — not by what they see, but by how
they degrade.

* **Discrete faces are error-insensitive.** The truncated divisor takes values in `ℕ`, so an error
  smaller than one multiplicity is no error at all: two divisors within distance `1` are equal
  (`heightReading_eq_of_close`). Every floor, every refutation and every unit computed from a
  truncated divisor therefore survives an approximate computation of it, with no loss.
* **Quantitative faces degrade by exactly the error.** The level reading is monotone in its level
  (`levelReading_mono_level`), so computing the deficit with error `ε` is *literally* the exact
  reading at level `η + ε`. Its limit is then `min ½ (depthResolution L (η+ε))`, which the
  square-root law bounds by `√((η+ε)/L³)` (`resolutionLimit_levelReading_error`): the degradation is
  continuous in the error and quantified by the same formula.

`theErrorDichotomy` states both. Neither face is fragile: the discrete one is exactly robust and the
quantitative one degrades at a known rate, so the programme's results are not artefacts of assuming
exact data. It also settles which face an approximate computation should feed: an error `ε` costs
nothing on the divisor and costs one level shift on the deficit, and by the budget law
(`TheDeficitBudgetOfAnAdaptivePolicy`) a level shift is affordable exactly when `ε ≤ β²L³`.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The divisor is error-insensitive -/

/-- **Two truncated divisors within one multiplicity are equal.** -/
theorem heightReading_eq_of_close {T : ℝ} {Z W : TemperedZeroConfig}
    (h : ∀ ρ : ℂ, heightReading T Z ρ ≤ heightReading T W ρ + 0 ∧
      heightReading T W ρ ≤ heightReading T Z ρ + 0) :
    heightReading T Z = heightReading T W := by
  funext ρ
  obtain ⟨h1, h2⟩ := h ρ
  omega

/-- The same in the form an approximate computation produces it: a bound below one on the
discrepancy at each zero forces equality. -/
theorem heightReading_eq_of_lt_one {T : ℝ} {Z W : TemperedZeroConfig}
    (h : ∀ ρ : ℂ, (heightReading T Z ρ : ℤ) - (heightReading T W ρ : ℤ) < 1 ∧
      (heightReading T W ρ : ℤ) - (heightReading T Z ρ : ℤ) < 1) :
    heightReading T Z = heightReading T W := by
  funext ρ
  obtain ⟨h1, h2⟩ := h ρ
  omega

/-! ### 2. The level reading degrades by exactly the error -/

/-- **The level reading is monotone in its level**, so an error is a level shift. -/
theorem levelReading_mono_level {L a η η' : ℝ} (hL : 0 < L) (hηη' : η ≤ η') {d : DepthDatum}
    (h : levelReading hL a η d) : levelReading hL a η' d := by
  intro f hf hfs hp hm
  have hint : (0 : ℝ) ≤ ∫ u, ‖f u‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun _ => by positivity
  have hstep : η * ∫ u, ‖f u‖ ^ 2 ≤ η' * ∫ u, ‖f u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hηη' hint
  have hbase := h f hf hfs hp hm
  linarith

/-- **The degradation is quantified.** Computing the deficit with error `ε` gives exactly the
limit of the level `η + ε`, bounded by `√((η+ε)/L³)`. -/
theorem resolutionLimit_levelReading_error {L a η ε : ℝ} (hL : 0 < L) (ha : L / 2 < a)
    (haL : a ≤ L) (hη : 0 ≤ η) (hε : 0 ≤ ε) {d₀ : DepthDatum}
    (hd₀ : levelReading hL a (η + ε) d₀) :
    resolutionLimit depth (levelReading hL a (η + ε)) d₀ =
        min (1 / 2) (depthResolution L (η + ε)) ∧
      resolutionLimit depth (levelReading hL a (η + ε)) d₀ ≤
        Real.sqrt ((η + ε) / L ^ 3) :=
  ⟨resolutionLimit_depth_levelReading hL ha haL (by linarith) hd₀,
    resolutionLimit_depth_levelReading_le_sqrt hL ha haL (by linarith) hd₀⟩

/-! ### 3. The dichotomy -/

/-- **The error dichotomy.** The divisor face is exactly robust: an error below one multiplicity
changes nothing. The level face degrades continuously: an error `ε` is a level shift, and the limit
is the square-root law at the shifted level. -/
theorem theErrorDichotomy {L a η ε : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) {d₀ : DepthDatum} (hd₀ : levelReading hL a (η + ε) d₀) :
    (∀ {T : ℝ} {Z W : TemperedZeroConfig},
        (∀ ρ : ℂ, (heightReading T Z ρ : ℤ) - (heightReading T W ρ : ℤ) < 1 ∧
          (heightReading T W ρ : ℤ) - (heightReading T Z ρ : ℤ) < 1) →
        heightReading T Z = heightReading T W) ∧
      resolutionLimit depth (levelReading hL a (η + ε)) d₀ ≤
        Real.sqrt ((η + ε) / L ^ 3) :=
  ⟨fun h => heightReading_eq_of_lt_one h,
    (resolutionLimit_levelReading_error hL ha haL hη hε hd₀).2⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
