import Mathlib
import GaloisForLFunctions.RHTower.DeningerStationaryKahlerGerm

/-!
# The archimedean place is a cusp for every flow-invariant transverse measure

The real apex of Deninger's stationary germ is contracted transversally by the flow: the invariant
transverse coordinate `x = r²` moves by `x ↦ e^{−2t} x`, so in the logarithmic coordinate
`y = log x` the flow is the translation `y ↦ y − 2t`.  A transverse measure invariant under the
flow is therefore translation-invariant on the line, hence, by uniqueness of Haar measure, a
multiple of Lebesgue measure, which gives infinite mass to every neighbourhood `y < a` of the
apex `y = −∞`.

So the global scalar product of the Deninger–Singhof positivity, which integrates leafwise
`L²`-norms against a flow-invariant transverse measure, sees the archimedean place as a complete
cusp end of infinite transverse mass, exactly as the finite primes are cusp ends of infinite
length.  No smooth stationary-point model of the real place carries a finite invariant
transverse measure.
-/

open MeasureTheory Set

namespace RHTower

/-- A nonzero translation-invariant measure on the line, finite on compacts, has infinite mass on
every left half-line. -/
theorem measure_Iio_eq_top_of_isAddLeftInvariant (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] (hμ : μ ≠ 0) (a : ℝ) : μ (Iio a) = ⊤ := by
  have h := Measure.isAddLeftInvariant_eq_smul μ volume
  have hc : μ.addHaarScalarFactor volume ≠ 0 := by
    intro h0
    apply hμ
    rw [h, h0, zero_smul]
  rw [h, Measure.smul_apply, Real.volume_Iio, ENNReal.smul_def]
  exact ENNReal.mul_top (by exact_mod_cast hc)

/-- A nonzero translation-invariant measure on the line, finite on compacts, has infinite mass on
every right half-line. -/
theorem measure_Ioi_eq_top_of_isAddLeftInvariant (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] (hμ : μ ≠ 0) (a : ℝ) : μ (Ioi a) = ⊤ := by
  have h := Measure.isAddLeftInvariant_eq_smul μ volume
  have hc : μ.addHaarScalarFactor volume ≠ 0 := by
    intro h0
    apply hμ
    rw [h, h0, zero_smul]
  rw [h, Measure.smul_apply, Real.volume_Ioi, ENNReal.smul_def]
  exact ENNReal.mul_top (by exact_mod_cast hc)

/-- The flow of the real apex germ in the logarithmic transverse coordinate: `y ↦ y − 2t`. -/
def apexTransverseLogFlow (t : ℝ) (y : ℝ) : ℝ := y - 2 * t

/-- Invariance under the logarithmic transverse flow is translation invariance. -/
theorem isAddLeftInvariant_of_apexTransverseLogFlow_invariant (μ : Measure ℝ)
    (h : ∀ t, μ.map (apexTransverseLogFlow t) = μ) : μ.IsAddLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have h1 := h (-g / 2)
  have heq : apexTransverseLogFlow (-g / 2) = fun y => g + y := by
    funext y
    simp only [apexTransverseLogFlow]
    ring
  rw [heq] at h1
  exact h1

/-- **The archimedean place is a cusp.**  Every nonzero flow-invariant transverse measure of the
real apex, finite on compacts, gives infinite mass to every neighbourhood of the apex. -/
theorem apex_transverse_mass_eq_top (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hinv : ∀ t, μ.map (apexTransverseLogFlow t) = μ) (hμ : μ ≠ 0) (a : ℝ) :
    μ (Iio a) = ⊤ := by
  haveI := isAddLeftInvariant_of_apexTransverseLogFlow_invariant μ hinv
  exact measure_Iio_eq_top_of_isAddLeftInvariant μ hμ a

end RHTower
