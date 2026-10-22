import Mathlib
import GaloisForLFunctions.RHTower.Deninger.DeningerStationaryKahlerGerm
import GaloisForLFunctions.RHTower.Deninger.DeningerAffineLeafFlow

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

/-- The logarithmic transverse coordinate of the stationary germ is moved by the flow exactly as
`apexTransverseLogFlow`. -/
theorem log_deningerGermTransverse_flow (t : ℝ) {p : ℂ × ℝ} (hp : p.2 ≠ 0) :
    Real.log (deningerGermTransverse (deningerGermFlow t p))
      = apexTransverseLogFlow t (Real.log (deningerGermTransverse p)) := by
  rw [deningerGermTransverse_flow]
  have hx : 0 < deningerGermTransverse p := by
    unfold deningerGermTransverse
    positivity
  unfold deningerReesFlow apexTransverseLogFlow
  rw [Real.log_mul (Real.exp_pos _).ne' hx.ne', Real.log_exp]
  ring

/-! ### The transverse measure atlas: generic stratum and real apex

On the fine generic source the flow dilates the suspension height, `u ↦ e^{t} u`, so the
logarithmic height is translated by `t`; at the real apex the logarithmic transverse coordinate is
translated by `−2t`.  The gluing `log x = −2 log u` intertwines the two flows, pushes the
canonical invariant measure of the generic stratum to half the canonical invariant measure of the
apex chart, and every flow-invariant transverse measure is a multiple of Lebesgue measure in the
logarithmic height, infinite at both ends of the transversal. -/

/-- The generic flow in the logarithmic height coordinate: `y ↦ y + t`. -/
def suspensionLogFlow (t : ℝ) (y : ℝ) : ℝ := y + t

/-- The logarithmic suspension height of a fine generic point is translated by the flow. -/
theorem log_deningerSuspFlow_susp {V H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (τ : ℝ) (p : DeningerFinePoint V H) :
    Real.log (deningerSuspFlow τ p).susp = suspensionLogFlow τ (Real.log p.susp) := by
  rw [deningerSuspFlow_susp, Real.log_mul (Real.exp_pos τ).ne' p.susp_pos.ne', Real.log_exp,
    suspensionLogFlow]
  ring

/-- Invariance under the logarithmic height flow is translation invariance. -/
theorem isAddLeftInvariant_of_suspensionLogFlow_invariant (μ : Measure ℝ)
    (h : ∀ t, μ.map (suspensionLogFlow t) = μ) : μ.IsAddLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have h1 := h g
  have heq : suspensionLogFlow g = fun y => g + y := by
    funext y
    simp only [suspensionLogFlow]
    ring
  rw [heq] at h1
  exact h1

/-- **Both ends of the transversal are cusps.**  A nonzero flow-invariant transverse measure of
the generic stratum, finite on compacts, has infinite mass on both ends of the logarithmic height
line. -/
theorem suspension_transverse_mass_eq_top (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hinv : ∀ t, μ.map (suspensionLogFlow t) = μ) (hμ : μ ≠ 0) (a : ℝ) :
    μ (Iio a) = ⊤ ∧ μ (Ioi a) = ⊤ := by
  haveI := isAddLeftInvariant_of_suspensionLogFlow_invariant μ hinv
  exact ⟨measure_Iio_eq_top_of_isAddLeftInvariant μ hμ a,
    measure_Ioi_eq_top_of_isAddLeftInvariant μ hμ a⟩

/-- The gluing of the logarithmic height to the logarithmic apex coordinate, `log x = −2 log u`,
the only power law compatible with the two flow weights `+1` and `−2`. -/
def apexGluing (y : ℝ) : ℝ := -2 * y

/-- The gluing intertwines the generic flow with the apex flow. -/
theorem apexGluing_intertwines (t y : ℝ) :
    apexGluing (suspensionLogFlow t y) = apexTransverseLogFlow t (apexGluing y) := by
  simp only [apexGluing, suspensionLogFlow, apexTransverseLogFlow]
  ring

/-- A power-law gluing `log x = a · log u` intertwines the two flows only for `a = −2`. -/
theorem apexGluing_exponent_unique (a : ℝ)
    (h : ∀ t y : ℝ, a * suspensionLogFlow t y = apexTransverseLogFlow t (a * y)) : a = -2 := by
  have h1 := h 1 0
  simp only [suspensionLogFlow, apexTransverseLogFlow] at h1
  linarith

/-- The gluing pushes a flow-invariant transverse measure of the generic stratum to a
flow-invariant transverse measure of the apex chart. -/
theorem map_apexGluing_invariant (μ : Measure ℝ) (hinv : ∀ t, μ.map (suspensionLogFlow t) = μ)
    (t : ℝ) : (μ.map apexGluing).map (apexTransverseLogFlow t) = μ.map apexGluing := by
  have hm1 : Measurable apexGluing := by
    unfold apexGluing
    fun_prop
  have hm2 : Measurable (apexTransverseLogFlow t) := by
    unfold apexTransverseLogFlow
    fun_prop
  have hm3 : Measurable (suspensionLogFlow t) := by
    unfold suspensionLogFlow
    fun_prop
  rw [Measure.map_map hm2 hm1]
  have hcomp : apexTransverseLogFlow t ∘ apexGluing = apexGluing ∘ suspensionLogFlow t := by
    funext y
    simp only [Function.comp]
    exact (apexGluing_intertwines t y).symm
  rw [hcomp, ← Measure.map_map hm1 hm3, hinv t]

/-- The gluing pushes Lebesgue measure to half of Lebesgue measure: the canonical apex measure
`d(log x)` is twice the canonical generic measure `d(log u)`. -/
theorem map_apexGluing_volume : volume.map apexGluing = ENNReal.ofReal (1 / 2) • volume := by
  have h := Real.map_volume_mul_left (a := (-2 : ℝ)) (by norm_num)
  unfold apexGluing
  rw [h]
  norm_num

end RHTower
