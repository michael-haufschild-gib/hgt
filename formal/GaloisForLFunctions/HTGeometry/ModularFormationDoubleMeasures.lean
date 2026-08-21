import GaloisForLFunctions.HTGeometry.ModularFormationDouble
import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift

/-!
# The modular formation double as a pair of measures

The two-sheet reflection closure lifts from densities to measures: a reflection-invariant dominating
measure carries the sheet weights to a pair of laws exchanged by reflection, and the canonical
common-recovery lift then transports that exchange to formed packets without losing information.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Pushing a density measure forward along a measure-preserving involution precomposes the
density. -/
theorem map_withDensity_of_involution {ω : Measure X} {R : X → X}
    (hRm : Measurable R) (hRinv : ∀ x, R (R x) = x) (hω : Measure.map R ω = ω)
    {g : X → ℝ≥0∞} (hg : Measurable g) :
    Measure.map R (ω.withDensity g) = ω.withDensity (fun x => g (R x)) := by
  ext s hs
  rw [Measure.map_apply hRm hs, withDensity_apply _ (hRm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hRm hs), ← lintegral_indicator hs]
  have hinv : ∫⁻ x, ((R ⁻¹' s).indicator g) x ∂ω
      = ∫⁻ x, ((R ⁻¹' s).indicator g) (R x) ∂ω := by
    conv_lhs => rw [← hω]
    exact lintegral_map (hg.indicator (hRm hs)) hRm
  rw [hinv]
  congr 1
  funext x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem (by simpa [Set.mem_preimage, hRinv] using hx),
      Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_preimage, hRinv] using hx),
      Set.indicator_of_notMem hx]

variable {b : X → ℝ} {R : X → X} {T : X → ℝ}

/-- The law of one formation sheet. -/
def sheetMeasure (ω : Measure X) (b : X → ℝ) (R : X → X) (T : X → ℝ) (a ε : ℝ) : Measure X :=
  ω.withDensity fun x => ENNReal.ofReal (sheetWeight b R T a ε x)

/-- **(FEL.D4) for measures.**  Reflection negates the tilt and toggles the sheet. -/
theorem map_sheetMeasure {ω : Measure X} (hRm : Measurable R) (hRinv : ∀ x, R (R x) = x)
    (hω : Measure.map R ω = ω) (hodd : ∀ x, T (R x) = -T x) (a ε : ℝ)
    (hmeas : Measurable fun x => ENNReal.ofReal (sheetWeight b R T a ε x)) :
    Measure.map R (sheetMeasure ω b R T a ε) = sheetMeasure ω b R T (-a) (-ε) := by
  rw [sheetMeasure, sheetMeasure, map_withDensity_of_involution hRm hRinv hω hmeas]
  congr 1
  funext x
  congr 1
  have h := sheetWeight_reflect (b := b) (R := R) (T := T) hRinv hodd (-a) (-ε) x
  rw [neg_neg, neg_neg] at h
  exact h

/-- **Corollary 3.2** (FEL.D6).  The canonical common-recovery lift of the reflection sends the
formed sheet packet to the formed opposite-sheet packet and preserves every pairwise relative
entropy. -/
theorem formationLift_sheetMeasure {H : Type*} [MeasurableSpace H]
    {ω : Measure X} (hRm : Measurable R) (hRinv : ∀ x, R (R x) = x)
    (hω : Measure.map R ω = ω) (hodd : ∀ x, T (R x) = -T x)
    (κ : Kernel X H) [IsMarkovKernel κ] (a ε : ℝ)
    (hmeas : Measurable fun x => ENNReal.ofReal (sheetWeight b R T a ε x))
    [IsFiniteMeasure (sheetMeasure ω b R T a ε)] :
    formationLiftKernel κ R hRm ∘ₘ splitFormation (sheetMeasure ω b R T a ε) κ
      = splitFormation (sheetMeasure ω b R T (-a) (-ε)) κ := by
  rw [formationLiftKernel_naturality (sheetMeasure ω b R T a ε) κ R hRm,
    map_sheetMeasure hRm hRinv hω hodd a ε hmeas]

/-- **Corollary 3.2, information neutrality.**  The lift is a relative-entropy isometry on formed
sheet packets. -/
theorem klDiv_formationLift_sheetMeasure {H : Type*} [MeasurableSpace H]
    (hRm : Measurable R) (hRinv : ∀ x, R (R x) = x)
    (κ : Kernel X H) [IsMarkovKernel κ] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (formationLiftKernel κ R hRm ∘ₘ splitFormation μ κ)
        (formationLiftKernel κ R hRm ∘ₘ splitFormation ν κ)
      = klDiv (splitFormation μ κ) (splitFormation ν κ) :=
  formationLiftKernel_klDiv_isometry μ ν κ R
    (measurableEmbedding_of_measurable_involution hRm hRinv)

end

end GaloisForLFunctions.HTGeometry
