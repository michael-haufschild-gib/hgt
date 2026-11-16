import GaloisForLFunctions.HTGeometry.CharFunWienerLemma
import GaloisForLFunctions.RHTower.ObserverTemporalDimensionLaw

/-!
# Directional Fourier averages and spectral hyperplanes

Restricting a Fourier transform to a line projects its spectral measure onto
that direction. Wiener's lemma consequently detects mass on perpendicular
hyperplanes, including the exact obstruction to mean-square decay.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Fourier response along a continuous linear frequency coordinate. -/
def directionalSpectralResponse (μ : Measure E) (L : E →L[ℝ] ℝ) (t : ℝ) : ℂ :=
  charFun (μ.map L) t

/-- The directional response is the original spectral integral restricted to a line. -/
theorem directionalSpectralResponse_eq_integral (μ : Measure E) [IsFiniteMeasure μ]
    (L : E →L[ℝ] ℝ) (t : ℝ) :
    directionalSpectralResponse μ L t =
      ∫ x, Complex.exp ((t : ℂ) * L x * Complex.I) ∂μ := by
  rw [directionalSpectralResponse, charFun_apply_real,
    integral_map L.continuous.measurable.aemeasurable
      (by fun_prop : Continuous fun s : ℝ => Complex.exp ((t : ℂ) * s * Complex.I)).aestronglyMeasurable]

/-- A frequency-selective directional average reads one spectral hyperplane exactly. -/
theorem directionalSpectralResponse_frequency_mean (μ : Measure E) [IsFiniteMeasure μ]
    (L : E →L[ℝ] ℝ) (a : ℝ) :
    Tendsto (fun Y : ℝ => (1 / Y : ℂ) * ∫ t in (0 : ℝ)..Y,
      directionalSpectralResponse μ L t * Complex.exp (-(t * a * Complex.I)))
      atTop (𝓝 (μ.real {x | L x = a} : ℂ)) := by
  have h := HTGeometry.tendsto_oneSided_mean_charFun_mul (μ.map L) a
  have hm : (μ.map L).real {a} = μ.real {x | L x = a} := by
    rw [measureReal_def, measureReal_def,
      Measure.map_apply L.continuous.measurable (measurableSet_singleton a)]
    rfl
  simpa only [directionalSpectralResponse, hm] using h

/-- Spectral pairs with the same directional frequency are the surviving mean-square mass. -/
theorem directionalSpectralResponse_mean_square (μ : Measure E) [IsFiniteMeasure μ]
    (L : E →L[ℝ] ℝ) :
    Tendsto (fun Y : ℝ => (1 / (2 * Y)) * ∫ t in (-Y)..Y,
      ‖directionalSpectralResponse μ L t‖ ^ 2) atTop
      (𝓝 ((μ.prod μ).real {p : E × E | L p.1 = L p.2})) := by
  have h := HTGeometry.tendsto_mean_normSq_charFun (μ.map L)
  have hm : ((μ.map L).prod (μ.map L)).real {p : ℝ × ℝ | p.1 = p.2} =
      (μ.prod μ).real {p : E × E | L p.1 = L p.2} := by
    have hdiag : {p : ℝ × ℝ | p.1 = p.2} = diagonal ℝ := by
      ext p
      simp only [mem_setOf_eq, mem_diagonal_iff]
    rw [hdiag]
    rw [Measure.map_prod_map μ μ L.continuous.measurable L.continuous.measurable,
      measureReal_def, measureReal_def,
      Measure.map_apply (L.continuous.measurable.prodMap L.continuous.measurable)
        measurableSet_diagonal]
    congr 2
  simpa only [directionalSpectralResponse, hm] using h

/-- Directional mean-square decay is equivalent to zero mass on every perpendicular hyperplane. -/
theorem directionalSpectralResponse_mean_square_zero_iff
    (μ : Measure E) [IsFiniteMeasure μ] (L : E →L[ℝ] ℝ) :
    Tendsto (fun Y : ℝ => (1 / (2 * Y)) * ∫ t in (-Y)..Y,
      ‖directionalSpectralResponse μ L t‖ ^ 2) atTop (𝓝 0) ↔
      ∀ a : ℝ, μ {x | L x = a} = 0 := by
  have hlim := HTGeometry.tendsto_mean_normSq_charFun (μ.map L)
  have hzero : (((μ.map L).prod (μ.map L)).real {p : ℝ × ℝ | p.1 = p.2} = 0) ↔
      ∀ a : ℝ, μ {x | L x = a} = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    simp only [measure_ne_top, or_false]
    have hdiag : {p : ℝ × ℝ | p.1 = p.2} = diagonal ℝ := by
      ext p
      simp only [mem_setOf_eq, mem_diagonal_iff]
    rw [hdiag]
    rw [← RHTower.spectralDifferenceMeasure_singleton_zero (μ.map L),
      RHTower.spectralDifferenceMeasure_singleton_zero_iff_noAtoms]
    constructor
    · intro h a
      letI := h
      have ha := measure_singleton (μ := μ.map L) a
      rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton a)] at ha
      exact ha
    · intro h
      constructor
      intro a
      rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton a)]
      exact h a
  constructor
  · intro h
    exact hzero.mp (tendsto_nhds_unique hlim h)
  · intro h
    simpa only [directionalSpectralResponse, hzero.mpr h] using hlim

end GaloisForLFunctions.BiarithmeticGeometry

