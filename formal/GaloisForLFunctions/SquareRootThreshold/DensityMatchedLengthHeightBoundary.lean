import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates
import GaloisForLFunctions.SquareRootThreshold.PositionAndDepthShareOneNyquistAperture

/-!+# The length-height boundary of the density-matched paired lattice

The paired lattice has density `L/π`. Matching the leading density `log T/(2π)` sets
`L = log T/2`. Its sharp indistinguishability aperture `L/2` therefore corresponds to
prime cutoff `X = exp(2a)` with `X² = T`. This calibration distinguishes the paired-lattice
boundary from the atomic touching boundary `X/T = 1`.

These are exact statements about the lattice configurations, not estimates for zeta zeros.
-/

noncomputable section

open Set MeasureTheory
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open SpacingScaleHarmonicAnalysis.LengthHeight Zeta23

/-- Period parameter giving the paired lattice density `log T/(2π)`. -/
def densityMatchedPeriod (T : ℝ) : ℝ := Real.log T / 2

theorem densityMatchedPeriod_pos {T : ℝ} (hT : 1 < T) : 0 < densityMatchedPeriod T :=
  half_pos (Real.log_pos hT)

theorem densityMatchedPeriod_density (T : ℝ) :
    densityMatchedPeriod T / Real.pi = Real.log T / (2 * Real.pi) := by
  dsimp [densityMatchedPeriod]
  ring

/-- The Nyquist aperture has the square-root prime cutoff at matched density. -/
theorem aperture_le_densityMatchedPeriod_half_iff {X T : ℝ} (hX : 0 < X) (hT : 0 < T) :
    aperture X ≤ densityMatchedPeriod T / 2 ↔ X ^ 2 ≤ T := by
  rw [← Real.log_le_log_iff (sq_pos_of_pos hX) hT, Real.log_pow]
  dsimp [aperture, densityMatchedPeriod]
  constructor <;> intro h <;> linarith only [h]

/-- Position and depth mimics agree exactly up to `X² ≤ T`, with multiplicities retained. -/
theorem densityMatched_lattices_agree_iff {X T δ : ℝ} (hX : 0 < X) (hT : 1 < T)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ((∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-aperture X) (aperture X) →
      (onLineLatticeConfig (densityMatchedPeriod_pos hT)).W f f =
        (simpleHalfLatticeConfig (densityMatchedPeriod_pos hT)).W f f) ↔ X ^ 2 ≤ T) ∧
    ((∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-aperture X) (aperture X) →
      (offLineLatticeConfig (densityMatchedPeriod_pos hT) hδ hδ').W f f =
        (onLineLatticeConfig (densityMatchedPeriod_pos hT)).W f f) ↔ X ^ 2 ≤ T) := by
  have hscale := aperture_le_densityMatchedPeriod_half_iff hX (zero_lt_one.trans hT)
  exact ⟨(onLineLattices_agree_iff_le_nyquist (densityMatchedPeriod_pos hT) _).trans hscale,
    (offLineLattice_agrees_iff_le_nyquist (densityMatchedPeriod_pos hT) hδ hδ' _).trans hscale⟩

/-- Beyond the square-root cutoff the matched off-line pair has a negative witness. -/
theorem densityMatched_negative_test_iff {X T δ : ℝ} (hX : 0 < X) (hT : 1 < T)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-aperture X) (aperture X) ∧
      ((offLineLatticeConfig (densityMatchedPeriod_pos hT) hδ hδ').W f f).re < 0) ↔
        T < X ^ 2 := by
  constructor
  · rintro ⟨f, hf, hfs, hneg⟩
    by_contra h
    have heq := ((densityMatched_lattices_agree_iff hX hT hδ hδ').2.mpr (not_lt.mp h)) f hf hfs
    rw [heq] at hneg
    exact (not_lt_of_ge (re_W_onLineLatticeConfig_nonneg (densityMatchedPeriod_pos hT) f)) hneg
  · intro h
    have ha : densityMatchedPeriod T / 2 < aperture X := by
      by_contra hle
      exact (not_le_of_gt h)
        ((aperture_le_densityMatchedPeriod_half_iff hX (zero_lt_one.trans hT)).mp (not_lt.mp hle))
    exact exists_re_W_offLineLatticeConfig_neg (densityMatchedPeriod_pos hT) hδ hδ' ha

/-- At atomic touching the matched paired-lattice obstruction is already past its boundary. -/
theorem densityMatched_negative_at_atomic_touching {T δ : ℝ} (hT : 1 < T)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    overlap T T = 1 ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧
      tsupport f ⊆ Icc (-aperture T) (aperture T) ∧
      ((offLineLatticeConfig (densityMatchedPeriod_pos hT) hδ hδ').W f f).re < 0 := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  refine ⟨div_self hT0.ne', (densityMatched_negative_test_iff hT0 hT hδ hδ').mpr ?_⟩
  nlinarith only [mul_lt_mul_of_pos_left hT hT0]

end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.densityMatched_lattices_agree_iff
#print axioms GaloisForLFunctions.SquareRootThreshold.densityMatched_negative_test_iff
#print axioms GaloisForLFunctions.SquareRootThreshold.densityMatched_negative_at_atomic_touching
