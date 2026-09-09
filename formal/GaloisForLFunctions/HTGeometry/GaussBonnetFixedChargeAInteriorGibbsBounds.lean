import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsPath
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAIntervalGibbsRange

/-!
# Exact finite-state bounds for every interior Gibbs gap

The full physical phase interval maps into the energy interval from zero
to the actual intermediate barrier. The bounds hold at every coexistence
state, before taking any critical limit.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAInteriorReducedRadius (τ ψ : ℝ) : ℝ :=
  (1 + egbCoexistenceASymmetricRatio τ * sin ψ) / (1 + egbCoexistenceASymmetricRatio τ)

theorem egbFixedChargeAInteriorReducedRadius_bounds (τ ψ : ℝ) :
    thermalRatio τ ≤ egbFixedChargeAInteriorReducedRadius τ ψ ∧ egbFixedChargeAInteriorReducedRadius τ ψ ≤ 1 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hden : 0 < 1 + egbCoexistenceASymmetricRatio τ := by positivity
  have hs := egbFixedChargeAInteriorScale_mapsTo τ ⟨neg_one_le_sin ψ, sin_le_one ψ⟩
  unfold egbFixedChargeAInteriorReducedRadius
  constructor
  · apply (le_div_iff₀ hden).2
    rw [egbCoexistenceASymmetricRatio_cross]
    exact hs.1
  · apply (div_le_iff₀ hden).2
    simpa only [one_mul] using hs.2

theorem egbFixedChargeAInteriorReducedRadius_pos (τ ψ : ℝ) : 0 < egbFixedChargeAInteriorReducedRadius τ ψ :=
  lt_of_lt_of_le (thermalRatio_pos τ) (egbFixedChargeAInteriorReducedRadius_bounds τ ψ).1

theorem egbFixedChargeAInteriorRadius_reduced_formula (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ ψ =
      egbFixedChargeALargeRadius w φ τ * egbFixedChargeAInteriorReducedRadius τ ψ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_large_radius_mean]
  unfold egbFixedChargeAInteriorRadius egbFixedChargeAInteriorReducedRadius
  field_simp

theorem egbFixedChargeAInteriorReducedRadius_log_bounds (τ ψ : ℝ) :
    log (thermalRatio τ) ≤ log (egbFixedChargeAInteriorReducedRadius τ ψ) ∧
      log (egbFixedChargeAInteriorReducedRadius τ ψ) ≤ 0 := by
  have hb := egbFixedChargeAInteriorReducedRadius_bounds τ ψ
  constructor
  · exact log_le_log (thermalRatio_pos τ) hb.1
  · simpa only [log_one] using log_le_log (egbFixedChargeAInteriorReducedRadius_pos τ ψ) hb.2

theorem egbFixedChargeAInteriorGibbsGap_reduced_formula (w φ τ l ψ : ℝ) :
    egbFixedChargeAInteriorGibbsGap w φ τ l ψ = egbFixedChargeALargeRadius w φ τ *
      (egbCoexistenceAReducedLogGibbs τ (egbFixedChargeAAngle τ φ) (log (egbFixedChargeAInteriorReducedRadius τ ψ)) -
        egbCoexistenceAReducedLogGibbs τ (egbFixedChargeAAngle τ φ) 0) := by
  have h := egbCoexistenceA_gibbs_gap (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
    (log (egbFixedChargeAInteriorReducedRadius τ ψ))
  rw [egbFixedChargeA_gibbs_function, egbFixedChargeALogScale_exp,
    exp_log (egbFixedChargeAInteriorReducedRadius_pos τ ψ), ← egbFixedChargeAInteriorRadius_reduced_formula] at h
  exact h

theorem egbFixedChargeAGibbsBarrier_reduced_formula (w φ τ l : ℝ) :
    egbFixedChargeAGibbsBarrier w φ τ l = egbFixedChargeALargeRadius w φ τ *
      (egbCoexistenceAReducedLogGibbs τ (egbFixedChargeAAngle τ φ)
        (log (egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ))) -
        egbCoexistenceAReducedLogGibbs τ (egbFixedChargeAAngle τ φ) 0) := by
  have h := egbCoexistenceA_gibbs_gap (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
    (log (egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)))
  rw [egbFixedChargeA_gibbs_function, egbFixedChargeALogScale_exp,
    exp_log (egbCoexistenceAMiddleRadius_pos τ (egbFixedChargeAAngle τ φ))] at h
  exact h

theorem egbFixedChargeAInteriorGibbsGap_bounds (w φ τ l ψ : ℝ) :
    0 ≤ egbFixedChargeAInteriorGibbsGap w φ τ l ψ ∧
      egbFixedChargeAInteriorGibbsGap w φ τ l ψ ≤ egbFixedChargeAGibbsBarrier w φ τ l := by
  have hR := (egbFixedChargeALargeRadius_pos w φ τ).le
  have hb := egbCoexistenceAReducedLogGibbs_interval_mapsTo τ (egbFixedChargeAAngle τ φ)
    (egbFixedChargeAInteriorReducedRadius_log_bounds τ ψ)
  rw [egbFixedChargeAInteriorGibbsGap_reduced_formula, egbFixedChargeAGibbsBarrier_reduced_formula]
  exact ⟨mul_nonneg hR (sub_nonneg.mpr hb.1), mul_le_mul_of_nonneg_left (sub_le_sub hb.2 le_rfl) hR⟩

theorem egbFixedChargeAInteriorGibbsGap_ratio_bounds (w φ τ l ψ : ℝ) :
    0 ≤ egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbFixedChargeAGibbsBarrier w φ τ l ∧
      egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbFixedChargeAGibbsBarrier w φ τ l ≤ 1 := by
  have hb := egbFixedChargeAInteriorGibbsGap_bounds w φ τ l ψ
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  constructor
  · exact div_nonneg hb.1 hB.le
  · apply (div_le_iff₀ hB).2
    simpa only [one_mul] using hb.2

end GaloisForLFunctions.HTGeometry
