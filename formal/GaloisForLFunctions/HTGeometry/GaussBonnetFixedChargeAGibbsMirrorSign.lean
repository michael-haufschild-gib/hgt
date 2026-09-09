import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsMirrorAsymmetry

/-!
# Strict near-critical asymmetry at actual mirrored radii

A real parameter supplies a strictly positive interior coordinate through
the corpus thermal ratio. The larger mirrored radius has strictly lower
Gibbs energy near criticality. This sign is obtained from the actual
fifth-order energy limit, with no sign or smallness hypotheses supplied
by the caller.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAMirrorAngle (σ : ℝ) : ℝ := arcsin (thermalRatio σ)
def egbFixedChargeAGibbsMirrorCoefficient (w φ σ : ℝ) : ℝ :=
  2 * egbFixedChargeAGibbsOddCoefficient w φ * thermalRatio σ * (1 - thermalRatio σ ^ 2) ^ 2

theorem egbFixedChargeAMirrorAngle_sin (σ : ℝ) : sin (egbFixedChargeAMirrorAngle σ) = thermalRatio σ := by
  unfold egbFixedChargeAMirrorAngle
  exact sin_arcsin (by linarith [thermalRatio_pos σ]) (thermalRatio_lt_one σ).le

theorem egbFixedChargeAMirrorAngle_cos_fourth (σ : ℝ) :
    cos (egbFixedChargeAMirrorAngle σ) ^ 4 = (1 - thermalRatio σ ^ 2) ^ 2 := by
  have h := sin_sq_add_cos_sq (egbFixedChargeAMirrorAngle σ)
  rw [egbFixedChargeAMirrorAngle_sin] at h
  have he : cos (egbFixedChargeAMirrorAngle σ) ^ 2 = 1 - thermalRatio σ ^ 2 := by linarith
  calc
    _ = (cos (egbFixedChargeAMirrorAngle σ) ^ 2) ^ 2 := by ring
    _ = _ := by rw [he]

theorem egbFixedChargeAGibbsMirrorCoefficient_neg (w φ σ : ℝ) :
    egbFixedChargeAGibbsMirrorCoefficient w φ σ < 0 := by
  have hz := thermalRatio_pos σ
  have hz1 := thermalRatio_lt_one σ
  have ht : 0 < 1 - thermalRatio σ ^ 2 := by
    nlinarith [mul_pos (by linarith : 0 < 1 - thermalRatio σ) (by linarith : 0 < 1 + thermalRatio σ)]
  have hc := egbFixedChargeAGibbsOddCoefficient_neg w φ
  unfold egbFixedChargeAGibbsMirrorCoefficient
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hz) (by positivity)

theorem egbFixedChargeAGibbsMirrorDifference_positive_coordinate_limit (w φ l σ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsMirrorDifference w φ τ l (egbFixedChargeAMirrorAngle σ) /
      egbCoexistenceASymmetricRatio τ ^ 5) atBot (𝓝 (egbFixedChargeAGibbsMirrorCoefficient w φ σ)) := by
  simpa only [egbFixedChargeAMirrorAngle_sin, egbFixedChargeAMirrorAngle_cos_fourth,
    egbFixedChargeAGibbsMirrorCoefficient] using
    egbFixedChargeAGibbsMirrorDifference_fifth_order_limit w φ l (egbFixedChargeAMirrorAngle σ)

theorem egbFixedChargeAGibbsMirrorDifference_eventually_neg (w φ l σ : ℝ) :
    ∀ᶠ τ in atBot, egbFixedChargeAGibbsMirrorDifference w φ τ l (egbFixedChargeAMirrorAngle σ) < 0 := by
  have h := (egbFixedChargeAGibbsMirrorDifference_positive_coordinate_limit w φ l σ).eventually_lt_const
    (egbFixedChargeAGibbsMirrorCoefficient_neg w φ σ)
  filter_upwards [h] with τ hτ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hd5 : 0 < egbCoexistenceASymmetricRatio τ ^ 5 := by positivity
  have he := (div_lt_iff₀ hd5).mp hτ
  linarith

theorem egbFixedChargeAGibbsMirror_energy_eventually_ordered (w φ l σ : ℝ) :
    ∀ᶠ τ in atBot,
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorRadius w φ τ (egbFixedChargeAMirrorAngle σ)) <
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
        (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorRadius w φ τ (-egbFixedChargeAMirrorAngle σ)) := by
  filter_upwards [egbFixedChargeAGibbsMirrorDifference_eventually_neg w φ l σ] with τ hτ
  unfold egbFixedChargeAGibbsMirrorDifference at hτ
  linarith

theorem egbFixedChargeAGibbsMirror_radius_straddles_mean (w φ τ σ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ (-egbFixedChargeAMirrorAngle σ) < egbFixedChargeAMeanRadius w φ τ ∧
    egbFixedChargeAMeanRadius w φ τ < egbFixedChargeAInteriorRadius w φ τ (egbFixedChargeAMirrorAngle σ) := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hz := thermalRatio_pos σ
  have hp : 0 < egbFixedChargeAMeanRadius w φ τ * (egbCoexistenceASymmetricRatio τ * thermalRatio σ) := by positivity
  unfold egbFixedChargeAInteriorRadius
  rw [sin_neg, egbFixedChargeAMirrorAngle_sin]
  constructor <;> nlinarith [hp]

end GaloisForLFunctions.HTGeometry
