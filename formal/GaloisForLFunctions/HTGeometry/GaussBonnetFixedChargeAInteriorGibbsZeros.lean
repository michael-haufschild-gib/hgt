import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsBounds

/-!
# Exact zeros of the physical interior Gibbs gap

The finite-state energy gap vanishes precisely at the two phase
endpoints. This agrees exactly with the zero set of the limiting quartic
profile, with no hidden interior zeros.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInteriorRadius_small_iff (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ ψ = egbFixedChargeASmallRadius w φ τ ↔ sin ψ = -1 := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_small_radius_mean]
  unfold egbFixedChargeAInteriorRadius
  constructor
  · intro h
    have he : 1 + egbCoexistenceASymmetricRatio τ * sin ψ = 1 - egbCoexistenceASymmetricRatio τ := by
      apply mul_left_cancel₀ hm.ne'
      nlinarith only [h]
    apply mul_left_cancel₀ hd.ne'
    linarith only [he]
  · intro h
    rw [h]
    ring

theorem egbFixedChargeAInteriorRadius_large_iff (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ ψ = egbFixedChargeALargeRadius w φ τ ↔ sin ψ = 1 := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeA_large_radius_mean]
  unfold egbFixedChargeAInteriorRadius
  constructor
  · intro h
    have he : 1 + egbCoexistenceASymmetricRatio τ * sin ψ = 1 + egbCoexistenceASymmetricRatio τ := by
      apply mul_left_cancel₀ hm.ne'
      nlinarith only [h]
    apply mul_left_cancel₀ hd.ne'
    linarith only [he]
  · intro h
    rw [h]
    ring

theorem egbFixedChargeAInteriorGibbsGap_zero_iff (w φ τ l ψ : ℝ) :
    egbFixedChargeAInteriorGibbsGap w φ τ l ψ = 0 ↔ cos ψ = 0 := by
  have h := egbFixedChargeA_global_minimizers_iff w φ τ l (log (egbFixedChargeAInteriorRadius w φ τ ψ))
  rw [exp_log (egbFixedChargeAInteriorRadius_pos w φ τ ψ),
    egbFixedChargeAInteriorRadius_small_iff, egbFixedChargeAInteriorRadius_large_iff] at h
  unfold egbFixedChargeAInteriorGibbsGap
  rw [sub_eq_zero, h]
  have hs := sin_sq_add_cos_sq ψ
  constructor
  · rintro (he | he) <;> rw [he] at hs <;> nlinarith [sq_nonneg (cos ψ)]
  · intro he
    rw [he] at hs
    have hfactor : (sin ψ - 1) * (sin ψ + 1) = 0 := by nlinarith only [hs]
    rcases mul_eq_zero.mp hfactor with h1 | h2
    · right; linarith only [h1]
    · left; linarith only [h2]

theorem egbFixedChargeAInteriorGibbsGap_pos_iff (w φ τ l ψ : ℝ) :
    0 < egbFixedChargeAInteriorGibbsGap w φ τ l ψ ↔ cos ψ ≠ 0 := by
  have hb := (egbFixedChargeAInteriorGibbsGap_bounds w φ τ l ψ).1
  have he := egbFixedChargeAInteriorGibbsGap_zero_iff w φ τ l ψ
  constructor
  · intro hp hc
    have hz := he.mpr hc
    linarith
  · intro hc
    by_contra hn
    have hz : egbFixedChargeAInteriorGibbsGap w φ τ l ψ = 0 := le_antisymm (le_of_not_gt hn) hb
    exact hc (he.mp hz)

end GaloisForLFunctions.HTGeometry
