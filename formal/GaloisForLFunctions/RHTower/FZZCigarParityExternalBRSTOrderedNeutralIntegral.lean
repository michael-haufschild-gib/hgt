import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTOrderedNeutralKernel

/-!
# FZZ external-BRST cyclic ordered neutral integral

The same-angle neutral external pair is compactly trivial. Keeping literal
cyclic order of two distinct marked branch positions instead gives an exact
inverse-frequency compact coefficient. This leaf isolates that integral from
the separate non-reality argument.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Cyclically ordered compact integral of two distinct literal neutral
external-BRST branch factors. -/
def fzzCigarExternalBRSTOrderedNeutralAngularIntegral
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t,
    fzzCigarExternalBRSTOrderedNeutralAngularKernel k j p ν s t

/-- The full cyclically ordered neutral branch coefficient is the inverse
nonzero angular frequency. -/
theorem fzzCigarExternalBRSTOrderedNeutralAngularIntegral_eq_inv_frequency
    (k : ℝ) (j : ℂ) (p ν : ℤ) (hp : p ≠ 0) :
    fzzCigarExternalBRSTOrderedNeutralAngularIntegral k j p ν =
      (fzzCigarExternalBRSTAngularFrequency p)⁻¹ := by
  let c : ℂ := fzzCigarExternalBRSTAngularFrequency p
  unfold fzzCigarExternalBRSTOrderedNeutralAngularIntegral
  change (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t,
    fzzCigarExternalBRSTOrderedNeutralAngularKernel k j p ν s t) = c⁻¹
  calc
    _ = ∫ t in (0 : ℝ)..1,
        ((RHTower.fzzTorusHolonomyCharacter p t - 1) / c) *
          RHTower.fzzTorusHolonomyCharacter (-p) t := by
            apply intervalIntegral.integral_congr
            intro t _
            simpa only [c] using
              intervalIntegral_fzzCigarExternalBRSTOrderedNeutralAngularKernel_inner
                k j p ν t hp
    _ = ∫ t in (0 : ℝ)..1, c⁻¹ *
          (1 - RHTower.fzzTorusHolonomyCharacter (-p) t) := by
            apply intervalIntegral.integral_congr
            intro t _
            dsimp only
            have hneutral : RHTower.fzzTorusHolonomyCharacter p t *
                RHTower.fzzTorusHolonomyCharacter (-p) t = 1 := by
              rw [RHTower.fzzTorusHolonomyCharacter_mul]
              simp
            rw [div_eq_mul_inv]
            calc
              (RHTower.fzzTorusHolonomyCharacter p t - 1) * c⁻¹ *
                  RHTower.fzzTorusHolonomyCharacter (-p) t =
                  c⁻¹ * (RHTower.fzzTorusHolonomyCharacter p t *
                    RHTower.fzzTorusHolonomyCharacter (-p) t -
                      RHTower.fzzTorusHolonomyCharacter (-p) t) := by ring
              _ = c⁻¹ * (1 - RHTower.fzzTorusHolonomyCharacter (-p) t) := by
                rw [hneutral]
    _ = c⁻¹ * ∫ t in (0 : ℝ)..1,
          (1 - RHTower.fzzTorusHolonomyCharacter (-p) t) := by
            rw [intervalIntegral.integral_const_mul]
    _ = c⁻¹ := by
            have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume 0 1 :=
              continuous_const.intervalIntegrable 0 1
            have hchar : IntervalIntegrable
                (RHTower.fzzTorusHolonomyCharacter (-p)) volume 0 1 :=
              RHTower.continuous_fzzTorusHolonomyCharacter (-p) |>.intervalIntegrable 0 1
            have hzero : (∫ t in (0 : ℝ)..1,
                RHTower.fzzTorusHolonomyCharacter (-p) t) = 0 := by
              rw [RHTower.intervalIntegral_fzzTorusHolonomyCharacter]
              simp [neg_ne_zero.mpr hp]
            rw [intervalIntegral.integral_sub hconst hchar, hzero]
            norm_num

end

end GaloisForLFunctions.RHTower
