import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTOrderedNeutralIntegral

/-!
# FZZ external-BRST reverse cyclic neutral integral

The reverse cyclic chamber of the literal neutral branch pair has the
negative inverse-frequency coefficient. This isolates the second chamber
before testing unordered symmetrization.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Reverse cyclic chamber for the same literal ordered neutral branch kernel. -/
def fzzCigarExternalBRSTReverseNeutralAngularIntegral
    (k : ℝ) (j : ℂ) (p ν : ℤ) : ℂ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..s,
    fzzCigarExternalBRSTOrderedNeutralAngularKernel k j p ν s t

/-- Reversing compact charge negates its angular frequency. -/
theorem fzzCigarExternalBRSTAngularFrequency_neg (p : ℤ) :
    fzzCigarExternalBRSTAngularFrequency (-p) =
      -fzzCigarExternalBRSTAngularFrequency p := by
  unfold fzzCigarExternalBRSTAngularFrequency
  push_cast
  ring

/-- The reverse cyclic chamber carries the negative inverse-frequency
current. -/
theorem fzzCigarExternalBRSTReverseNeutralAngularIntegral_eq_neg_inv_frequency
    (k : ℝ) (j : ℂ) (p ν : ℤ) (hp : p ≠ 0) :
    fzzCigarExternalBRSTReverseNeutralAngularIntegral k j p ν =
      -(fzzCigarExternalBRSTAngularFrequency p)⁻¹ := by
  let c : ℂ := fzzCigarExternalBRSTAngularFrequency p
  unfold fzzCigarExternalBRSTReverseNeutralAngularIntegral
  change (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..s,
    fzzCigarExternalBRSTOrderedNeutralAngularKernel k j p ν s t) = -c⁻¹
  calc
    _ = ∫ s in (0 : ℝ)..1,
        RHTower.fzzTorusHolonomyCharacter p s *
          ((RHTower.fzzTorusHolonomyCharacter (-p) s - 1) /
            fzzCigarExternalBRSTAngularFrequency (-p)) := by
            apply intervalIntegral.integral_congr
            intro s _
            change (∫ t in (0 : ℝ)..s,
              RHTower.fzzTorusHolonomyCharacter p s *
                RHTower.fzzTorusHolonomyCharacter (-p) t) = _
            rw [intervalIntegral.integral_const_mul,
              intervalIntegral_fzzCigarExternalBRSTAngularBranch_to (-p) s
                (neg_ne_zero.mpr hp)]
    _ = ∫ s in (0 : ℝ)..1, c⁻¹ *
          (RHTower.fzzTorusHolonomyCharacter p s - 1) := by
            apply intervalIntegral.integral_congr
            intro s _
            have hfreq : fzzCigarExternalBRSTAngularFrequency (-p) = -c := by
              dsimp only [c]
              exact fzzCigarExternalBRSTAngularFrequency_neg p
            have hneutral : RHTower.fzzTorusHolonomyCharacter p s *
                RHTower.fzzTorusHolonomyCharacter (-p) s = 1 := by
              rw [RHTower.fzzTorusHolonomyCharacter_mul]
              simp
            rw [hfreq]
            calc
              RHTower.fzzTorusHolonomyCharacter p s *
                  ((RHTower.fzzTorusHolonomyCharacter (-p) s - 1) / -c) =
                  -(RHTower.fzzTorusHolonomyCharacter p s *
                    RHTower.fzzTorusHolonomyCharacter (-p) s * c⁻¹) +
                      RHTower.fzzTorusHolonomyCharacter p s * c⁻¹ := by
                        rw [div_eq_mul_inv]
                        ring
              _ = c⁻¹ * (RHTower.fzzTorusHolonomyCharacter p s - 1) := by
                    rw [hneutral]
                    ring
    _ = c⁻¹ * ∫ s in (0 : ℝ)..1,
          (RHTower.fzzTorusHolonomyCharacter p s - 1) := by
            rw [intervalIntegral.integral_const_mul]
    _ = -c⁻¹ := by
            have hchar : IntervalIntegrable
                (RHTower.fzzTorusHolonomyCharacter p) volume 0 1 :=
              RHTower.continuous_fzzTorusHolonomyCharacter p |>.intervalIntegrable 0 1
            have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume 0 1 :=
              continuous_const.intervalIntegrable 0 1
            have hzero : (∫ s in (0 : ℝ)..1,
                RHTower.fzzTorusHolonomyCharacter p s) = 0 := by
              rw [RHTower.intervalIntegral_fzzTorusHolonomyCharacter]
              simp [hp]
            rw [intervalIntegral.integral_sub hchar hconst, hzero]
            norm_num

end

end GaloisForLFunctions.RHTower
