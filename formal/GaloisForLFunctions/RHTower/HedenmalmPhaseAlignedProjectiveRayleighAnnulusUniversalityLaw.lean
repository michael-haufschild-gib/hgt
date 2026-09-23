import GaloisForLFunctions.RHTower.HedenmalmProjectiveRayleighGapUniversalityLaw

/-!
# Hedenmalm phase-aligned projective Rayleigh annulus

Projective phase alignment turns the concrete Hedenmalm source–tangent energy estimate into an
actual metric bound modulo unit phase. Source–tangent independence makes that distance strictly
positive, while Rayleigh coercivity supplies its explicit upper radius.
-/

open Complex MeasureTheory
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- **Hedenmalm phase-aligned projective Rayleigh-annulus law.** Under the concrete spectral-gap
hypotheses, some unit phase aligns tangent and source at a strictly positive squared distance
bounded by twice the normalized Rayleigh excess. -/
theorem thetaCuspRightLine_phaseAlignedProjectiveRayleighAnnulusUniversality
    (a : ℝ) (ha : |a| < 1)
    (T : Lp (α := ℝ) ℂ 2 volume →L[ℂ] Lp (α := ℝ) ℂ 2 volume)
    (hT : T.toLinearMap.IsSymmetric)
    {epsilon gap : ℝ}
    (hTv : T (thetaCuspRightLineUnitSource a ha) =
      (epsilon : ℂ) • thetaCuspRightLineUnitSource a ha)
    (hgap : 0 < gap)
    (hcoercive : gap * ‖thetaCuspRightLineUnitTangent a ha -
        inner ℂ (thetaCuspRightLineUnitSource a ha)
          (thetaCuspRightLineUnitTangent a ha) •
            thetaCuspRightLineUnitSource a ha‖ ^ (2 : ℕ) ≤
      (T - (epsilon : ℂ) • ContinuousLinearMap.id ℂ
        (Lp (α := ℝ) ℂ 2 volume)).reApplyInnerSelf
        (thetaCuspRightLineUnitTangent a ha -
          inner ℂ (thetaCuspRightLineUnitSource a ha)
            (thetaCuspRightLineUnitTangent a ha) •
              thetaCuspRightLineUnitSource a ha)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      0 < ‖thetaCuspRightLineUnitTangent a ha -
        c • thetaCuspRightLineUnitSource a ha‖ ^ (2 : ℕ) ∧
      ‖thetaCuspRightLineUnitTangent a ha -
          c • thetaCuspRightLineUnitSource a ha‖ ^ (2 : ℕ) ≤
        2 * ((T.rayleighQuotient (thetaCuspRightLineUnitTangent a ha) -
          epsilon) / gap) ∧
      epsilon < T.rayleighQuotient
        (thetaCuspRightLineUnitTangent a ha) := by
  have hrayleigh :=
    thetaCuspRightLine_projectiveRayleighGap_strict
      a ha T hT hTv hgap hcoercive
  obtain ⟨c, hc, hdistance⟩ :=
    exists_unitScalar_norm_sub_sq_le_two_projectiveQuantumTangentEnergy
      (𝕜 := ℂ)
      (v := thetaCuspRightLineUnitSource a ha)
      (g := thetaCuspRightLineUnitTangent a ha)
      (norm_thetaCuspRightLineUnitSource a ha)
      (norm_thetaCuspRightLineUnitTangent a ha)
  have hlinear :=
    thetaCuspRightLine_unit_source_tangent_linearIndependent a ha
  have hne :
      thetaCuspRightLineUnitTangent a ha -
          c • thetaCuspRightLineUnitSource a ha ≠ 0 := by
    intro hzero
    have heq :
        thetaCuspRightLineUnitTangent a ha =
          c • thetaCuspRightLineUnitSource a ha :=
      sub_eq_zero.mp hzero
    have hrelation :
        (-c) • thetaCuspRightLineUnitSource a ha +
          (1 : ℂ) • thetaCuspRightLineUnitTangent a ha = 0 := by
      rw [heq]
      module
    have hcoeff :=
      (LinearIndependent.pair_iff.mp hlinear) (-c) 1 hrelation
    exact one_ne_zero hcoeff.2
  have hpositive :
      0 < ‖thetaCuspRightLineUnitTangent a ha -
        c • thetaCuspRightLineUnitSource a ha‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hupper :
      ‖thetaCuspRightLineUnitTangent a ha -
          c • thetaCuspRightLineUnitSource a ha‖ ^ (2 : ℕ) ≤
        2 * ((T.rayleighQuotient (thetaCuspRightLineUnitTangent a ha) -
          epsilon) / gap) :=
    hdistance.trans (mul_le_mul_of_nonneg_left hrayleigh.2.1 (by norm_num))
  exact ⟨c, hc, hpositive, hupper, hrayleigh.2.2⟩

end

end RHTower
