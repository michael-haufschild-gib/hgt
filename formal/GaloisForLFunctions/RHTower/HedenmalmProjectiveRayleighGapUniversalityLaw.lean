import GaloisForLFunctions.RHTower.HedenmalmRankTwoTangentInertia
import GaloisForLFunctions.RHTower.RayleighProjectiveQuantumFisher

/-!
# Hedenmalm projective Rayleigh-gap universality law

The actual exponentially tilted theta source and its aperture tangent form an independent pair in
complex `L²(ℝ)`.  Normalizing this pair turns that source theorem into a strict spectral law: every
symmetric continuous operator for which the source is an eigenvector and the tangent complement is
coercive has tangent Rayleigh quotient strictly above the source eigenvalue.  The excess controls
the concrete projective Gram/Fisher energy quantitatively.
-/

open Complex MeasureTheory
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Unit normalization of the Hedenmalm right-line theta source. -/
def thetaCuspRightLineUnitSource (a : ℝ) (ha : |a| < 1) :
    Lp (α := ℝ) ℂ 2 volume :=
  ((‖thetaCuspRightLineSourceL2 a ha‖⁻¹ : ℝ) : ℂ) •
    thetaCuspRightLineSourceL2 a ha

/-- Unit normalization of the Hedenmalm aperture tangent. -/
def thetaCuspRightLineUnitTangent (a : ℝ) (ha : |a| < 1) :
    Lp (α := ℝ) ℂ 2 volume :=
  ((‖thetaCuspRightLineTangentL2 a ha‖⁻¹ : ℝ) : ℂ) •
    thetaCuspRightLineTangentL2 a ha

theorem norm_thetaCuspRightLineUnitSource (a : ℝ) (ha : |a| < 1) :
    ‖thetaCuspRightLineUnitSource a ha‖ = 1 := by
  have hu0 : thetaCuspRightLineSourceL2 a ha ≠ 0 :=
    (thetaCuspRightLine_source_tangent_linearIndependent a ha).ne_zero 0
  simp [thetaCuspRightLineUnitSource, norm_smul, hu0]

theorem norm_thetaCuspRightLineUnitTangent (a : ℝ) (ha : |a| < 1) :
    ‖thetaCuspRightLineUnitTangent a ha‖ = 1 := by
  have hw0 : thetaCuspRightLineTangentL2 a ha ≠ 0 :=
    (thetaCuspRightLine_source_tangent_linearIndependent a ha).ne_zero 1
  simp [thetaCuspRightLineUnitTangent, norm_smul, hw0]

/-- Normalization preserves independence of the concrete source and tangent. -/
theorem thetaCuspRightLine_unit_source_tangent_linearIndependent
    (a : ℝ) (ha : |a| < 1) :
    LinearIndependent ℂ
      ![thetaCuspRightLineUnitSource a ha,
        thetaCuspRightLineUnitTangent a ha] := by
  rw [LinearIndependent.pair_iff]
  intro s t hrel
  have hu0 : thetaCuspRightLineSourceL2 a ha ≠ 0 :=
    (thetaCuspRightLine_source_tangent_linearIndependent a ha).ne_zero 0
  have hw0 : thetaCuspRightLineTangentL2 a ha ≠ 0 :=
    (thetaCuspRightLine_source_tangent_linearIndependent a ha).ne_zero 1
  have hscaleU : (((‖thetaCuspRightLineSourceL2 a ha‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hu0)
  have hscaleW : (((‖thetaCuspRightLineTangentL2 a ha‖⁻¹ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hw0)
  have hscaled :
      (s * ((‖thetaCuspRightLineSourceL2 a ha‖⁻¹ : ℝ) : ℂ)) •
          thetaCuspRightLineSourceL2 a ha +
        (t * ((‖thetaCuspRightLineTangentL2 a ha‖⁻¹ : ℝ) : ℂ)) •
          thetaCuspRightLineTangentL2 a ha = 0 := by
    simpa [thetaCuspRightLineUnitSource, thetaCuspRightLineUnitTangent,
      smul_smul] using hrel
  have hcoeff := (LinearIndependent.pair_iff.mp
    (thetaCuspRightLine_source_tangent_linearIndependent a ha)) _ _ hscaled
  exact ⟨(mul_eq_zero.mp hcoeff.1).resolve_right hscaleU,
    (mul_eq_zero.mp hcoeff.2).resolve_right hscaleW⟩

/-- **Hedenmalm projective Rayleigh-gap universality law.**  Concrete source-tangent
independence makes the projective Fisher energy positive.  Positive gap coercivity therefore
forces strict spectral separation of the tangent from the source eigenvalue. -/
theorem thetaCuspRightLine_projectiveRayleighGap_strict
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
            thetaCuspRightLineUnitSource a ha‖ ^ 2 ≤
      (T - (epsilon : ℂ) • ContinuousLinearMap.id ℂ
        (Lp (α := ℝ) ℂ 2 volume)).reApplyInnerSelf
        (thetaCuspRightLineUnitTangent a ha -
          inner ℂ (thetaCuspRightLineUnitSource a ha)
            (thetaCuspRightLineUnitTangent a ha) •
              thetaCuspRightLineUnitSource a ha)) :
    0 < HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
        (thetaCuspRightLineUnitSource a ha)
        (thetaCuspRightLineUnitTangent a ha) ∧
      HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
          (thetaCuspRightLineUnitSource a ha)
          (thetaCuspRightLineUnitTangent a ha) ≤
        (T.rayleighQuotient (thetaCuspRightLineUnitTangent a ha) - epsilon) / gap ∧
      epsilon < T.rayleighQuotient (thetaCuspRightLineUnitTangent a ha) := by
  have hv := norm_thetaCuspRightLineUnitSource a ha
  have hg := norm_thetaCuspRightLineUnitTangent a ha
  have hpos : 0 < HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (thetaCuspRightLineUnitSource a ha)
      (thetaCuspRightLineUnitTangent a ha) :=
    (HTGeometry.projectiveGramTangentEnergy_pos_iff_linearIndependent_pair _ _).2
      (thetaCuspRightLine_unit_source_tangent_linearIndependent a ha)
  have hle := projectiveQuantumTangentEnergy_le_rayleighExcess_div_gap
    T hT hv hg hTv hgap hcoercive
  refine ⟨hpos, hle, ?_⟩
  have hquotPos : 0 <
      (T.rayleighQuotient (thetaCuspRightLineUnitTangent a ha) - epsilon) / gap :=
    hpos.trans_le hle
  rcases (div_pos_iff.mp hquotPos) with h | h
  · exact sub_pos.mp h.1
  · linarith

end

end RHTower
