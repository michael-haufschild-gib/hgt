import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspC5CorrelatedFourthSource
/-! Exact primitive-Wronskian dissipation of the actual curvature defect.
The correlated fourth-source slack gives strict concavity in the primitive
clock, hence one supporting tangent for both reflected source endpoints.
These interval constraints retain the common source; the complete inner
inverse-clock current sign remains an open obligation. -/
namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section
local notation "G" => sourceDefectPrimitive
local notation "B" => curvatureDefect
local notation "H" => sourceDefectJet
local notation "q" => thetaCuspLikelihoodCoordinate
local notation "F" => fun x => sourceDefectFactor (q x)
local notation "sigma" => fun x => sourceCorrelatedFourthEnvelope x-thetaCuspLogCurvatureJetFour x

/-- Wronskian of the actual curvature defect and its exact source primitive. -/
def curvatureDefectPrimitiveFlux (x : ℝ) : ℝ := F x*B x-G x*H x
local notation "J" => curvatureDefectPrimitiveFlux

theorem curvatureDefectPrimitiveFlux_eq_reserve {x : ℝ} (hx : 0 ≤ x) :
    J x=F x*sourcePrimitiveReserve x := by
  unfold curvatureDefectPrimitiveFlux sourcePrimitiveReserve normalizedSourceDefect
  field_simp [(sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)).ne']

theorem curvatureDefectPrimitiveFlux_pos {x : ℝ} (hx : 0 ≤ x) : 0 < J x := by
  rw [curvatureDefectPrimitiveFlux_eq_reserve hx]
  exact mul_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx))
    (sourcePrimitiveReserve_pos hx)

/-- The correlated fourth-source slack is exactly the dissipation of this flux. -/
theorem hasDerivAt_curvatureDefectPrimitiveFlux {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt J (-G x*sigma x) x := by
  have hB : HasDerivAt B (-H x) x := by
    convert! hasDerivAt_curvatureDefect x using 1
    unfold thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet sourceDefectJet
    ring
  have hcoef : sourceFourthTransportRate x*G x= -factorLogSlope (q x)*F x := by
    rw [sourceFourthTransportRate_factor hx,←sourceDefectPrimitive_mul_rate hx]
    ring
  have hd:=((hasDerivAt_sourceDefectFactor_coordinate hx).mul hB).sub
    ((hasDerivAt_sourceDefectPrimitive hx).mul (hasDerivAt_sourceDefectJet x))
  convert! hd using 1
  unfold sourceCorrelatedFourthEnvelope sourceDefectJetSlope thetaCuspLogCurvatureJetFour
    thetaCuspLogCurvatureJetTwo
  dsimp only
  linear_combination -curvatureDefect x*hcoef

theorem curvatureDefectPrimitiveFlux_strictAntiOn : StrictAntiOn J (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_curvatureDefectPrimitiveFlux hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(hasDerivAt_curvatureDefectPrimitiveFlux hx0).deriv]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (sourceDefectPrimitive_pos hx0))
      (sub_pos.mpr (sourceCorrelatedFourthEnvelope_gt_actual hx0))

theorem normalizedCurvatureDefect_deriv_eq_flux {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt normalizedCurvatureDefect (J x/(G x)^2) x := by
  rw [curvatureDefectPrimitiveFlux_eq_reserve hx]
  exact hasDerivAt_normalizedCurvatureDefect hx

private theorem clock_continuousOn {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun x => 1/(G x)^2) (Icc a b) := by
  intro x hx
  exact (continuousAt_const.div ((hasDerivAt_sourceDefectPrimitive (ha.trans hx.1)).continuousAt.pow 2)
    (pow_ne_zero _ (sourceDefectPrimitive_pos (ha.trans hx.1)).ne')).continuousWithinAt
private theorem slope_continuousOn {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun x => J x/(G x)^2) (Icc a b) := by
  intro x hx
  have h:=ha.trans hx.1
  exact ((hasDerivAt_curvatureDefectPrimitiveFlux h).continuousAt.div
    ((hasDerivAt_sourceDefectPrimitive h).continuousAt.pow 2)
    (pow_ne_zero _ (sourceDefectPrimitive_pos h).ne')).continuousWithinAt

theorem normalizedCurvatureDefect_sub_eq_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    normalizedCurvatureDefect b-normalizedCurvatureDefect a =
      ∫ x in a..b, J x/(G x)^2 := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => normalizedCurvatureDefect_deriv_eq_flux (ha.trans ((uIcc_of_le hab ▸ hx).1)))
  exact (slope_continuousOn ha).intervalIntegrable_of_Icc hab

theorem normalizedCurvatureDefect_strict_clock_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    J b*(∫ x in a..b, 1/(G x)^2) <
      normalizedCurvatureDefect b-normalizedCurvatureDefect a ∧
    normalizedCurvatureDefect b-normalizedCurvatureDefect a <
      J a*(∫ x in a..b, 1/(G x)^2) := by
  have hb := ha.trans hab.le
  have hclock := clock_continuousOn (b := b) ha
  have hnorm := slope_continuousOn (b := b) ha
  have hfpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < (G x)^2 :=
    pow_pos (sourceDefectPrimitive_pos (ha.trans hx.1)) 2
  have hlow : (∫ x in a..b, J b*(1/(G x)^2)) <
      ∫ x in a..b, J x/(G x)^2 := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      (continuousOn_const.mul hclock) hnorm
    · intro x hx
      have hZ := curvatureDefectPrimitiveFlux_strictAntiOn.antitoneOn (ha.trans hx.1.le) hb hx.2
      simpa only [Pi.mul_apply,mul_one_div] using div_le_div_of_nonneg_right hZ (hfpos x ⟨hx.1.le,hx.2⟩).le
    · refine ⟨a,⟨le_rfl,hab.le⟩,?_⟩
      simpa only [Pi.mul_apply,mul_one_div] using div_lt_div_of_pos_right (curvatureDefectPrimitiveFlux_strictAntiOn ha hb hab) (hfpos a ⟨le_rfl,hab.le⟩)
  have hupp : (∫ x in a..b, J x/(G x)^2) <
      ∫ x in a..b, J a*(1/(G x)^2) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      hnorm (continuousOn_const.mul hclock)
    · intro x hx
      have hZ := curvatureDefectPrimitiveFlux_strictAntiOn.antitoneOn ha (ha.trans hx.1.le) hx.1.le
      simpa only [Pi.mul_apply,mul_one_div] using div_le_div_of_nonneg_right hZ (hfpos x ⟨hx.1.le,hx.2⟩).le
    · refine ⟨b,⟨hab.le,le_rfl⟩,?_⟩
      simpa only [Pi.mul_apply,mul_one_div] using div_lt_div_of_pos_right (curvatureDefectPrimitiveFlux_strictAntiOn ha hb hab) (hfpos b ⟨hab.le,le_rfl⟩)
  rw [intervalIntegral.integral_const_mul] at hlow hupp
  rw [normalizedCurvatureDefect_sub_eq_integral ha hab.le]
  exact ⟨hlow,hupp⟩

/-- Strict supporting line for the actual normalized defect, at its own source clock. -/
theorem normalizedCurvatureDefect_clock_tangent {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ y) :
    normalizedCurvatureDefect y < normalizedCurvatureDefect x+
      J x*(∫ s in x..y, 1/(G s)^2) := by
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have hh:=(normalizedCurvatureDefect_strict_clock_bounds hx hxy).2
    linarith only [hh]
  · have hh:=(normalizedCurvatureDefect_strict_clock_bounds hy hyx).1
    rw [intervalIntegral.integral_symm x y] at hh
    linarith only [hh]

/-- Both reflected source endpoints are controlled by one center and one flux. -/
theorem curvatureDefectPrimitive_tangent_upper {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ y) :
    B y<G y*(B x/G x+J x*(∫ s in x..y, 1/(G s)^2)) := by
  have hh:=normalizedCurvatureDefect_clock_tangent hx hy hne
  unfold normalizedCurvatureDefect at hh
  have hm:=(div_lt_iff₀ (sourceDefectPrimitive_pos hy)).mp hh
  nlinarith only [hm]

/-- The interval-to-interval slope of the actual defect strictly decreases in its clock. -/
theorem normalizedCurvatureDefect_clock_three_point {a x b : ℝ}
    (ha : 0 ≤ a) (hax : a < x) (hxb : x < b) :
    (normalizedCurvatureDefect b-normalizedCurvatureDefect x)*
        (∫ s in a..x, 1/(G s)^2) <
      (normalizedCurvatureDefect x-normalizedCurvatureDefect a)*
        (∫ s in x..b, 1/(G s)^2) := by
  have hx:=ha.trans hax.le
  have hb:=hx.trans hxb.le
  have hleft:=normalizedCurvatureDefect_strict_clock_bounds ha hax
  have hright:=normalizedCurvatureDefect_strict_clock_bounds hx hxb
  have hI : 0 < ∫ s in a..x, 1/(G s)^2 := by
    have hp:=(sub_pos.mpr (normalizedCurvatureDefect_strictMonoOn ha hx hax)).trans hleft.2
    exact (mul_pos_iff_of_pos_left (curvatureDefectPrimitiveFlux_pos ha)).mp hp
  have hK : 0 < ∫ s in x..b, 1/(G s)^2 := by
    have hp:=(sub_pos.mpr (normalizedCurvatureDefect_strictMonoOn hx hb hxb)).trans hright.2
    exact (mul_pos_iff_of_pos_left (curvatureDefectPrimitiveFlux_pos hx)).mp hp
  have h1:=mul_lt_mul_of_pos_right hleft.1 hK
  have h2:=mul_lt_mul_of_pos_right hright.2 hI
  nlinarith only [h1,h2]

end
end RHTower.ThetaCuspDefect
