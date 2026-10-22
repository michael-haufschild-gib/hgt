import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthSeamOrientation
/-! The complete source-growth sign gives a positive, strictly decreasing
Sturm flux for the fifth-versus-third defect. Exact integration supplies
strict finite-interval bounds in its natural clock, retaining the complete
source and its rational factor. The nonlocal C5 compensation sign remains open. -/

namespace RHTower.ThetaCuspDefect
open Set Filter Topology MeasureTheory
noncomputable section

local notation "q" => thetaCuspLikelihoodCoordinate
local notation "F" => fun x => sourceDefectFactor (q x)

def sourceDefectJet (x : ℝ) : ℝ :=
  iteratedDeriv 5 thetaCuspLogSource x-4*iteratedDeriv 3 thetaCuspLogSource x

def sourceDefectJetSlope (x : ℝ) : ℝ :=
  iteratedDeriv 6 thetaCuspLogSource x-4*iteratedDeriv 4 thetaCuspLogSource x

def defectSturmFlux (x : ℝ) : ℝ :=
  F x*(sourceDefectJetSlope x-factorLogSlope (q x)*sourceDefectJet x)

def normalizedSourceDefect (x : ℝ) : ℝ := sourceDefectJet x/F x

theorem hasDerivAt_factorLogSlope_coordinate {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => factorLogSlope (q t))
      (2*(q x+3/2)*(3/(q x+3)^2+15/(q x)^2)) x := by
  have hq := thetaCuspLikelihoodCoordinate_pos hx
  have hq3 : q x+3 ≠ 0 := by positivity
  have hA := (hasDerivAt_id (q x)).add_const (3/2:ℝ)
  have hd := ((hasDerivAt_const (q x) (4:ℝ)).add
    ((hA.const_mul 2).div ((hasDerivAt_id (q x)).add_const 3) hq3)).sub
      ((hA.const_mul 10).div (hasDerivAt_id (q x)) hq.ne')
  convert! hd.comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x) using 1
  dsimp only [id_eq]
  rw [thetaCuspC5FarTail_scale_eq_coordinate_add]
  field_simp [hq.ne',hq3]
  ring

theorem hasDerivAt_sourceDefectJet (x : ℝ) :
    HasDerivAt sourceDefectJet (sourceDefectJetSlope x) x := by
  exact (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).sub
    ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 3 x).const_mul 4)

theorem hasDerivAt_sourceDefectJetSlope (x : ℝ) :
    HasDerivAt sourceDefectJetSlope
      (iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x) x := by
  exact (hasDerivAt_iteratedDeriv_thetaCuspLogSource 6 x).sub
    ((hasDerivAt_iteratedDeriv_thetaCuspLogSource 4 x).const_mul 4)

theorem hasDerivAt_defectSturmFlux {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt defectSturmFlux
      (F x*((iteratedDeriv 7 thetaCuspLogSource x-4*iteratedDeriv 5 thetaCuspLogSource x)-
        factorCurvature (q x)*sourceDefectJet x)) x := by
  have hd := (hasDerivAt_sourceDefectFactor_coordinate hx).mul
    ((hasDerivAt_sourceDefectJetSlope x).sub
      ((hasDerivAt_factorLogSlope_coordinate hx).mul (hasDerivAt_sourceDefectJet x)))
  convert! hd using 1
  dsimp only [Pi.sub_apply,Pi.mul_apply]
  unfold factorCurvature
  ring

theorem defectSturmFlux_strictAntiOn : StrictAntiOn defectSturmFlux (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_defectSturmFlux hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(hasDerivAt_defectSturmFlux hx0.le).deriv]
    exact mul_neg_of_pos_of_neg (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx0.le))
      (sub_neg.mpr (sourceDefect_curvature_upper hx0))

theorem defectSturmFlux_pos {x : ℝ} (hx : 0 ≤ x) : 0 < defectSturmFlux x := by
  have hpos : 0 < defectSturmFlux (x+1) := by
    unfold defectSturmFlux
    exact mul_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos (by linarith)))
      (sub_pos.mpr (sourceDefect_slope_lower (by linarith)))
  exact hpos.trans (defectSturmFlux_strictAntiOn hx (show x+1 ∈ Ici (0:ℝ) from by change 0 ≤ x+1; linarith) (by linarith))

theorem hasDerivAt_normalizedSourceDefect {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt normalizedSourceDefect (defectSturmFlux x/(F x)^2) x := by
  have hF := sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx)
  convert! (hasDerivAt_sourceDefectJet x).div (hasDerivAt_sourceDefectFactor_coordinate hx) hF.ne' using 1
  unfold defectSturmFlux
  ring

private theorem continuousOn_defectClockDensity {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun x => 1/(F x)^2) (Icc a b) := by
  intro x hx
  have hx0 := ha.trans hx.1
  exact (continuousAt_const.div ((hasDerivAt_sourceDefectFactor_coordinate hx0).continuousAt.pow 2)
    (pow_ne_zero _ (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx0)).ne')).continuousWithinAt

private theorem continuousOn_defectNormalizedSlope {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (fun x => defectSturmFlux x/(F x)^2) (Icc a b) := by
  intro x hx
  have hx0 := ha.trans hx.1
  exact ((hasDerivAt_defectSturmFlux hx0).continuousAt.div
    ((hasDerivAt_sourceDefectFactor_coordinate hx0).continuousAt.pow 2)
      (pow_ne_zero _ (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos hx0)).ne')).continuousWithinAt

theorem normalizedSourceDefect_sub_eq_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    normalizedSourceDefect b-normalizedSourceDefect a =
      ∫ x in a..b, defectSturmFlux x/(F x)^2 := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_normalizedSourceDefect (ha.trans ((uIcc_of_le hab ▸ hx).1)))
  exact (continuousOn_defectNormalizedSlope ha).intervalIntegrable_of_Icc hab

theorem normalizedSourceDefect_strict_clock_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    defectSturmFlux b*(∫ x in a..b, 1/(F x)^2) <
      normalizedSourceDefect b-normalizedSourceDefect a ∧
    normalizedSourceDefect b-normalizedSourceDefect a <
      defectSturmFlux a*(∫ x in a..b, 1/(F x)^2) := by
  have hb := ha.trans hab.le
  have hclock := continuousOn_defectClockDensity (b := b) ha
  have hnorm := continuousOn_defectNormalizedSlope (b := b) ha
  have hfpos (x : ℝ) (hx : x ∈ Icc a b) : 0 < (F x)^2 :=
    pow_pos (sourceDefectFactor_pos (thetaCuspLikelihoodCoordinate_pos (ha.trans hx.1))) 2
  have hlow : (∫ x in a..b, defectSturmFlux b*(1/(F x)^2)) <
      ∫ x in a..b, defectSturmFlux x/(F x)^2 := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      (continuousOn_const.mul hclock) hnorm
    · intro x hx
      have hZ := defectSturmFlux_strictAntiOn.antitoneOn (ha.trans hx.1.le) hb hx.2
      simpa only [Pi.mul_apply,mul_one_div] using div_le_div_of_nonneg_right hZ (hfpos x ⟨hx.1.le,hx.2⟩).le
    · refine ⟨a,⟨le_rfl,hab.le⟩,?_⟩
      simpa only [Pi.mul_apply,mul_one_div] using div_lt_div_of_pos_right (defectSturmFlux_strictAntiOn ha hb hab) (hfpos a ⟨le_rfl,hab.le⟩)
  have hupp : (∫ x in a..b, defectSturmFlux x/(F x)^2) <
      ∫ x in a..b, defectSturmFlux a*(1/(F x)^2) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      hnorm (continuousOn_const.mul hclock)
    · intro x hx
      have hZ := defectSturmFlux_strictAntiOn.antitoneOn ha (ha.trans hx.1.le) hx.1.le
      simpa only [Pi.mul_apply,mul_one_div] using div_le_div_of_nonneg_right hZ (hfpos x ⟨hx.1.le,hx.2⟩).le
    · refine ⟨b,⟨hab.le,le_rfl⟩,?_⟩
      simpa only [Pi.mul_apply,mul_one_div] using div_lt_div_of_pos_right (defectSturmFlux_strictAntiOn ha hb hab) (hfpos b ⟨hab.le,le_rfl⟩)
  rw [intervalIntegral.integral_const_mul] at hlow hupp
  rw [normalizedSourceDefect_sub_eq_integral ha hab.le]
  exact ⟨hlow,hupp⟩

end
end RHTower.ThetaCuspDefect
