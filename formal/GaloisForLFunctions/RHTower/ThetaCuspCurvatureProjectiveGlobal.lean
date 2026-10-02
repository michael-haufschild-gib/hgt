import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectSource
import GaloisForLFunctions.RHTower.ThetaCuspCompletedCurvatureProjectiveFarTail
import GaloisForLFunctions.RHTower.ThetaCuspC5GlobalCurvatureSigns

/-!
# Global strict projective curvature of the complete theta source

The curvature defect b = c'' - 4 c has strictly negative derivative.
Existing tail projective monotonicity and the limit c'' / c -> 4 give
cofinal positivity of b, which propagates to the whole nonnegative axis.
The identity c' c'' - c c''' = c' b + c (L5 - 4 L3) then gives strict
projective positivity on the positive axis.
-/

namespace RHTower.ThetaCuspDefect
open Set Filter
noncomputable section

def curvatureDefect (x : ℝ) : ℝ := thetaCuspLogCurvatureJetTwo x-4*thetaCuspLogCurvature x

theorem hasDerivAt_curvatureDefect (x : ℝ) :
    HasDerivAt curvatureDefect
      (thetaCuspLogCurvatureJetThree x-4*thetaCuspLogCurvatureJet x) x :=
  (hasDerivAt_thetaCuspLogCurvatureJetTwo x).sub ((hasDerivAt_thetaCuspLogCurvature x).const_mul 4)

theorem curvatureDefect_strictAntiOn : StrictAntiOn curvatureDefect (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x _
    exact (hasDerivAt_curvatureDefect x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(hasDerivAt_curvatureDefect x).deriv]
    have h := source_defect_pos hx'
    unfold thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
    linarith

theorem projectiveRatio_tendsto_four :
    Tendsto thetaCuspCompletedCurvatureProjectiveRatio atTop (nhds 4) := by
  have h := thetaCuspC5FarTail_neg_logJetFour_div_scale_tendsto_sixteen.div
    thetaCuspC5FarTail_neg_logJetTwo_div_scale_tendsto_four (show (4:ℝ) ≠ 0 by norm_num)
  have heq : (fun x : ℝ =>
      ((-iteratedDeriv 4 thetaCuspLogSource x)/thetaCuspSingleAtomReflectionScale 1 x)/
        ((-iteratedDeriv 2 thetaCuspLogSource x)/thetaCuspSingleAtomReflectionScale 1 x)) =
      thetaCuspCompletedCurvatureProjectiveRatio := by
    funext x
    have hA : thetaCuspSingleAtomReflectionScale 1 x ≠ 0 := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    have hc : (-iteratedDeriv 2 thetaCuspLogSource x) ≠ 0 :=
      (thetaCuspLogCurvature_pos x).ne'
    unfold thetaCuspCompletedCurvatureProjectiveRatio thetaCuspLogCurvatureJetTwo thetaCuspLogCurvature
    field_simp [hA,hc]
  change Tendsto (fun x : ℝ =>
    ((-iteratedDeriv 4 thetaCuspLogSource x)/thetaCuspSingleAtomReflectionScale 1 x)/
      ((-iteratedDeriv 2 thetaCuspLogSource x)/thetaCuspSingleAtomReflectionScale 1 x))
    atTop (nhds (16/4:ℝ)) at h
  rw [heq] at h
  norm_num at h
  exact h

private theorem eventually_curvatureDefect_pos :
    ∀ᶠ x : ℝ in atTop, 0 < curvatureDefect x := by
  obtain ⟨x0,hx0,hanti⟩ := exists_strictAntiOn_thetaCuspCompletedCurvatureProjectiveRatio_farTail
  filter_upwards [eventually_ge_atTop x0] with x hx
  have hmem : x ∈ Ici x0 := hx
  have hmem1 : x+1 ∈ Ici x0 := by change x0 ≤ x+1; linarith
  have hlim : 4 ≤ thetaCuspCompletedCurvatureProjectiveRatio (x+1) := by
    apply le_of_tendsto projectiveRatio_tendsto_four
    filter_upwards [eventually_gt_atTop (x+1)] with y hy
    have hymem : y ∈ Ici x0 := by change x0 ≤ y; linarith
    exact (hanti hmem1 hymem hy).le
  have hdec := hanti hmem hmem1 (show x < x+1 by linarith)
  have hfour := lt_of_le_of_lt hlim hdec
  change 4 < thetaCuspLogCurvatureJetTwo x/thetaCuspLogCurvature x at hfour
  exact sub_pos.mpr ((lt_div_iff₀ (thetaCuspLogCurvature_pos x)).mp hfour)

theorem curvatureDefect_pos {x : ℝ} (hx : 0 ≤ x) : 0 < curvatureDefect x := by
  obtain ⟨X,hX⟩ := eventually_atTop.1 eventually_curvatureDefect_pos
  let y := max X (x+1)
  have hyX : X ≤ y := le_max_left _ _
  have hxy : x < y := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hy0 : 0 ≤ y := hx.trans hxy.le
  have hdec := curvatureDefect_strictAntiOn (show x ∈ Ici 0 from hx)
    (show y ∈ Ici 0 from hy0) hxy
  exact lt_trans (hX y hyX) hdec

theorem projectiveEnergy_pos {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspCompletedCurvatureProjectiveEnergy x := by
  have hb := curvatureDefect_pos hx.le
  have hc := thetaCuspLogCurvature_pos x
  have hv := thetaCuspLogCurvatureJet_pos_of_pos hx
  have hH := source_defect_pos hx
  have heq : thetaCuspCompletedCurvatureProjectiveEnergy x =
      thetaCuspLogCurvatureJet x*curvatureDefect x+
        thetaCuspLogCurvature x*(iteratedDeriv 5 thetaCuspLogSource x-
          4*iteratedDeriv 3 thetaCuspLogSource x) := by
    unfold thetaCuspCompletedCurvatureProjectiveEnergy curvatureDefect
      thetaCuspLogCurvatureJetThree thetaCuspLogCurvatureJet
    ring
  rw [heq]
  exact add_pos (mul_pos hv hb) (mul_pos hc hH)

theorem projectiveRatio_strictAntiOn :
    StrictAntiOn thetaCuspCompletedCurvatureProjectiveRatio (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x _
    exact (hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    rw [(hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio x).deriv]
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (projectiveEnergy_pos hx'))
      (sq_pos_of_pos (thetaCuspLogCurvature_pos x))

/-- The existing two-step ratio descent now gives center negativity on the
entire same-half-line chamber, with no source-scale cutoff. -/
theorem centerNumerator_neg {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0 := by
  apply centerNumerator_neg_of_curvatureSigns ht htu (x₀ := 0) le_rfl
    (sub_nonneg.mpr htu)
  · intro x _ hx
    exact thetaCuspLogCurvatureJet_pos_of_pos hx
  · intro x _
    exact thetaCuspLogCurvatureJetTwo_pos_all x
  · intro x hx _
    rcases eq_or_lt_of_le hx with rfl | hx
    · simp only [thetaCuspLogCurvatureJetThree, thetaCuspLogCurvatureJet,
        iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 5 from ⟨2,rfl⟩),
        iteratedDeriv_thetaCuspLogSource_zero_of_odd (show Odd 3 from ⟨1,rfl⟩),
        neg_zero, mul_zero, zero_mul, le_refl]
    · have h := projectiveEnergy_pos hx
      unfold thetaCuspCompletedCurvatureProjectiveEnergy at h
      linarith
end
end RHTower.ThetaCuspDefect
