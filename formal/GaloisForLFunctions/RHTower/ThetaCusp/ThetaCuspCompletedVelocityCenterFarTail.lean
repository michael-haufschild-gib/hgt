import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCompletedCurvatureProjectiveFarTail

/-!
# Cofinal closure of the completed fixed-action velocity-center endpoint

This file integrates the cofinal projective law for completed theta curvature twice.  If
`A = -(log Theta)''`, the strict decrease of `A'' / A` forces strict increase of
`3(A')^(2 : ℕ) - 2AA''`.  These two endpoint comparisons make the second reflected derivative
ratio strictly decreasing.  Two monotone-l'Hospital descents then prove the completed
fixed-action center numerator is strictly negative.

This closes the noncompact part of Conjecture K's zero face.  The remaining zero-face
burden is confined to a compact structural interval; the other three shifted faces remain
separate.
-/

open Real Set Filter Topology

namespace RHTower

noncomputable section

private theorem exists_completedProjectiveTailData :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      0 < thetaCuspLogCurvatureJet x ∧
      0 < thetaCuspLogCurvatureJetTwo x ∧
      0 < thetaCuspLogCurvatureJetThree x ∧
      0 < thetaCuspCompletedCurvatureProjectiveEnergy x := by
  have hpLim : Tendsto (fun x : ℝ =>
      thetaCuspLogCurvatureJet x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 8) := by
    simpa only [thetaCuspLogCurvatureJet] using
      thetaCuspC5FarTail_neg_logJetThree_div_scale_tendsto_eight
  have hBLim : Tendsto (fun x : ℝ =>
      thetaCuspLogCurvatureJetTwo x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 16) := by
    simpa only [thetaCuspLogCurvatureJetTwo] using
      thetaCuspC5FarTail_neg_logJetFour_div_scale_tendsto_sixteen
  have hCLim : Tendsto (fun x : ℝ =>
      thetaCuspLogCurvatureJetThree x /
        thetaCuspSingleAtomReflectionScale 1 x) atTop (nhds 32) := by
    simpa only [thetaCuspLogCurvatureJetThree] using
      thetaCuspC5FarTail_neg_logJetFive_div_scale_tendsto_thirtytwo
  have hpRatio : ∀ᶠ x : ℝ in atTop, 0 <
      thetaCuspLogCurvatureJet x /
        thetaCuspSingleAtomReflectionScale 1 x :=
    (tendsto_order.1 hpLim).1 0 (by norm_num)
  have hBRatio : ∀ᶠ x : ℝ in atTop, 0 <
      thetaCuspLogCurvatureJetTwo x /
        thetaCuspSingleAtomReflectionScale 1 x :=
    (tendsto_order.1 hBLim).1 0 (by norm_num)
  have hCRatio : ∀ᶠ x : ℝ in atTop, 0 <
      thetaCuspLogCurvatureJetThree x /
        thetaCuspSingleAtomReflectionScale 1 x :=
    (tendsto_order.1 hCLim).1 0 (by norm_num)
  have hE := eventually_thetaCuspCompletedCurvatureProjectiveEnergy_pos
  have hall : ∀ᶠ x : ℝ in atTop,
      0 < x ∧ 0 < thetaCuspLogCurvatureJet x ∧
        0 < thetaCuspLogCurvatureJetTwo x ∧
        0 < thetaCuspLogCurvatureJetThree x ∧
        0 < thetaCuspCompletedCurvatureProjectiveEnergy x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hpRatio, hBRatio, hCRatio, hE]
      with x hx hp hB hC henergy
    have hS : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale
      positivity
    have hp' : 0 < thetaCuspLogCurvatureJet x := by
      by_contra hn
      have hnle : thetaCuspLogCurvatureJet x ≤ 0 := le_of_not_gt hn
      have := div_nonpos_of_nonpos_of_nonneg hnle hS.le
      linarith
    have hB' : 0 < thetaCuspLogCurvatureJetTwo x := by
      by_contra hn
      have hnle : thetaCuspLogCurvatureJetTwo x ≤ 0 := le_of_not_gt hn
      have := div_nonpos_of_nonpos_of_nonneg hnle hS.le
      linarith
    have hC' : 0 < thetaCuspLogCurvatureJetThree x := by
      by_contra hn
      have hnle : thetaCuspLogCurvatureJetThree x ≤ 0 := le_of_not_gt hn
      have := div_nonpos_of_nonpos_of_nonneg hnle hS.le
      linarith
    exact ⟨hx, hp', hB', hC', henergy⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hall
  exact ⟨x₀, (hx₀ x₀ le_rfl).1, fun x hx => (hx₀ x hx).2⟩

private theorem completed_exists_derivRatio_eq_incrementRatio
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hgderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hgInc : g b - g a ≠ 0)
    (hg' : ∀ x ∈ Set.Ioo a b, g' x ≠ 0) :
    ∃ c ∈ Set.Ioo a b,
      f' c / g' c = (f b - f a) / (g b - g a) := by
  let lam := (f b - f a) / (g b - g a)
  let k : ℝ → ℝ := fun x => f x - lam * g x
  let k' : ℝ → ℝ := fun x => f' x - lam * g' x
  have hkcont : ContinuousOn k (Set.Icc a b) :=
    hfcont.sub (continuousOn_const.mul hgcont)
  have hkderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt k (k' x) x := by
    intro x hx
    have hraw := (hfderiv x hx).sub ((hgderiv x hx).const_mul lam)
    refine (hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    ring
  obtain ⟨c, hc, hcslope⟩ :=
    exists_hasDerivAt_eq_slope k k' hab hkcont hkderiv
  have hkEnds : k b - k a = 0 := by
    dsimp only [k, lam]
    field_simp [hgInc]
    ring
  have hk'zero : k' c = 0 := by rw [hcslope, hkEnds]; simp
  refine ⟨c, hc, ?_⟩
  have hlinear : f' c = lam * g' c := by
    dsimp only [k'] at hk'zero
    linarith
  rw [div_eq_iff (hg' c hc)]
  exact hlinear

private theorem completed_div_derivativeNumerator_neg_of_strictAnti_derivRatio
    {f g f' g' : ℝ → ℝ} {a b x : ℝ}
    (hab : a < b) (hx : x ∈ Set.Ioc a b)
    (hfa : f a = 0) (hga : g a = 0)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hgderiv : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y)
    (hg'pos : ∀ y ∈ Set.Ioc a b, 0 < g' y)
    (hratio : StrictAntiOn (fun y => f' y / g' y) (Set.Ioc a b)) :
    f' x * g x - f x * g' x < 0 := by
  have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
  have hgmono : StrictMonoOn g (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro y hy
      exact (hgderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hgderiv y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hg'pos y ⟨hy.1, hy.2.le⟩
  have hgx : 0 < g x := by
    rw [← hga]
    exact hgmono (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩) hxIcc hx.1
  have hfcontAx : ContinuousOn f (Set.Icc a x) :=
    hfcont.mono (by intro y hy; exact ⟨hy.1, hy.2.trans hx.2⟩)
  have hgcontAx : ContinuousOn g (Set.Icc a x) :=
    hgcont.mono (by intro y hy; exact ⟨hy.1, hy.2.trans hx.2⟩)
  obtain ⟨c, hc, hcRatio⟩ := completed_exists_derivRatio_eq_incrementRatio
    hx.1 hfcontAx hgcontAx
    (fun y hy => hfderiv y ⟨hy.1.le, hy.2.le.trans hx.2⟩)
    (fun y hy => hgderiv y ⟨hy.1.le, hy.2.le.trans hx.2⟩)
    (by rw [hga]; simpa only [sub_zero] using hgx.ne')
    (fun y hy => (hg'pos y ⟨hy.1, hy.2.le.trans hx.2⟩).ne')
  have hcIoc : c ∈ Set.Ioc a b := ⟨hc.1, hc.2.le.trans hx.2⟩
  have hratioCx := hratio hcIoc hx hc.2
  have hquot : f' x / g' x < f x / g x := by
    change f' x / g' x < f' c / g' c at hratioCx
    rw [hcRatio, hfa, hga, sub_zero, sub_zero] at hratioCx
    exact hratioCx
  have hcross := (div_lt_div_iff₀ (hg'pos x hx) hgx).mp hquot
  linarith

private theorem completed_strictAntiOn_div_of_strictAnti_derivRatio
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hfa : f a = 0) (hga : g a = 0)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hgderiv : ∀ y ∈ Set.Icc a b, HasDerivAt g (g' y) y)
    (hg'pos : ∀ y ∈ Set.Ioc a b, 0 < g' y)
    (hratio : StrictAntiOn (fun y => f' y / g' y) (Set.Ioc a b)) :
    StrictAntiOn (fun y => f y / g y) (Set.Ioc a b) := by
  have hgmono : StrictMonoOn g (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · intro y hy
      exact (hgderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hgderiv y ⟨hy.1.le, hy.2.le⟩).deriv]
      exact hg'pos y ⟨hy.1, hy.2.le⟩
  apply strictAntiOn_of_deriv_neg (convex_Ioc a b)
  · intro x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
    have hgx : 0 < g x := by
      rw [← hga]
      exact hgmono (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩) hxIcc hx.1
    exact ((hfderiv x hxIcc).div (hgderiv x hxIcc) hgx.ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hxIoc : x ∈ Set.Ioc a b := ⟨hx.1, hx.2.le⟩
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
    have hgx : 0 < g x := by
      rw [← hga]
      exact hgmono (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab.le⟩) hxIcc hx.1
    change deriv (f / g) x < 0
    rw [((hfderiv x hxIcc).div (hgderiv x hxIcc) hgx.ne').deriv]
    exact div_neg_of_neg_of_pos
      (completed_div_derivativeNumerator_neg_of_strictAnti_derivRatio
        hab hxIoc hfa hga hfcont hgcont hfderiv hgderiv hg'pos hratio)
      (sq_pos_of_pos hgx)

private theorem hasDerivAt_completedDecaySlope (x : ℝ) :
    HasDerivAt thetaCuspLogDecaySlope (thetaCuspLogCurvature x) x := by
  unfold thetaCuspLogDecaySlope thetaCuspLogCurvature
  change HasDerivAt (-iteratedDeriv 1 thetaCuspLogSource)
    (-iteratedDeriv 2 thetaCuspLogSource x) x
  simpa only [Nat.reduceAdd] using
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 x).neg

private theorem hasDerivAt_completedCurvatureJetThree (x : ℝ) :
    HasDerivAt thetaCuspLogCurvatureJetThree
      (-iteratedDeriv 6 thetaCuspLogSource x) x := by
  unfold thetaCuspLogCurvatureJetThree
  change HasDerivAt (-iteratedDeriv 5 thetaCuspLogSource)
    (-iteratedDeriv 6 thetaCuspLogSource x) x
  simpa only [Nat.reduceAdd] using
    (hasDerivAt_iteratedDeriv_thetaCuspLogSource 5 x).neg

private def completedCurvatureJetSum (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJet (u + t) + thetaCuspLogCurvatureJet (u - t)

private def completedCurvatureJetDifference (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJet (u + t) - thetaCuspLogCurvatureJet (u - t)

private def completedCurvatureJetTwoDifference (u t : ℝ) : ℝ :=
  thetaCuspLogCurvatureJetTwo (u + t) - thetaCuspLogCurvatureJetTwo (u - t)

private def completedSecondTransportDenominator (u t : ℝ) : ℝ :=
  2 * thetaCuspReflectedLogJetTwo u t +
    t * completedCurvatureJetDifference u t

private def completedFirstTransportDenominator (u t : ℝ) : ℝ :=
  thetaCuspReflectedLogJetOne u t +
    t * thetaCuspReflectedLogJetTwo u t

private def completedTransportScaleDenominator (u t : ℝ) : ℝ :=
  t * thetaCuspReflectedLogJetOne u t

private theorem hasDerivAt_completedCurvatureJetSum (u t : ℝ) :
    HasDerivAt (completedCurvatureJetSum u)
      (completedCurvatureJetTwoDifference u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u + t)).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u - t)).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  unfold completedCurvatureJetSum completedCurvatureJetTwoDifference
  convert hp.add hm using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · ring

private theorem hasDerivAt_completedCurvatureJetDifference (u t : ℝ) :
    HasDerivAt (completedCurvatureJetDifference u)
      (thetaCuspLogCurvatureJetTwo (u + t) +
        thetaCuspLogCurvatureJetTwo (u - t)) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvatureJet (u + t)).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hm := (hasDerivAt_thetaCuspLogCurvatureJet (u - t)).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  unfold completedCurvatureJetDifference
  convert hp.sub hm using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · ring

private theorem hasDerivAt_completedSecondTransportDenominator (u t : ℝ) :
    HasDerivAt (completedSecondTransportDenominator u)
      (3 * completedCurvatureJetDifference u t +
        t * (thetaCuspLogCurvatureJetTwo (u + t) +
          thetaCuspLogCurvatureJetTwo (u - t))) t := by
  have hb : HasDerivAt (thetaCuspReflectedLogJetTwo u)
      (completedCurvatureJetDifference u t) t := by
    have hp := (hasDerivAt_thetaCuspLogCurvature (u + t)).comp t
      ((hasDerivAt_const t u).add (hasDerivAt_id t))
    have hm := (hasDerivAt_thetaCuspLogCurvature (u - t)).comp t
      ((hasDerivAt_const t u).sub (hasDerivAt_id t))
    unfold thetaCuspReflectedLogJetTwo completedCurvatureJetDifference
    convert hp.add hm using 1
    · apply AddCommGroup.ext
      rfl
    · apply Module.ext
      rfl
    · funext x
      rfl
    · ring
  have hdiff := hasDerivAt_completedCurvatureJetDifference u t
  have hraw := (hb.const_mul 2).add ((hasDerivAt_id t).mul hdiff)
  unfold completedSecondTransportDenominator
  convert hraw using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · simp only [id_eq]
    ring

private theorem hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogCenterMixedJetOne u)
      (completedCurvatureJetSum u t) t := by
  have hp := (hasDerivAt_thetaCuspLogCurvature (u + t)).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hm := (hasDerivAt_thetaCuspLogCurvature (u - t)).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  unfold thetaCuspReflectedLogCenterMixedJetOne completedCurvatureJetSum
  convert hp.sub hm using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · ring

private theorem hasDerivAt_completedFirstTransportDenominator (u t : ℝ) :
    HasDerivAt (completedFirstTransportDenominator u)
      (completedSecondTransportDenominator u t) t := by
  have ha : HasDerivAt (thetaCuspReflectedLogJetOne u)
      (thetaCuspReflectedLogJetTwo u t) t :=
    hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hb : HasDerivAt (thetaCuspReflectedLogJetTwo u)
      (completedCurvatureJetDifference u t) t := by
    have hp := (hasDerivAt_thetaCuspLogCurvature (u + t)).comp t
      ((hasDerivAt_const t u).add (hasDerivAt_id t))
    have hm := (hasDerivAt_thetaCuspLogCurvature (u - t)).comp t
      ((hasDerivAt_const t u).sub (hasDerivAt_id t))
    unfold thetaCuspReflectedLogJetTwo completedCurvatureJetDifference
    convert hp.add hm using 1
    · apply AddCommGroup.ext
      rfl
    · apply Module.ext
      rfl
    · funext x
      rfl
    · ring
  have hraw := ha.add ((hasDerivAt_id t).mul hb)
  unfold completedFirstTransportDenominator completedSecondTransportDenominator
  convert hraw using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · simp only [id_eq]
    ring

private theorem hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement
    (u t : ℝ) :
    HasDerivAt (thetaCuspReflectedLogCenterJetOne u)
      (thetaCuspReflectedLogCenterMixedJetOne u t) t := by
  have hp := (hasDerivAt_completedDecaySlope (u + t)).comp t
    ((hasDerivAt_const t u).add (hasDerivAt_id t))
  have hm := (hasDerivAt_completedDecaySlope (u - t)).comp t
    ((hasDerivAt_const t u).sub (hasDerivAt_id t))
  unfold thetaCuspReflectedLogCenterJetOne thetaCuspReflectedLogCenterMixedJetOne
  have hraw := (hp.add hm).sub_const (2 * thetaCuspLogDecaySlope u)
  convert hraw using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · ring

private theorem hasDerivAt_completedTransportScaleDenominator (u t : ℝ) :
    HasDerivAt (completedTransportScaleDenominator u)
      (completedFirstTransportDenominator u t) t := by
  have ha : HasDerivAt (thetaCuspReflectedLogJetOne u)
      (thetaCuspReflectedLogJetTwo u t) t :=
    hasDerivAt_thetaCuspReflectedLogJetOne u t
  have hraw := (hasDerivAt_id t).mul ha
  unfold completedTransportScaleDenominator completedFirstTransportDenominator
  convert hraw using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext x
    rfl
  · simp only [id_eq]
    ring

/-- Auxiliary projective potential whose increase supplies the second endpoint
comparison after the decrease of `A'' / A`. -/
private def completedCurvatureProjectivePotential (x : ℝ) : ℝ :=
  3 * thetaCuspLogCurvatureJet x ^ (2 : ℕ) -
    2 * thetaCuspLogCurvature x * thetaCuspLogCurvatureJetTwo x

private theorem hasDerivAt_completedCurvatureProjectivePotential (x : ℝ) :
    HasDerivAt completedCurvatureProjectivePotential
      (4 * thetaCuspLogCurvatureJet x * thetaCuspLogCurvatureJetTwo x -
        2 * thetaCuspLogCurvature x * thetaCuspLogCurvatureJetThree x) x := by
  have hp := hasDerivAt_thetaCuspLogCurvatureJet x
  have hA := hasDerivAt_thetaCuspLogCurvature x
  have hB := hasDerivAt_thetaCuspLogCurvatureJetTwo x
  have hraw := ((hp.mul hp).const_mul 3).sub ((hA.mul hB).const_mul 2)
  unfold completedCurvatureProjectivePotential
  convert hraw using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · funext y
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  · ring

private theorem exists_completedTailOrderData :
    ∃ x₀ : ℝ, 0 < x₀ ∧
      (∀ x : ℝ, x₀ ≤ x →
        0 < thetaCuspLogCurvatureJet x ∧
        0 < thetaCuspLogCurvatureJetTwo x ∧
        0 < thetaCuspLogCurvatureJetThree x ∧
        0 < thetaCuspCompletedCurvatureProjectiveEnergy x) ∧
      StrictMonoOn thetaCuspLogCurvatureJet (Set.Ici x₀) ∧
      StrictAntiOn thetaCuspCompletedCurvatureProjectiveRatio (Set.Ici x₀) ∧
      StrictMonoOn completedCurvatureProjectivePotential (Set.Ici x₀) := by
  obtain ⟨x₀, hx₀, hdata⟩ := exists_completedProjectiveTailData
  have hpMono : StrictMonoOn thetaCuspLogCurvatureJet (Set.Ici x₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
    · intro x hx
      exact (hasDerivAt_thetaCuspLogCurvatureJet x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_thetaCuspLogCurvatureJet x).deriv]
      exact (hdata x hx.le).2.1
  have hratioAnti :
      StrictAntiOn thetaCuspCompletedCurvatureProjectiveRatio (Set.Ici x₀) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x₀)
    · intro x hx
      exact (hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_thetaCuspCompletedCurvatureProjectiveRatio x).deriv]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (hdata x hx.le).2.2.2)
        (sq_pos_of_pos (thetaCuspLogCurvature_pos x))
  have hpotentialMono :
      StrictMonoOn completedCurvatureProjectivePotential (Set.Ici x₀) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
    · intro x hx
      exact (hasDerivAt_completedCurvatureProjectivePotential x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hasDerivAt_completedCurvatureProjectivePotential x).deriv]
      have hp := (hdata x hx.le).1
      have hB := (hdata x hx.le).2.1
      have hE := (hdata x hx.le).2.2.2
      unfold thetaCuspCompletedCurvatureProjectiveEnergy at hE
      nlinarith [mul_pos hp hB]
  exact ⟨x₀, hx₀, hdata, hpMono, hratioAnti, hpotentialMono⟩

private theorem completedSecondTransportDenominator_pos
    {x₀ u t : ℝ} (ht : 0 < t) (hleft : x₀ ≤ u - t)
    (hpMono : StrictMonoOn thetaCuspLogCurvatureJet (Set.Ici x₀)) :
    0 < completedSecondTransportDenominator u t := by
  have hlr : u - t < u + t := by linarith
  have hright : x₀ ≤ u + t := hleft.trans hlr.le
  have hpDiff := hpMono (show u - t ∈ Set.Ici x₀ by exact hleft)
    (show u + t ∈ Set.Ici x₀ by exact hright) hlr
  have hpDiffPos : 0 <
      thetaCuspLogCurvatureJet (u + t) -
        thetaCuspLogCurvatureJet (u - t) := sub_pos.mpr hpDiff
  have hAl := thetaCuspLogCurvature_pos (u - t)
  have hAr := thetaCuspLogCurvature_pos (u + t)
  unfold completedSecondTransportDenominator thetaCuspReflectedLogJetTwo
    completedCurvatureJetDifference
  nlinarith [mul_pos ht hpDiffPos]

private theorem completedFirstTransportDenominator_pos
    {u t : ℝ} (ht : 0 < t) :
    0 < completedFirstTransportDenominator u t := by
  have ha := thetaCuspReflectedLogJetOne_pos u ht
  have hAl := thetaCuspLogCurvature_pos (u - t)
  have hAr := thetaCuspLogCurvature_pos (u + t)
  unfold completedFirstTransportDenominator thetaCuspReflectedLogJetTwo
  nlinarith [mul_pos ht (add_pos hAr hAl)]

private theorem completedTransportScaleDenominator_pos
    {u t : ℝ} (ht : 0 < t) :
    0 < completedTransportScaleDenominator u t := by
  unfold completedTransportScaleDenominator
  exact mul_pos ht (thetaCuspReflectedLogJetOne_pos u ht)

private theorem completedSecondTransportRatio_strictAnti
    {x₀ u t : ℝ}
    (hdata : ∀ x : ℝ, x₀ ≤ x →
      0 < thetaCuspLogCurvatureJet x ∧
      0 < thetaCuspLogCurvatureJetTwo x ∧
      0 < thetaCuspLogCurvatureJetThree x ∧
      0 < thetaCuspCompletedCurvatureProjectiveEnergy x)
    (hpMono : StrictMonoOn thetaCuspLogCurvatureJet (Set.Ici x₀))
    (hratioAnti :
      StrictAntiOn thetaCuspCompletedCurvatureProjectiveRatio (Set.Ici x₀))
    (hpotentialMono :
      StrictMonoOn completedCurvatureProjectivePotential (Set.Ici x₀))
    (hleft : x₀ ≤ u - t) :
    StrictAntiOn
      (fun y => completedCurvatureJetSum u y /
        completedSecondTransportDenominator u y) (Set.Ioc 0 t) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 t)
  · intro y hy
    have hleftY : x₀ ≤ u - y := by linarith [hy.2]
    have hden := completedSecondTransportDenominator_pos hy.1 hleftY hpMono
    exact ((hasDerivAt_completedCurvatureJetSum u y).div
      (hasDerivAt_completedSecondTransportDenominator u y) hden.ne').continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    have hyIoc : y ∈ Set.Ioc (0 : ℝ) t := ⟨hy.1, hy.2.le⟩
    have hleftY : x₀ ≤ u - y := by linarith [hyIoc.2]
    have hlr : u - y < u + y := by linarith [hyIoc.1]
    have hrightY : x₀ ≤ u + y := hleftY.trans hlr.le
    have hlSet : u - y ∈ Set.Ici x₀ := hleftY
    have hrSet : u + y ∈ Set.Ici x₀ := hrightY
    have hpl := (hdata (u - y) hleftY).1
    have hpr := (hdata (u + y) hrightY).1
    have hBl := (hdata (u - y) hleftY).2.1
    have hBr := (hdata (u + y) hrightY).2.1
    have hratioCompare := hratioAnti hlSet hrSet hlr
    have hprojective :
        thetaCuspLogCurvatureJetTwo (u + y) *
            thetaCuspLogCurvature (u - y) <
          thetaCuspLogCurvatureJetTwo (u - y) *
            thetaCuspLogCurvature (u + y) := by
      unfold thetaCuspCompletedCurvatureProjectiveRatio at hratioCompare
      exact (div_lt_div_iff₀ (thetaCuspLogCurvature_pos (u + y))
        (thetaCuspLogCurvature_pos (u - y))).mp hratioCompare
    have hpotentialCompare := hpotentialMono hlSet hrSet hlr
    have hmix : 0 <
        thetaCuspLogCurvatureJetTwo (u + y) *
            thetaCuspLogCurvatureJet (u - y) +
          thetaCuspLogCurvatureJetTwo (u - y) *
            thetaCuspLogCurvatureJet (u + y) :=
      add_pos (mul_pos hBr hpl) (mul_pos hBl hpr)
    have hdecomp :
        completedCurvatureJetTwoDifference u y *
              completedSecondTransportDenominator u y -
            completedCurvatureJetSum u y *
              (3 * completedCurvatureJetDifference u y +
                y * (thetaCuspLogCurvatureJetTwo (u + y) +
                  thetaCuspLogCurvatureJetTwo (u - y))) =
          2 * (thetaCuspLogCurvature (u - y) *
                thetaCuspLogCurvatureJetTwo (u + y) -
              thetaCuspLogCurvature (u + y) *
                thetaCuspLogCurvatureJetTwo (u - y)) -
            2 * y *
              (thetaCuspLogCurvatureJetTwo (u + y) *
                  thetaCuspLogCurvatureJet (u - y) +
                thetaCuspLogCurvatureJetTwo (u - y) *
                  thetaCuspLogCurvatureJet (u + y)) +
            (completedCurvatureProjectivePotential (u - y) -
              completedCurvatureProjectivePotential (u + y)) := by
      unfold completedCurvatureJetTwoDifference completedSecondTransportDenominator
        thetaCuspReflectedLogJetTwo completedCurvatureJetDifference
        completedCurvatureJetSum completedCurvatureProjectivePotential
      ring
    have hN :
        completedCurvatureJetTwoDifference u y *
              completedSecondTransportDenominator u y -
            completedCurvatureJetSum u y *
              (3 * completedCurvatureJetDifference u y +
                y * (thetaCuspLogCurvatureJetTwo (u + y) +
                  thetaCuspLogCurvatureJetTwo (u - y))) < 0 := by
      rw [hdecomp]
      nlinarith [mul_pos hyIoc.1 hmix]
    have hden := completedSecondTransportDenominator_pos hyIoc.1 hleftY hpMono
    have hquot := (hasDerivAt_completedCurvatureJetSum u y).div
      (hasDerivAt_completedSecondTransportDenominator u y) hden.ne'
    change deriv (completedCurvatureJetSum u /
      completedSecondTransportDenominator u) y < 0
    rw [hquot.deriv]
    exact div_neg_of_neg_of_pos hN (sq_pos_of_pos hden)

/-- **Cofinal completed endpoint closure.**  Beyond one source threshold, every physical
fixed-action displacement has strictly negative completed velocity-centre numerator.

This is an unconditional, non-computational discharge of the noncompact part of
Conjecture K's zero face. -/
theorem exists_c5CompletedVelocityCenterNumerator_neg_farTail :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ u t : ℝ, 0 < t → x₀ ≤ u - t →
      c5CompletedVelocityCenterNumerator u t < 0 := by
  obtain ⟨x₀, hx₀, hdata, hpMono, hratioAnti, hpotentialMono⟩ :=
    exists_completedTailOrderData
  refine ⟨x₀, hx₀, ?_⟩
  intro u t ht hleft
  have hsecondRatio := completedSecondTransportRatio_strictAnti
    hdata hpMono hratioAnti hpotentialMono hleft
  have hmZero : thetaCuspReflectedLogCenterMixedJetOne u 0 = 0 := by
    unfold thetaCuspReflectedLogCenterMixedJetOne
    ring_nf
  have hfirstDenZero : completedFirstTransportDenominator u 0 = 0 := by
    unfold completedFirstTransportDenominator thetaCuspReflectedLogJetOne
      thetaCuspReflectedLogJetTwo
    ring_nf
  have hfirstRatio : StrictAntiOn
      (fun y => thetaCuspReflectedLogCenterMixedJetOne u y /
        completedFirstTransportDenominator u y) (Set.Ioc 0 t) := by
    apply completed_strictAntiOn_div_of_strictAnti_derivRatio
      (f := thetaCuspReflectedLogCenterMixedJetOne u)
      (g := completedFirstTransportDenominator u)
      (f' := completedCurvatureJetSum u)
      (g' := completedSecondTransportDenominator u)
      ht hmZero hfirstDenZero
    · intro y hy
      exact (hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement u y).continuousAt.continuousWithinAt
    · intro y hy
      exact (hasDerivAt_completedFirstTransportDenominator u y).continuousAt.continuousWithinAt
    · intro y hy
      exact hasDerivAt_thetaCuspReflectedLogCenterMixedJetOne_displacement u y
    · intro y hy
      exact hasDerivAt_completedFirstTransportDenominator u y
    · intro y hy
      have hleftY : x₀ ≤ u - y := by linarith [hy.2]
      exact completedSecondTransportDenominator_pos hy.1 hleftY hpMono
    · exact hsecondRatio
  have hsZero : thetaCuspReflectedLogCenterJetOne u 0 = 0 := by
    unfold thetaCuspReflectedLogCenterJetOne
    ring_nf
  have hscaleZero : completedTransportScaleDenominator u 0 = 0 := by
    unfold completedTransportScaleDenominator
    ring
  have hfinal := completed_div_derivativeNumerator_neg_of_strictAnti_derivRatio
    (f := thetaCuspReflectedLogCenterJetOne u)
    (g := completedTransportScaleDenominator u)
    (f' := thetaCuspReflectedLogCenterMixedJetOne u)
    (g' := completedFirstTransportDenominator u)
    ht (show t ∈ Set.Ioc (0 : ℝ) t by exact ⟨ht, le_rfl⟩)
    hsZero hscaleZero
    (fun y hy =>
      (hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement u y).continuousAt.continuousWithinAt)
    (fun y hy =>
      (hasDerivAt_completedTransportScaleDenominator u y).continuousAt.continuousWithinAt)
    (fun y hy => hasDerivAt_thetaCuspReflectedLogCenterJetOne_displacement u y)
    (fun y hy => hasDerivAt_completedTransportScaleDenominator u y)
    (fun y hy => completedFirstTransportDenominator_pos hy.1)
    hfirstRatio
  have hintrinsic :
      thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t < 0 := by
    have heq :
        thetaCuspReflectedActionVelocityFixedActionCenterNumerator u t =
          thetaCuspReflectedLogCenterMixedJetOne u t *
              completedTransportScaleDenominator u t -
            thetaCuspReflectedLogCenterJetOne u t *
              completedFirstTransportDenominator u t := by
      unfold thetaCuspReflectedActionVelocityFixedActionCenterNumerator
        completedTransportScaleDenominator completedFirstTransportDenominator
      ring
    rw [heq]
    exact hfinal
  have htu : t < u := by linarith
  rw [c5CompletedVelocityCenterNumerator_eq_intrinsic ht htu]
  exact hintrinsic

end


end RHTower
