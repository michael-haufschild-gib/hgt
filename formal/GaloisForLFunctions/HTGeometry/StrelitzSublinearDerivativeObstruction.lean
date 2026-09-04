import GaloisForLFunctions.HTGeometry.StrelitzJetCurveSlopeSign

/-!
# Sublinear-growth obstruction for Strelitz branches

A real branch escaping to infinity cannot be sublinear when its derivative, normalized by a
nonnegative real power of the branch, tends to a nonzero constant.  The sign of that constant is
not assumed: a negative limit would force eventual linear decrease and contradict escape, while a
positive limit gives an eventual positive derivative floor and contradicts sublinearity.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A derivative floor on a half-line integrates to the corresponding affine lower bound. -/
theorem linear_lower_bound_of_deriv_ge
    {K K' : ℝ → ℝ} {x0 c : ℝ}
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hlower : ∀ x ∈ Ioi x0, c ≤ K' x) :
    ∀ x ∈ Ici x0, K x0 + c * (x - x0) ≤ K x := by
  intro x hx
  have hxle : x0 ≤ x := hx
  rcases hxle.eq_or_lt with hxeq | hlt
  · subst x
    simp
  · obtain ⟨y, hy, hslope⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
      K K' hlt (hcont.mono fun z hz => hz.1)
      (fun z hz => hderiv z hz.1) id (fun _ => 1) continuousOn_id
      (fun z _ => hasDerivAt_id z)
    have hx0 : 0 ≤ x - x0 := sub_nonneg.mpr hlt.le
    have hmul : c * (x - x0) ≤ K' y * (x - x0) :=
      mul_le_mul_of_nonneg_right (hlower y hy.1) hx0
    simp only [id_eq, mul_one] at hslope
    nlinarith

/-- A positive derivative floor is incompatible with sublinear growth on a half-line. -/
theorem not_tendsto_div_zero_of_deriv_ge_pos
    {K K' : ℝ → ℝ} {x0 c : ℝ}
    (hK0 : 0 ≤ K x0) (hc : 0 < c)
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hlower : ∀ x ∈ Ioi x0, c ≤ K' x) :
    ¬ Tendsto (fun x => K x / x) atTop (nhds 0) := by
  intro hsublinear
  have hlinear := linear_lower_bound_of_deriv_ge hcont hderiv hlower
  have hevent : ∀ᶠ x : ℝ in atTop, c / 2 ≤ K x / x := by
    filter_upwards [eventually_ge_atTop x0, eventually_ge_atTop (2 * x0),
      eventually_ge_atTop 1] with x hxx0 hx2 hx1
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hK : K x0 + c * (x - x0) ≤ K x := hlinear x hxx0
    rw [le_div_iff₀ hxpos]
    nlinarith
  have hc0 : c / 2 ≤ 0 := ge_of_tendsto hsublinear hevent
  linarith

/-- A positive normalized derivative limit at a nonnegative real power excludes sublinear growth. -/
theorem not_tendsto_div_zero_of_nonnegative_rpow_normalized_deriv
    {K K' : ℝ → ℝ} {x0 p c : ℝ}
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hKTop : Tendsto K atTop atTop)
    (hp : 0 ≤ p) (hc : 0 < c)
    (hnormalized : Tendsto (fun x => K' x / K x ^ p) atTop (nhds c)) :
    ¬ Tendsto (fun x => K x / x) atTop (nhds 0) := by
  have hratio : ∀ᶠ x : ℝ in atTop, c / 2 < K' x / K x ^ p :=
    (tendsto_order.1 hnormalized).1 _ (by linarith)
  have hKone : ∀ᶠ x : ℝ in atTop, 1 ≤ K x := hKTop.eventually_ge_atTop 1
  have hlowerEvent : ∀ᶠ x : ℝ in atTop, c / 2 ≤ K' x := by
    filter_upwards [hratio, hKone] with x hratiox hKx
    have hKpos : 0 < K x := lt_of_lt_of_le zero_lt_one hKx
    have hpowPos : 0 < K x ^ p := Real.rpow_pos_of_pos hKpos p
    have hscaled : c / 2 * K x ^ p < K' x :=
      (lt_div_iff₀ hpowPos).mp hratiox
    have hpowOne : 1 ≤ K x ^ p := Real.one_le_rpow hKx hp
    have hcHalf : 0 ≤ c / 2 := by linarith
    simpa using (mul_le_mul_of_nonneg_left hpowOne hcHalf).trans hscaled.le
  obtain ⟨x1, hx1⟩ := eventually_atTop.1 (hlowerEvent.and hKone)
  let x2 := max x0 x1
  have hK2 : 0 ≤ K x2 := by
    have := (hx1 x2 (le_max_right _ _)).2
    linarith
  have hcont2 : ContinuousOn K (Ici x2) :=
    hcont.mono fun x hx => by exact (le_max_left x0 x1).trans hx
  have hderiv2 : ∀ x ∈ Ioi x2, HasDerivAt K (K' x) x := by
    intro x hx
    apply hderiv x
    exact (le_max_left x0 x1).trans_lt hx
  have hlower2 : ∀ x ∈ Ioi x2, c / 2 ≤ K' x := by
    intro x hx
    exact (hx1 x (le_trans (le_max_right _ _) hx.le)).1
  exact not_tendsto_div_zero_of_deriv_ge_pos hK2 (by linarith) hcont2 hderiv2 hlower2

/-- A derivative ceiling on a half-line integrates to the corresponding affine upper bound. -/
theorem linear_upper_bound_of_deriv_le
    {K K' : ℝ → ℝ} {x0 c : ℝ}
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hupper : ∀ x ∈ Ioi x0, K' x ≤ c) :
    ∀ x ∈ Ici x0, K x ≤ K x0 + c * (x - x0) := by
  have hcontNeg : ContinuousOn (fun x => -K x) (Ici x0) := hcont.neg
  have hderivNeg : ∀ x ∈ Ioi x0, HasDerivAt (fun x => -K x) (-K' x) x := by
    intro x hx
    exact (hderiv x hx).neg
  have hlowerNeg : ∀ x ∈ Ioi x0, -c ≤ -K' x := by
    intro x hx
    exact neg_le_neg (hupper x hx)
  intro x hx
  have h := linear_lower_bound_of_deriv_ge hcontNeg hderivNeg hlowerNeg x hx
  change -K x0 + (-c) * (x - x0) ≤ -K x at h
  linarith

/-- A strictly negative derivative ceiling forbids escape to positive infinity. -/
theorem not_tendsto_atTop_of_deriv_le_neg
    {K K' : ℝ → ℝ} {x0 c : ℝ}
    (hc : c < 0)
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hupper : ∀ x ∈ Ioi x0, K' x ≤ c) :
    ¬ Tendsto K atTop atTop := by
  intro hKTop
  have hlinear := linear_upper_bound_of_deriv_le hcont hderiv hupper
  have hlarge : ∀ᶠ x : ℝ in atTop, K x0 < K x := hKTop.eventually_gt_atTop (K x0)
  have hxlarge : ∀ᶠ x : ℝ in atTop, x0 + 1 ≤ x := eventually_ge_atTop (x0 + 1)
  obtain ⟨x, hKx, hx⟩ := (hlarge.and hxlarge).exists
  have hxx0 : x ∈ Ici x0 := by
    change x0 ≤ x
    linarith
  have hbound := hlinear x hxx0
  have hdiff : 1 ≤ x - x0 := by linarith
  have hmul : c * (x - x0) ≤ c := by
    simpa using mul_le_mul_of_nonpos_left hdiff hc.le
  linarith

/-- A nonzero normalized derivative limit on an escaping real branch must be positive. -/
theorem positive_limit_of_nonzero_rpow_normalized_deriv
    {K K' : ℝ → ℝ} {x0 p c : ℝ}
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hKTop : Tendsto K atTop atTop)
    (hp : 0 ≤ p) (hc : c ≠ 0)
    (hnormalized : Tendsto (fun x => K' x / K x ^ p) atTop (nhds c)) :
    0 < c := by
  by_cases hcneg : c < 0
  · have hratio : ∀ᶠ x : ℝ in atTop, K' x / K x ^ p < c / 2 :=
      (tendsto_order.1 hnormalized).2 _ (by linarith)
    have hKone : ∀ᶠ x : ℝ in atTop, 1 ≤ K x := hKTop.eventually_ge_atTop 1
    have hupperEvent : ∀ᶠ x : ℝ in atTop, K' x ≤ c / 2 := by
      filter_upwards [hratio, hKone] with x hratiox hKx
      have hKpos : 0 < K x := lt_of_lt_of_le zero_lt_one hKx
      have hpowPos : 0 < K x ^ p := Real.rpow_pos_of_pos hKpos p
      have hscaled : K' x < c / 2 * K x ^ p :=
        (div_lt_iff₀ hpowPos).mp hratiox
      have hpowOne : 1 ≤ K x ^ p := Real.one_le_rpow hKx hp
      have hcHalf : c / 2 ≤ 0 := by linarith
      have hmul : c / 2 * K x ^ p ≤ c / 2 := by
        simpa using mul_le_mul_of_nonpos_left hpowOne hcHalf
      exact hscaled.le.trans hmul
    obtain ⟨x1, hx1⟩ := eventually_atTop.1 hupperEvent
    let x2 := max x0 x1
    have hcont2 : ContinuousOn K (Ici x2) :=
      hcont.mono fun x hx => by exact (le_max_left x0 x1).trans hx
    have hderiv2 : ∀ x ∈ Ioi x2, HasDerivAt K (K' x) x := by
      intro x hx
      apply hderiv x
      exact (le_max_left x0 x1).trans_lt hx
    have hupper2 : ∀ x ∈ Ioi x2, K' x ≤ c / 2 := by
      intro x hx
      exact hx1 x ((le_max_right x0 x1).trans hx.le)
    exact False.elim ((not_tendsto_atTop_of_deriv_le_neg (by linarith)
      hcont2 hderiv2 hupper2) hKTop)
  · exact lt_of_le_of_ne (le_of_not_gt hcneg) hc.symm

/-- Full nonzero-coefficient obstruction for a nonnegative-power Strelitz ODE branch. -/
theorem not_tendsto_div_zero_of_nonzero_rpow_normalized_deriv
    {K K' : ℝ → ℝ} {x0 p c : ℝ}
    (hcont : ContinuousOn K (Ici x0))
    (hderiv : ∀ x ∈ Ioi x0, HasDerivAt K (K' x) x)
    (hKTop : Tendsto K atTop atTop)
    (hp : 0 ≤ p) (hc : c ≠ 0)
    (hnormalized : Tendsto (fun x => K' x / K x ^ p) atTop (nhds c)) :
    ¬ Tendsto (fun x => K x / x) atTop (nhds 0) :=
  not_tendsto_div_zero_of_nonnegative_rpow_normalized_deriv
    hcont hderiv hKTop hp
      (positive_limit_of_nonzero_rpow_normalized_deriv
        hcont hderiv hKTop hp hc hnormalized)
      hnormalized

end

end GaloisForLFunctions.HTGeometry
