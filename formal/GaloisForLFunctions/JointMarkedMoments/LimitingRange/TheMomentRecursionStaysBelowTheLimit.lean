import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheLimitingImprovement

/-!
# The moment recursion stays below the limiting improvement

A stage `R ↦ r < R` of the joint moment recursion with cutoff `k` propagates the marked-length
improvement `z` to `Y(r) = (r/R) z + (1/k − 2)u`, `u = (1 − r/R)/6` (eq. (3)). Its large-value
condition with cutoff length `w ≥ R` is `5/6 − (5/4 − 3k/2)w − k(1 + R)/2 − kz ≥ 0`.

* `propagatedImprovement_thresholdCutoff`: at the threshold cutoff
  `k∗(R, z) = (5R/4 − 5/6)/(R − 1/2 − z)` the propagation is the Euler step
  `z + (r − R)((45R − 24)z + 9R − 7)/(R(45R − 30))` of the slope field of `G`.
* `propagatedImprovement_le_limitImprovement` (Proposition 6.2): if `z ≤ G(R)` then
  `Y(r) ≤ G(r)`. The large-value condition forces `k ≥ k∗`, `Y` decreases in `k`, the Euler
  step increases in `z`, and `G` lies above its tangent lines.
* `chain_le_limitImprovement`: every finite descending chain started below `G` stays below `G`.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Real Set

noncomputable section

/-- The propagated improvement `Y(r) = (r/R) z + (1/k − 2)(1 − r/R)/6`. -/
def propagatedImprovement (R r z k : ℝ) : ℝ := r / R * z + (1 / k - 2) * ((1 - r / R) / 6)

/-- The threshold cutoff `k∗(R, z) = (5R/4 − 5/6)/(R − 1/2 − z)`. -/
def thresholdCutoff (R z : ℝ) : ℝ := (5 * R / 4 - 5 / 6) / (R - 1 / 2 - z)

/-- At the threshold cutoff the propagation is the Euler step of the slope field. -/
theorem propagatedImprovement_thresholdCutoff {R r z : ℝ} (hR : 2 / 3 < R) (hz : z < R - 1 / 2) :
    propagatedImprovement R r z (thresholdCutoff R z) = z + (r - R) * recursionSlope R z := by
  have hR0 : R ≠ 0 := by linarith
  have hc : 5 * R / 4 - 5 / 6 ≠ 0 := by linarith
  have hU : 45 * R - 30 ≠ 0 := by linarith
  have hD : R - 1 / 2 - z ≠ 0 := by linarith
  unfold propagatedImprovement thresholdCutoff recursionSlope
  generalize hc' : 5 * R / 4 - 5 / 6 = c at hc ⊢
  generalize hU' : 45 * R - 30 = U at hU ⊢
  generalize hD' : R - 1 / 2 - z = D at hD ⊢
  field_simp
  rw [← hc', ← hU', ← hD']
  ring

/-- Proposition 6.2: one stage of the recursion keeps the improvement below `G`. -/
theorem propagatedImprovement_le_limitImprovement {R r z k w : ℝ} (hr : 2 / 3 ≤ r)
    (hrR : r < R) (hk : 0 < k) (hk' : k ≤ 5 / 6) (hw : R ≤ w)
    (hstage : 0 ≤ 5 / 6 - (5 / 4 - 3 * k / 2) * w - k * (1 + R) / 2 - k * z)
    (hz : z ≤ limitImprovement R) :
    propagatedImprovement R r z k ≤ limitImprovement r := by
  have hR : 2 / 3 < R := lt_of_le_of_lt hr hrR
  have hR0 : 0 < R := by linarith
  have hc : 0 < 5 * R / 4 - 5 / 6 := by linarith
  have hA : 0 ≤ 5 / 4 - 3 * k / 2 := by linarith
  -- replacing `w` by `R` gives `k (R − 1/2 − z) ≥ 5R/4 − 5/6 > 0`
  have hkD : 5 * R / 4 - 5 / 6 ≤ k * (R - 1 / 2 - z) := by
    nlinarith [mul_nonneg hA (sub_nonneg.2 hw)]
  have hD : 0 < R - 1 / 2 - z := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hk.le h]
  -- hence `k ≥ k∗`, and the propagation decreases in `k`
  have hinv : 1 / k ≤ 1 / thresholdCutoff R z := by
    unfold thresholdCutoff
    rw [one_div_div, div_le_div_iff₀ hk hc]
    linarith
  have hu : 0 ≤ (1 - r / R) / 6 := by
    have : r / R < 1 := (div_lt_one hR0).2 hrR
    linarith
  have hmono : propagatedImprovement R r z k ≤
      propagatedImprovement R r z (thresholdCutoff R z) := by
    unfold propagatedImprovement
    nlinarith [mul_le_mul_of_nonneg_right (sub_le_sub_right hinv 2) hu]
  rw [propagatedImprovement_thresholdCutoff hR (by linarith)] at hmono
  -- the Euler step increases in `z`
  have hzmono : z + (r - R) * recursionSlope R z ≤
      limitImprovement R + (r - R) * recursionSlope R (limitImprovement R) := by
    have hU : 0 < 45 * R - 30 := by linarith
    have key : (limitImprovement R + (r - R) * recursionSlope R (limitImprovement R)) -
        (z + (r - R) * recursionSlope R z) =
        (limitImprovement R - z) * ((r * (45 * R - 24) - 6 * R) / (R * (45 * R - 30))) := by
      unfold recursionSlope
      have hR0' : R ≠ 0 := hR0.ne'
      generalize limitImprovement R = g
      generalize hU' : 45 * R - 30 = U at hU ⊢
      have : U ≠ 0 := hU.ne'
      field_simp
      rw [← hU']
      ring
    have hnum : 0 ≤ r * (45 * R - 24) - 6 * R := by
      nlinarith [mul_le_mul_of_nonneg_right hr (by linarith : (0 : ℝ) ≤ 45 * R - 24)]
    have hfac : 0 ≤ (r * (45 * R - 24) - 6 * R) / (R * (45 * R - 30)) :=
      div_nonneg hnum (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hz) hfac]
  rw [← limitSlope_eq_recursionSlope hR] at hzmono
  have htan := limitImprovement_tangent_le hR hr
  linarith

/-- A finite descending chain started below `G` stays below `G` at every stage. -/
theorem chain_le_limitImprovement {n : ℕ} {R z k w : ℕ → ℝ}
    (hlow : ∀ j ≤ n, 2 / 3 ≤ R j) (hdesc : ∀ j < n, R (j + 1) < R j)
    (hk : ∀ j < n, 0 < k j ∧ k j ≤ 5 / 6) (hw : ∀ j < n, R j ≤ w j)
    (hstage : ∀ j < n,
      0 ≤ 5 / 6 - (5 / 4 - 3 * k j / 2) * w j - k j * (1 + R j) / 2 - k j * z j)
    (hstep : ∀ j < n, z (j + 1) ≤ propagatedImprovement (R j) (R (j + 1)) (z j) (k j))
    (h0 : z 0 ≤ limitImprovement (R 0)) :
    ∀ j ≤ n, z j ≤ limitImprovement (R j) := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    have hjn : j < n := Nat.lt_of_succ_le hj
    exact (hstep j hjn).trans (propagatedImprovement_le_limitImprovement (hlow (j + 1) hj)
      (hdesc j hjn) (hk j hjn).1 (hk j hjn).2 (hw j hjn) (hstage j hjn) (ih hjn.le))

end

end GaloisForLFunctions.JointMarkedMoments
