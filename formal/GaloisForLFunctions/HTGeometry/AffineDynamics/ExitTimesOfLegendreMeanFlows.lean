import GaloisForLFunctions.HTGeometry.LegendreResidualTransduction

/-!
# Affine barriers on Legendre mean flows

The comparison argument in Theorem 1 of Singh and Vaughan (arXiv:2610.15936)
controls the slack of each face of a feasible region. On a Legendre mean
flow the slack can be solved exactly. The target determines infinite-horizon
viability, while the initial margin determines the first exit time.
-/

noncomputable section
open Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.AffineDynamics

/-- Slack with initial value a and attracting value b in unit-rate time. -/
def slack (a b t : ℝ) : ℝ := b + Real.exp (-t) * (a-b)

private theorem slack_zero (a b : ℝ) : slack a b 0 = a := by simp [slack]

/-- Sampling any two successive time windows gives the same slack as their union. -/
theorem slack_restart (a b t s : ℝ) : slack (slack a b t) b s = slack a b (t+s) := by
  simp only [slack, neg_add, Real.exp_add]
  ring

theorem slack_derivative (a b t : ℝ) : HasDerivAt (slack a b) (b - slack a b t) t := by
  have h := ((((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).mul_const (a-b)).const_add b)
  unfold slack
  convert h using 1 <;> ring

private theorem slack_limit (a b : ℝ) : Tendsto (slack a b) atTop (𝓝 b) := by
  unfold slack
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (a-b)).const_add b

/-- For every strictly positive time, the paper's exponential lower bound is
equivalent to the target lying on the safe side of the face. -/
theorem comparison_iff (a b t : ℝ) (ht : 0 < t) :
    Real.exp (-t) * a ≤ slack a b t ↔ 0 ≤ b := by
  have hw : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  rw [← sub_nonneg, show slack a b t - Real.exp (-t)*a = (1-Real.exp (-t))*b by
    unfold slack; ring]
  exact mul_nonneg_iff_of_pos_left hw

/-- All intermediate slacks lie between the slacks at the two ends of a time window. -/
theorem slack_window (a b s t u : ℝ) (hs : s ≤ t) (hu : t ≤ u) :
    slack a b t ∈ Icc (min (slack a b s) (slack a b u)) (max (slack a b s) (slack a b u)) := by
  have hst := Real.exp_le_exp.mpr (neg_le_neg hs)
  have htu := Real.exp_le_exp.mpr (neg_le_neg hu)
  by_cases hab : 0 ≤ a-b
  · exact ⟨(min_le_right _ _).trans (add_le_add_right
      (mul_le_mul_of_nonneg_right htu hab) _),
      (add_le_add_right (mul_le_mul_of_nonneg_right hst hab) _).trans (le_max_left _ _)⟩
  · have hh := le_of_not_ge hab
    exact ⟨(min_le_left _ _).trans (add_le_add_right
      (mul_le_mul_of_nonpos_right hst hh) _),
      (add_le_add_right (mul_le_mul_of_nonpos_right htu hh) _).trans (le_max_right _ _)⟩

/-- A whole finite window is safe exactly when its two endpoints are safe. -/
theorem window_safe_iff (a b s u : ℝ) (h : s ≤ u) :
    (∀ t ∈ Icc s u, 0 ≤ slack a b t) ↔ 0 ≤ slack a b s ∧ 0 ≤ slack a b u := by
  constructor
  · intro H
    exact ⟨H _ ⟨le_rfl,h⟩,H _ ⟨h,le_rfl⟩⟩
  · rintro ⟨hs,hu⟩ t ⟨hst,htu⟩
    exact (le_min hs hu).trans (slack_window a b s t u hst htu).1

/-- The exact viability test on an infinite horizon recovers both endpoint conditions. -/
theorem forever_safe_iff (a b : ℝ) :
    (∀ t : ℝ, 0 ≤ t → 0 ≤ slack a b t) ↔ 0 ≤ a ∧ 0 ≤ b := by
  constructor
  · intro H
    refine ⟨by simpa [slack_zero] using H 0 le_rfl, ?_⟩
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (slack_limit a b)
      ((eventually_ge_atTop (0 : ℝ)).mono H)
  · rintro ⟨ha,hb⟩ t ht
    rcases eq_or_lt_of_le ht with h | h
    · simpa [← h, slack_zero] using ha
    · exact (mul_nonneg (Real.exp_pos _).le ha).trans ((comparison_iff a b t h).2 hb)

/-- Clearing the positive integrating factor converts slack into an affine function of exp t. -/
theorem scaled_slack (a b t : ℝ) : Real.exp t * slack a b t = a + (Real.exp t - 1)*b := by
  unfold slack
  rw [Real.exp_neg]
  field_simp
  ring

/-- An exterior target at distance d produces one exact last safe time. -/
theorem last_safe_time (a : NNReal) (d t : ℝ) (hd : 0 < d) :
    0 ≤ slack a (-d) t ↔ t ≤ Real.log (1 + (a : ℝ)/d) := by
  have hd' : 0 < 1 + (a : ℝ)/d := by positivity
  rw [← mul_nonneg_iff_of_pos_left (Real.exp_pos t), scaled_slack,
    ← Real.exp_le_exp (x := t) (y := Real.log (1+(a : ℝ)/d)), Real.exp_log hd']
  rw [← sub_le_iff_le_add', le_div_iff₀ hd]
  constructor <;> intro h <;> linarith only [h]

/-- Exact feasible target half-line for a prescribed positive horizon. -/
theorem finite_target_threshold (a b T : ℝ) (hT : 0 < T) :
    (∀ t ∈ Icc 0 T, 0 ≤ slack a b t) ↔
      0 ≤ a ∧ -a / (Real.exp T - 1) ≤ b := by
  rw [window_safe_iff a b 0 T hT.le, slack_zero]
  apply and_congr_right
  intro _
  rw [div_le_iff₀ (sub_pos.mpr (Real.one_lt_exp_iff.mpr hT)),
    ← mul_nonneg_iff_of_pos_left (Real.exp_pos T), scaled_slack]
  constructor <;> intro h <;> linarith only [h]

open ResidualTransduction
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- An affine face on the actual mean trajectory has the scalar slack above. -/
theorem mean_face (C : LegendreChart Θ) (m : Θ →L[ℝ] ℝ) (x v : Θ) (B t : ℝ) :
    B - C.flowMean m x t v = slack (B - C.μ x v) (B - m v) t := by
  change B - (m v + Real.exp (-t) * (C.μ x v - m v)) = _
  unfold slack
  ring

/-- A possibly infinite intersection of affine half-spaces is viable along the
mean trajectory exactly when it contains the initial reporter and target. -/
theorem mean_polyhedron (C : LegendreChart Θ) (m : Θ →L[ℝ] ℝ) (x : Θ)
    {ι : Type*} (v : ι → Θ) (B : ι → ℝ) :
    (∀ t : ℝ, 0 ≤ t → ∀ i, C.flowMean m x t (v i) ≤ B i) ↔
      (∀ i, C.μ x (v i) ≤ B i) ∧ (∀ i, m (v i) ≤ B i) := by
  have h (i : ι) : (∀ t : ℝ, 0 ≤ t → C.flowMean m x t (v i) ≤ B i) ↔
      C.μ x (v i) ≤ B i ∧ m (v i) ≤ B i := by
    have eq := forever_safe_iff (B i - C.μ x (v i)) (B i - m (v i))
    simp only [← mean_face,sub_nonneg] at eq
    exact eq
  exact ⟨fun H => ⟨fun i => ((h i).mp (fun t ht => H t ht i)).1,
    fun i => ((h i).mp (fun t ht => H t ht i)).2⟩,
    fun ⟨L,R⟩ t ht i => (h i).mpr ⟨L i,R i⟩ t ht⟩

end GaloisForLFunctions.HTGeometry.AffineDynamics

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.slack_restart
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.slack_derivative
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.comparison_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.slack_window
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.window_safe_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.forever_safe_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.scaled_slack
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.last_safe_time
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.finite_target_threshold
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.mean_face
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.mean_polyhedron
