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
  apply h.congr_deriv
  change Real.exp (-t) * (-1) * (a-b) = b - (b + Real.exp (-t)*(a-b))
  ring

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
  have hs : Real.exp t ≤ 1 + (a : ℝ)/d ↔ Real.exp t-1 ≤ (a : ℝ)/d := by
    constructor <;> intro h <;> linarith only [h]
  rw [hs, le_div_iff₀ hd]
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

/-- A segment records its duration and attracting target. -/
abbrev Segment := NNReal × ℝ

/-- Final slack after a finite schedule of target switches. -/
def endpoint (a : ℝ) (L : List Segment) : ℝ :=
  L.foldl (fun x p => slack x p.2 p.1) a

/-- The full duration determines how much of any initial offset survives. -/
theorem endpoint_difference (a b : ℝ) (L : List Segment) :
    endpoint a L - endpoint b L = Real.exp (-((L.map fun p => (p.1 : ℝ)).sum))*(a-b) := by
  induction L generalizing a b with
  | nil => simp [endpoint]
  | cons p L ih =>
    change endpoint (slack a p.2 p.1) L - endpoint (slack b p.2 p.1) L = _
    rw [ih]
    simp only [List.map_cons,List.sum_cons,neg_add,Real.exp_add,slack]
    ring

/-- Interchanging adjacent targets has a signed effect independent of the starting slack. -/
theorem interchange (a b c s t : ℝ) :
    slack (slack a b t) c s - slack (slack a c s) b t =
      (1-Real.exp (-t))*(1-Real.exp (-s))*(c-b) := by unfold slack; ring

/-- With both durations positive, sorting adjacent targets increasingly improves
the final slack of a schedule precisely when those targets were out of order. -/
theorem interchange_order (a b c : ℝ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (L : List Segment) :
    endpoint (slack (slack a c s) b t) L ≤ endpoint (slack (slack a b t) c s) L ↔ b ≤ c := by
  rw [← sub_nonneg,endpoint_difference,interchange,mul_nonneg_iff_of_pos_left (Real.exp_pos _)]
  have ht' := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hs' := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs))
  rw [mul_nonneg_iff_of_pos_left (mul_pos ht' hs'),sub_nonneg]

/-- Safety along all continuous pieces of a switched schedule. -/
def safeAlong (a : ℝ) : List Segment → Prop
  | [] => 0 ≤ a
  | (t,b) :: L => (∀ s ∈ Icc 0 (t : ℝ), 0 ≤ slack a b s) ∧ safeAlong (slack a b t) L

/-- Checking only segment endpoints suffices even when individual targets are exterior. -/
theorem switched_safe_iff (a : ℝ) (L : List Segment) :
    safeAlong a L ↔ ∀ P Q : List Segment, L = P ++ Q → 0 ≤ endpoint a P := by
  induction L generalizing a with
  | nil =>
    constructor
    · rintro ha P Q h
      obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp h.symm
      exact ha
    · intro h
      exact h [] [] rfl
  | cons p L ih =>
    rcases p with ⟨t,b⟩
    rw [safeAlong,window_safe_iff a b 0 t t.property,slack_zero,ih]
    constructor
    · rintro ⟨⟨ha,_⟩,hs⟩ P Q he
      cases P with
      | nil => exact ha
      | cons p P =>
        obtain ⟨rfl,h⟩ := List.cons.inj he
        exact hs P Q h
    · intro H
      have hs (P Q : List Segment) (h : L = P ++ Q) :
          0 ≤ endpoint (slack a b t) P :=
        H ((t,b)::P) Q (congrArg (List.cons (t,b)) h)
      exact ⟨⟨H [] _ rfl,hs [] L rfl⟩,hs⟩

/-- The unique periodic initial slack for a positive-duration cycle. -/
def periodicSlack (L : List Segment) : ℝ :=
  endpoint 0 L / (1-Real.exp (-((L.map fun p => (p.1 : ℝ)).sum)))

theorem periodic_iff (a : ℝ) (L : List Segment) (hL : 0 < (L.map fun p => (p.1 : ℝ)).sum) :
    endpoint a L = a ↔ a = periodicSlack L := by
  have hd := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL))
  have h := endpoint_difference a 0 L
  rw [periodicSlack,eq_div_iff hd.ne']
  constructor <;> intro he <;> linarith only [h,he]

/-- At homologous phases of successive cycles, offsets from the periodic orbit
are attenuated by the exponential of the total elapsed time. -/
theorem after_cycles (a : ℝ) (L : List Segment) (n : ℕ)
    (hL : 0 < (L.map fun p => (p.1 : ℝ)).sum) :
    (fun x => endpoint x L)^[n] a - periodicSlack L =
      Real.exp (-((L.map fun p => (p.1 : ℝ)).sum))^n*(a-periodicSlack L) := by
  have hf := (periodic_iff (periodicSlack L) L hL).2 rfl
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := endpoint_difference ((fun x => endpoint x L)^[n] a) (periodicSlack L) L
    rw [hf,ih] at h
    rw [h,pow_succ]
    ring

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
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.endpoint_difference
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.interchange
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.interchange_order
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.switched_safe_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.periodic_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.after_cycles
