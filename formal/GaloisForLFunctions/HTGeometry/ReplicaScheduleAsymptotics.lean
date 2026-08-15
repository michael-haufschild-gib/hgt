import GaloisForLFunctions.HTGeometry.ReplicaReporterExpectation

/-!
# Replica schedules and their asymptotic consequences

The exponential replica deficit is driven to any prescribed accuracy by a replica order that grows
only logarithmically in the reciprocal accuracy and inverse-quadratically in the threshold gap.  The
logarithmic schedule at inverse-quadratic accuracy and the schedule for a union of finitely many
observation times are both instances of that single arithmetic.

Because the reporter mean brackets the two threshold probabilities up to the deficit, a schedule
whose deficit vanishes converts a vanishing reporter mean into a vanishing upper-threshold
probability and a vanishing lower-threshold probability into a vanishing reporter mean, for an
arbitrary sequence of underlying probability spaces and score functions.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

section Schedules

/-- The logarithmic schedule at inverse-quadratic accuracy is the prescribed-error schedule. -/
theorem replicaOrderOf_inv_sq {δ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    replicaOrderOf (((n : ℝ) ^ 2)⁻¹) δ = ⌈4 * Real.log n / δ ^ 2⌉₊ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hlog : Real.log (1 / ((n : ℝ) ^ 2)⁻¹) = 2 * Real.log n := by
    rw [one_div, inv_inv, Real.log_pow]
    push_cast
    ring
  rw [replicaOrderOf, hlog]
  congr 1
  ring

/-- **Logarithmic replica schedule.**  Replica order proportional to the logarithm of the index
makes the deficit inverse-quadratic. -/
theorem replicaDeficit_logSchedule_le {a b δ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hδ : 0 < δ)
    (hab : a - b = δ) :
    replicaDeficit ⌈4 * Real.log n / δ ^ 2⌉₊ a b ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hζ0 : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
  have hζ1 : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [hn1]
  rw [← replicaOrderOf_inv_sq (δ := δ) hn]
  exact replicaDeficit_replicaOrderOf_le hζ0 hζ1 hδ hab

/-- **Observation-time schedule.**  A union over finitely many observation times costs only the
logarithm of their number. -/
theorem replicaDeficit_timeSchedule_le {a b δ ζ : ℝ} {N : ℕ} (hN : 1 ≤ N) (hζ0 : 0 < ζ)
    (hζN : ζ ≤ N) (hδ : 0 < δ) (hab : a - b = δ) :
    (N : ℝ) * replicaDeficit (replicaOrderOf (ζ / N) δ) a b ≤ ζ := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hq0 : 0 < ζ / (N : ℝ) := div_pos hζ0 hN0
  have hq1 : ζ / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN0]
    exact hζN
  have h := replicaDeficit_replicaOrderOf_le hq0 hq1 hδ hab
  calc (N : ℝ) * replicaDeficit (replicaOrderOf (ζ / N) δ) a b
      ≤ (N : ℝ) * (ζ / (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt hN0)
    _ = ζ := by field_simp

/-- The observation-time schedule in explicit form. -/
theorem replicaOrderOf_timeSchedule (δ ζ : ℝ) (N : ℕ) :
    replicaOrderOf (ζ / N) δ = ⌈2 * Real.log ((N : ℝ) / ζ) / δ ^ 2⌉₊ := by
  rw [replicaOrderOf, one_div, inv_div]

/-- The logarithmic schedule drives the deficit to zero. -/
theorem tendsto_replicaDeficit_logSchedule {a b δ : ℝ} (hδ : 0 < δ) (hab : a - b = δ) :
    Tendsto (fun n : ℕ => replicaDeficit ⌈4 * Real.log n / δ ^ 2⌉₊ a b) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    hsq.inv_tendsto_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => (replicaDeficit_pos _ a b).le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact replicaDeficit_logSchedule_le hn hδ hab

end Schedules

section Asymptotics

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Vanishing reporter mean forces vanishing incidence.**  Along any schedule whose deficit
vanishes, a vanishing bounded-replica reporter mean forces the upper-threshold probability to
vanish, for an arbitrary sequence of probability spaces and scores. -/
theorem tendsto_measure_of_tendsto_integral (ν : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (ν n)] (Y : ∀ n, Ω n → ℝ) (hY : ∀ n, Measurable (Y n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (hY1 : ∀ n ω, Y n ω ≤ 1) {a b : ℝ} (hb : 0 < b) (hba : b < a)
    (ha : a < 1) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => replicaDeficit (r n) a b) atTop (𝓝 0))
    (hE : Tendsto (fun n => ∫ ω, binomialTail (r n) (replicaThreshold (r n) a b) (Y n ω) ∂ν n)
      atTop (𝓝 0)) :
    Tendsto (fun n => ((ν n) {ω | a ≤ Y n ω}).toReal) atTop (𝓝 0) := by
  have hP1 : ∀ n, ((ν n) {ω | a ≤ Y n ω}).toReal ≤ 1 := by
    intro n
    have h := prob_le_one (μ := ν n) (s := {ω | a ≤ Y n ω})
    have := ENNReal.toReal_mono ENNReal.one_ne_top h
    simpa using this
  have hP0 : ∀ n, 0 ≤ ((ν n) {ω | a ≤ Y n ω}).toReal := fun n => ENNReal.toReal_nonneg
  have hbound : ∀ n, ((ν n) {ω | a ≤ Y n ω}).toReal ≤
      (∫ ω, binomialTail (r n) (replicaThreshold (r n) a b) (Y n ω) ∂ν n) +
        replicaDeficit (r n) a b := by
    intro n
    have hmain := replicaDeficit_mul_measure_le_integral (ν n) (hY n) (hY0 n) (hY1 n)
      (r := r n) hb hba ha
    have hd0 : 0 < replicaDeficit (r n) a b := replicaDeficit_pos _ a b
    nlinarith [hmain, hP1 n, hP0 n, hd0]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hE.add hr) (Eventually.of_forall hP0) (Eventually.of_forall hbound)

/-- **Vanishing incidence forces vanishing reporter mean.**  Along any schedule whose deficit
vanishes, a vanishing lower-threshold probability forces the bounded-replica reporter mean to
vanish. -/
theorem tendsto_integral_of_tendsto_measure (ν : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (ν n)] (Y : ∀ n, Ω n → ℝ) (hY : ∀ n, Measurable (Y n))
    (hY0 : ∀ n ω, 0 ≤ Y n ω) (hY1 : ∀ n ω, Y n ω ≤ 1) {a b : ℝ} (hba : b < a) (ha : a < 1)
    (r : ℕ → ℕ) (hr : Tendsto (fun n => replicaDeficit (r n) a b) atTop (𝓝 0))
    (hQ : Tendsto (fun n => ((ν n) {ω | b ≤ Y n ω}).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, binomialTail (r n) (replicaThreshold (r n) a b) (Y n ω) ∂ν n)
      atTop (𝓝 0) := by
  have hE0 : ∀ n, 0 ≤ ∫ ω, binomialTail (r n) (replicaThreshold (r n) a b) (Y n ω) ∂ν n := by
    intro n
    refine integral_nonneg fun ω => ?_
    exact binomialTail_nonneg (hY0 n ω) (hY1 n ω) _ _
  have hbound : ∀ n, (∫ ω, binomialTail (r n) (replicaThreshold (r n) a b) (Y n ω) ∂ν n) ≤
      ((ν n) {ω | b ≤ Y n ω}).toReal + replicaDeficit (r n) a b := fun n =>
    integral_le_measure_add_replicaDeficit (ν n) (hY n) (hY0 n) (hY1 n) (r := r n) hba ha
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hQ.add hr) (Eventually.of_forall hE0) (Eventually.of_forall hbound)

end Asymptotics

end GaloisForLFunctions.HTGeometry
