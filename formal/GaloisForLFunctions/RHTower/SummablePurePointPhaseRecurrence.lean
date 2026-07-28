import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence

/-!
# Summable pure-point phase recurrence

Every nonnegative summable countable phase energy returns below every
positive resolution.  The quantitative theorem isolates a finite head,
synchronizes it by simultaneous approximation, and pays four times the
remaining summable tail.
-/

open scoped BigOperators Topology

noncomputable section

namespace RHTower

/-- Total recurrence energy of a countable pure-point phase packet. -/
def summablePhaseEnergy
    (a omega : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' p, a p *
    ‖Complex.exp
      (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1‖ ^ 2

private theorem phaseChord_le_two (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤ 2 := by
  calc
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤
        ‖Complex.exp (Complex.I * (x : ℂ))‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by
      rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I]
      norm_num

private theorem summable_phaseEnergy_term
    (a omega : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hsum : Summable a) (n : ℕ) :
    Summable (fun p => a p *
      ‖Complex.exp
        (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
      (fun p => mul_nonneg (ha p) (sq_nonneg _))
      (fun p => ?_) (hsum.mul_left 4)
  have hchord := phaseChord_le_two ((n : ℝ) * omega p)
  have hsq :
      ‖Complex.exp
        (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg
      (Complex.exp
        (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (ha p)

/-- Explicit head--tail recurrence bound.  The first `M` frequencies pay
the finite synchronization factor; every remaining unit-circle chord is
bounded by two. -/
theorem exists_summablePhaseEnergy_recurrence_quantitative
    (a omega : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hsum : Summable a) (M Q : ℕ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ M ∧
      summablePhaseEnergy a omega n ≤
        (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            ∑ p ∈ Finset.range M, a p +
          4 * ∑' p : {p : ℕ // p ∉ Finset.range M}, a p := by
  let omegaHead : Fin M → ℝ := fun p => omega p
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_quantitative
      (Q := Q) omegaHead
  refine ⟨n, hn, hnQ, ?_⟩
  let f : ℕ → ℝ := fun p => a p *
    ‖Complex.exp
      (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1‖ ^ 2
  have hf : Summable f := by
    simpa only [f] using summable_phaseEnergy_term a omega ha hsum n
  have hhead :
      ∑ p ∈ Finset.range M, f p ≤
        (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
          ∑ p ∈ Finset.range M, a p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    let i : Fin M := ⟨p, Finset.mem_range.mp hp⟩
    have hchord :=
      norm_exp_I_mul_real_sub_one_le_mod_two_pi
        ((n : ℝ) * omega p) (r i)
    have hphase :
        ‖Complex.exp
            (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1‖ ≤
          2 * Real.pi / (Q + 1 : ℝ) :=
      hchord.trans (by simpa only [omegaHead, i] using hr i)
    have hdelta : 0 ≤ 2 * Real.pi / (Q + 1 : ℝ) := by positivity
    have hsq := (sq_le_sq₀ (norm_nonneg _) hdelta).2 hphase
    dsimp only [f]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (ha p)
  have htail :
      ∑' p : {p : ℕ // p ∉ Finset.range M}, f p ≤
        4 * ∑' p : {p : ℕ // p ∉ Finset.range M}, a p := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum
      (fun p => by
        have hchord := phaseChord_le_two ((n : ℝ) * omega p)
        have hsq :
            ‖Complex.exp
              (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1‖ ^ 2 ≤ 4 := by
          nlinarith [norm_nonneg
            (Complex.exp
              (Complex.I * ((((n : ℝ) * omega p : ℝ) : ℂ))) - 1)]
        dsimp only [f]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsq (ha p))
      (hf.subtype _)
      ((hsum.subtype _).mul_left 4)
  have hsplit :=
    hf.sum_add_tsum_subtype_compl (Finset.range M)
  rw [summablePhaseEnergy]
  change ∑' p, f p ≤ _
  rw [← hsplit]
  exact add_le_add hhead htail

private theorem exists_tsum_subtype_compl_range_lt
    (a : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p) (hsum : Summable a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ,
      ∑' p : {p : ℕ // p ∉ Finset.range M}, a p < ε := by
  have htend := hsum.hasSum.tendsto_sum_nat
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨M, hM⟩ := htend ε hε
  refine ⟨M, ?_⟩
  have hdist := hM M le_rfl
  rw [Real.dist_eq] at hdist
  have hle :
      ∑ p ∈ Finset.range M, a p ≤ ∑' p, a p :=
    hsum.sum_le_tsum (Finset.range M)
      (fun p _hp => ha p)
  have hsplit :=
    hsum.sum_add_tsum_subtype_compl (Finset.range M)
  have habs :
      |(∑ p ∈ Finset.range M, a p) - ∑' p, a p| =
        ∑' p : {p : ℕ // p ∉ Finset.range M}, a p := by
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  rw [← habs]
  exact hdist

private theorem exists_phaseResolution_head_lt
    (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ Q : ℕ, (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 * A < ε := by
  by_cases hAzero : A = 0
  · exact ⟨0, by simp [hAzero, hε]⟩
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
  let c : ℝ := Real.sqrt (ε / A) / (2 * Real.pi)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  obtain ⟨Q, hQ⟩ := exists_nat_one_div_lt hc
  refine ⟨Q, ?_⟩
  let δ : ℝ := 2 * Real.pi / (Q + 1 : ℝ)
  have hδ : δ < Real.sqrt (ε / A) := by
    have hscale :=
      mul_lt_mul_of_pos_left hQ (mul_pos two_pos Real.pi_pos)
    calc
      δ = (2 * Real.pi) * (1 / ((Q : ℝ) + 1)) := by
        dsimp only [δ]
        ring
      _ < (2 * Real.pi) * c := hscale
      _ = Real.sqrt (ε / A) := by
        dsimp only [c]
        field_simp [Real.pi_ne_zero]
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hsqrt0 : 0 ≤ Real.sqrt (ε / A) := Real.sqrt_nonneg _
  have hδsq :
      δ ^ 2 < (Real.sqrt (ε / A)) ^ 2 :=
    (sq_lt_sq₀ hδ0 hsqrt0).2 hδ
  calc
    (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 * A =
        δ ^ 2 * A := rfl
    _ < (Real.sqrt (ε / A)) ^ 2 * A :=
      mul_lt_mul_of_pos_right hδsq hApos
    _ = (ε / A) * A := by
      rw [Real.sq_sqrt (div_nonneg hε.le hA)]
    _ = ε := by field_simp [hAzero]

/-- Every nonnegative summable countable phase packet returns at every
positive resolution. -/
theorem exists_summablePhaseEnergy_recurrence
    (a omega : ℕ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hsum : Summable a) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ summablePhaseEnergy a omega n < ε := by
  obtain ⟨M, htail⟩ :=
    exists_tsum_subtype_compl_range_lt a ha hsum
      (show 0 < ε / 8 by positivity)
  have hhead0 : 0 ≤ ∑ p ∈ Finset.range M, a p :=
    Finset.sum_nonneg fun p _hp => ha p
  obtain ⟨Q, hhead⟩ :=
    exists_phaseResolution_head_lt
      (∑ p ∈ Finset.range M, a p) (ε / 2)
      hhead0 (show 0 < ε / 2 by positivity)
  obtain ⟨n, hn, _hnQ, henergy⟩ :=
    exists_summablePhaseEnergy_recurrence_quantitative
      a omega ha hsum M Q
  refine ⟨n, hn, ?_⟩
  calc
    summablePhaseEnergy a omega n ≤
        (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            ∑ p ∈ Finset.range M, a p +
          4 * ∑' p : {p : ℕ // p ∉ Finset.range M}, a p :=
      henergy
    _ < ε := by linarith

end RHTower
