import GaloisForLFunctions.RHTower.SummablePurePointPhaseRecurrence

/-!
# Countable pure-point projective survival escape--return law

For every normalized nonnegative summable spectral packet, a finite head of
`M` modes can be synchronized projectively with only `M - 1` independent
frequency gaps.  The unsynchronized countable complement enters through its
exact summable spectral tail.

The resulting survival-probability loss has a quadratic phase-resolution
remainder.  Thus the law applies to genuinely countably infinite pure-point
spectra without truncating the state or assuming finite spectral support.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Unitary phase of the `k`-th pure-point spectral mode at time `t`. -/
def summablePurePointSurvivalPhase
    (omega : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℂ :=
  Complex.exp (Complex.I * (((t * omega k : ℝ) : ℂ)))

/-- Survival amplitude of a normalized countable pure-point spectral packet. -/
def summablePurePointSurvivalAmplitude
    (p omega : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' k, (p k : ℂ) * summablePurePointSurvivalPhase omega t k

/-- Survival probability of a normalized countable pure-point spectral packet. -/
def summablePurePointSurvivalProbability
    (p omega : ℕ → ℝ) (t : ℝ) : ℝ :=
  Complex.normSq (summablePurePointSurvivalAmplitude p omega t)

/-- Loss of survival probability from its initial value one. -/
def summablePurePointSurvivalDeviation
    (p omega : ℕ → ℝ) (t : ℝ) : ℝ :=
  1 - summablePurePointSurvivalProbability p omega t

/-- Spectral weight outside the first `M` modes. -/
def summablePurePointSurvivalTail
    (p : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑' j, p (M + j)

/--
Projective survival-recurrence budget: quadratic head synchronization plus
the exact countable spectral tail.
-/
def summablePurePointSurvivalRecurrenceBudget
    (p : ℕ → ℝ) (M Q : ℕ) : ℝ :=
  (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
      ∑ k ∈ Finset.range (M - 1), p (k + 1) +
    4 * summablePurePointSurvivalTail p M

/-- Phase relative to the reference mode `0`. -/
private def summablePurePointProjectivePhase
    (omega : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℂ :=
  Complex.exp
    (Complex.I * (((t * (omega k - omega 0) : ℝ) : ℂ)))

/-- Projectively dephased survival amplitude. -/
private def summablePurePointProjectiveAmplitude
    (p omega : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' k, (p k : ℂ) * summablePurePointProjectivePhase omega t k

private theorem summablePurePointSurvivalPhase_norm
    (omega : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    ‖summablePurePointSurvivalPhase omega t k‖ = 1 := by
  rw [summablePurePointSurvivalPhase,
    show Complex.I * (((t * omega k : ℝ) : ℂ)) =
      ((t * omega k : ℝ) : ℂ) * Complex.I by ring,
    Complex.norm_exp_ofReal_mul_I]

private theorem summablePurePointProjectivePhase_norm
    (omega : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    ‖summablePurePointProjectivePhase omega t k‖ = 1 := by
  rw [summablePurePointProjectivePhase,
    show Complex.I * (((t * (omega k - omega 0) : ℝ) : ℂ)) =
      ((t * (omega k - omega 0) : ℝ) : ℂ) * Complex.I by ring,
    Complex.norm_exp_ofReal_mul_I]

private theorem summable_survivalAmplitude_term
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (t : ℝ) :
    Summable
      (fun k => (p k : ℂ) * summablePurePointSurvivalPhase omega t k) := by
  apply Summable.of_norm
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hp _), summablePurePointSurvivalPhase_norm, mul_one]
    using hsum

private theorem summable_projectiveAmplitude_term
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (t : ℝ) :
    Summable
      (fun k => (p k : ℂ) * summablePurePointProjectivePhase omega t k) := by
  apply Summable.of_norm
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hp _), summablePurePointProjectivePhase_norm, mul_one]
    using hsum

private theorem summablePurePointSurvivalAmplitude_norm_le_one
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1) (t : ℝ) :
    ‖summablePurePointSurvivalAmplitude p omega t‖ ≤ 1 := by
  rw [summablePurePointSurvivalAmplitude]
  calc
    ‖∑' k, (p k : ℂ) * summablePurePointSurvivalPhase omega t k‖ ≤
        ∑' k, ‖(p k : ℂ) *
          summablePurePointSurvivalPhase omega t k‖ :=
      norm_tsum_le_tsum_norm
        (summable_survivalAmplitude_term p omega hp hsum t).norm
    _ = ∑' k, p k := by
      apply tsum_congr
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp k), summablePurePointSurvivalPhase_norm, mul_one]
    _ = 1 := htotal

private theorem summablePurePointProjectiveAmplitude_norm_le_one
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1) (t : ℝ) :
    ‖summablePurePointProjectiveAmplitude p omega t‖ ≤ 1 := by
  rw [summablePurePointProjectiveAmplitude]
  calc
    ‖∑' k, (p k : ℂ) * summablePurePointProjectivePhase omega t k‖ ≤
        ∑' k, ‖(p k : ℂ) *
          summablePurePointProjectivePhase omega t k‖ :=
      norm_tsum_le_tsum_norm
        (summable_projectiveAmplitude_term p omega hp hsum t).norm
    _ = ∑' k, p k := by
      apply tsum_congr
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp k), summablePurePointProjectivePhase_norm, mul_one]
    _ = 1 := htotal

/-- Normalized nonnegative countable pure-point packets have survival
probability at most one. -/
theorem summablePurePointSurvivalProbability_le_one
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1) (t : ℝ) :
    summablePurePointSurvivalProbability p omega t ≤ 1 := by
  rw [summablePurePointSurvivalProbability, Complex.normSq_eq_norm_sq]
  have hnorm :=
    summablePurePointSurvivalAmplitude_norm_le_one
      p omega hp hsum htotal t
  nlinarith [norm_nonneg
    (summablePurePointSurvivalAmplitude p omega t)]

/-- Survival loss is nonnegative for every normalized nonnegative packet. -/
theorem summablePurePointSurvivalDeviation_nonneg
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1) (t : ℝ) :
    0 ≤ summablePurePointSurvivalDeviation p omega t := by
  unfold summablePurePointSurvivalDeviation
  exact sub_nonneg.mpr
    (summablePurePointSurvivalProbability_le_one
      p omega hp hsum htotal t)

private theorem summablePurePointSurvivalPhase_eq_reference_mul_projective
    (omega : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    summablePurePointSurvivalPhase omega t k =
      summablePurePointSurvivalPhase omega t 0 *
        summablePurePointProjectivePhase omega t k := by
  unfold summablePurePointSurvivalPhase
    summablePurePointProjectivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem summablePurePointSurvivalAmplitude_eq_reference_mul_projective
    (p omega : ℕ → ℝ) (t : ℝ) :
    summablePurePointSurvivalAmplitude p omega t =
      summablePurePointSurvivalPhase omega t 0 *
        summablePurePointProjectiveAmplitude p omega t := by
  unfold summablePurePointSurvivalAmplitude
    summablePurePointProjectiveAmplitude
  calc
    (∑' k, (p k : ℂ) * summablePurePointSurvivalPhase omega t k) =
        ∑' k, summablePurePointSurvivalPhase omega t 0 *
          ((p k : ℂ) * summablePurePointProjectivePhase omega t k) := by
      apply tsum_congr
      intro k
      rw [summablePurePointSurvivalPhase_eq_reference_mul_projective]
      ring
    _ = summablePurePointSurvivalPhase omega t 0 *
        ∑' k, (p k : ℂ) *
          summablePurePointProjectivePhase omega t k := tsum_mul_left

private theorem summablePurePointSurvivalProbability_eq_projective
    (p omega : ℕ → ℝ) (t : ℝ) :
    summablePurePointSurvivalProbability p omega t =
      Complex.normSq
        (summablePurePointProjectiveAmplitude p omega t) := by
  rw [summablePurePointSurvivalProbability,
    summablePurePointSurvivalAmplitude_eq_reference_mul_projective,
    Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    summablePurePointSurvivalPhase_norm]
  norm_num

private theorem projectivePhase_chord_sq
    (omega : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    ‖summablePurePointProjectivePhase omega t k - 1‖ ^ 2 =
      2 - 2 * (summablePurePointProjectivePhase omega t k).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have hnorm :
      (summablePurePointProjectivePhase omega t k).re ^ 2 +
        (summablePurePointProjectivePhase omega t k).im ^ 2 = 1 := by
    simp only [pow_two]
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq,
      summablePurePointProjectivePhase_norm]
    norm_num
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im]
  nlinarith

private theorem summablePurePointSurvivalDeviation_le_projectivePhaseEnergy
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1) (n : ℕ) :
    summablePurePointSurvivalDeviation p omega n ≤
      summablePhaseEnergy
        (fun k => p (k + 1))
        (fun k => omega (k + 1) - omega 0) n := by
  let t : ℝ := n
  let z : ℕ → ℂ :=
    fun k => summablePurePointProjectivePhase omega t k
  let B : ℂ := summablePurePointProjectiveAmplitude p omega t
  let e : ℕ → ℝ := fun k => p k * ‖z k - 1‖ ^ 2
  have hpC :
      Summable (fun k => (p k : ℂ)) :=
    (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable hsum
  have hz :
      Summable (fun k => (p k : ℂ) * z k) := by
    simpa only [z] using
      summable_projectiveAmplitude_term p omega hp hsum t
  have he : Summable e := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (hp k) (sq_nonneg _))
      (fun k => ?_) (hsum.mul_left 4)
    have hchord :
        ‖z k - 1‖ ≤ 2 := by
      calc
        ‖z k - 1‖ ≤ ‖z k‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [show ‖z k‖ = 1 by
            simpa only [z] using
              summablePurePointProjectivePhase_norm omega t k]
          norm_num
    have hsq : ‖z k - 1‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (z k - 1)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hsq (hp k)
  have hBRe :
      B.re = ∑' k, p k * (z k).re := by
    rw [show B = ∑' k, (p k : ℂ) * z k by rfl,
      Complex.re_tsum hz]
    apply tsum_congr
    intro k
    simp
  have hzRe : Summable (fun k => p k * (z k).re) := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      Complex.reCLM.summable hz
  have henergy :
      ∑' k, e k = 2 - 2 * B.re := by
    calc
      ∑' k, e k =
          ∑' k, p k * (2 - 2 * (z k).re) := by
        apply tsum_congr
        intro k
        dsimp only [e]
        rw [projectivePhase_chord_sq]
      _ = ∑' k, (2 * p k - 2 * (p k * (z k).re)) := by
        apply tsum_congr
        intro k
        ring
      _ = (∑' k, 2 * p k) -
          ∑' k, 2 * (p k * (z k).re) := by
        exact
          ((hsum.mul_left 2).tsum_sub
            (hzRe.mul_left 2))
      _ = 2 - 2 * B.re := by
        rw [tsum_mul_left, htotal, hBRe, tsum_mul_left]
        ring
  have hroot : e 0 = 0 := by
    dsimp only [e, z, summablePurePointProjectivePhase]
    norm_num
  have hshift :
      ∑' k, e (k + 1) = ∑' k, e k := by
    have hsplit := he.sum_add_tsum_nat_add 1
    simpa only [Finset.sum_range_one, hroot, zero_add,
      Nat.one_mul, Nat.add_comm] using hsplit
  have hshiftEnergy :
      ∑' k, e (k + 1) =
        summablePhaseEnergy
          (fun k => p (k + 1))
          (fun k => omega (k + 1) - omega 0) n := by
    rw [summablePhaseEnergy]
    apply tsum_congr
    intro k
    dsimp only [e, z, summablePurePointProjectivePhase]
  have hdefect :
      1 - Complex.normSq B ≤ 2 - 2 * B.re := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (B.re - 1), sq_nonneg B.im]
  rw [summablePurePointSurvivalDeviation,
    summablePurePointSurvivalProbability_eq_projective]
  change 1 - Complex.normSq B ≤ _
  rw [← hshiftEnergy, hshift, henergy]
  exact hdefect

private theorem summablePurePointSurvivalTail_eq_shifted_complement
    (p : ℕ → ℝ) (hsum : Summable p) (M : ℕ) (hM : 1 ≤ M) :
    summablePurePointSurvivalTail p M =
      ∑' k : {k : ℕ // k ∉ Finset.range (M - 1)}, p (k + 1) := by
  let pShift : ℕ → ℝ := fun k => p (k + 1)
  have hsumShift : Summable pShift := by
    change Summable (p ∘ Nat.succ)
    exact hsum.comp_injective Nat.succ_injective
  have hsubtype :=
    hsumShift.sum_add_tsum_subtype_compl (Finset.range (M - 1))
  have hnat := hsumShift.sum_add_tsum_nat_add (M - 1)
  have hcomm :
      (∑' j, pShift (j + (M - 1))) =
        ∑' j, pShift (M - 1 + j) := by
    apply tsum_congr
    intro j
    rw [Nat.add_comm]
  have htail :
      (∑' k : {k : ℕ // k ∉ Finset.range (M - 1)}, pShift k) =
        ∑' j, pShift (M - 1 + j) := by
    linarith [hsubtype, hnat, hcomm]
  rw [summablePurePointSurvivalTail]
  calc
    (∑' j, p (M + j)) = ∑' j, pShift (M - 1 + j) := by
      apply tsum_congr
      intro j
      dsimp only [pShift]
      congr 1
      omega
    _ = ∑' k : {k : ℕ // k ∉ Finset.range (M - 1)},
        pShift k := htail.symm
    _ = ∑' k : {k : ℕ // k ∉ Finset.range (M - 1)},
        p (k + 1) := rfl

/--
**Countably infinite projective survival recurrence.**

For every normalized nonnegative summable pure-point packet and every
nonempty finite head, a positive return occurs by the `M - 1` projective-gap
deadline.  Survival loss is bounded by a quadratic synchronization remainder
plus exactly four times the unsynchronized countable spectral tail.
-/
theorem exists_summablePurePointSurvival_recurrence_quantitative
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M Q : ℕ) (hM : 1 ≤ M) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ (M - 1) ∧
      summablePurePointSurvivalDeviation p omega n ≤
        summablePurePointSurvivalRecurrenceBudget p M Q := by
  let pShift : ℕ → ℝ := fun k => p (k + 1)
  let omegaGap : ℕ → ℝ := fun k => omega (k + 1) - omega 0
  have hpShift : ∀ k, 0 ≤ pShift k := fun k => hp (k + 1)
  have hsumShift : Summable pShift := by
    change Summable (p ∘ Nat.succ)
    exact hsum.comp_injective Nat.succ_injective
  obtain ⟨n, hn0, hnQ, henergy⟩ :=
    exists_summablePhaseEnergy_recurrence_quantitative
      pShift omegaGap hpShift hsumShift (M - 1) Q
  refine ⟨n, hn0, hnQ, ?_⟩
  calc
    summablePurePointSurvivalDeviation p omega n ≤
        summablePhaseEnergy pShift omegaGap n := by
      simpa only [pShift, omegaGap] using
        summablePurePointSurvivalDeviation_le_projectivePhaseEnergy
          p omega hp hsum htotal n
    _ ≤
        (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 *
            ∑ k ∈ Finset.range (M - 1), pShift k +
          4 * ∑' k : {k : ℕ // k ∉ Finset.range (M - 1)},
            pShift k := henergy
    _ = summablePurePointSurvivalRecurrenceBudget p M Q := by
      unfold summablePurePointSurvivalRecurrenceBudget
      rw [summablePurePointSurvivalTail_eq_shifted_complement
        p hsum M hM]

/-- Sampling at multiples of a physical tick is exactly frequency scaling. -/
theorem summablePurePointSurvivalDeviation_nat_mul_tick_eq_scaled
    (p omega : ℕ → ℝ) (n : ℕ) (tick : ℝ) :
    summablePurePointSurvivalDeviation p omega ((n : ℝ) * tick) =
      summablePurePointSurvivalDeviation
        p (fun k => tick * omega k) n := by
  unfold summablePurePointSurvivalDeviation
    summablePurePointSurvivalProbability
    summablePurePointSurvivalAmplitude
    summablePurePointSurvivalPhase
  congr 2
  apply tsum_congr
  intro k
  congr 2
  push_cast
  ring

/-- Every exit is followed strictly later by a return within the same
projective finite-head deadline. -/
theorem exists_summablePurePointSurvival_postExit_recurrence
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M Q : ℕ) (hM : 1 ≤ M)
    (exitTime guardTime : ℝ)
    (hexitTime : 0 ≤ exitTime) (hguard : 0 < guardTime)
    (hexit :
      summablePurePointSurvivalRecurrenceBudget p M Q <
        summablePurePointSurvivalDeviation p omega exitTime) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ (M - 1) ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ (M - 1) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      summablePurePointSurvivalRecurrenceBudget p M Q <
        summablePurePointSurvivalDeviation p omega exitTime ∧
      summablePurePointSurvivalDeviation p omega
          ((n : ℝ) * (exitTime + guardTime)) ≤
        summablePurePointSurvivalRecurrenceBudget p M Q := by
  let tick : ℝ := exitTime + guardTime
  have htick : 0 < tick := by
    dsimp only [tick]
    linarith
  obtain ⟨n, hn0, hnQ, hreturn⟩ :=
    exists_summablePurePointSurvival_recurrence_quantitative
      p (fun k => tick * omega k) hp hsum htotal M Q hM
  refine ⟨n, hn0, hnQ, ?_, ?_, hexit, ?_⟩
  · have hn1 : 1 ≤ n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0)
    calc
      exitTime < tick := by
        dsimp only [tick]
        linarith
      _ = (1 : ℝ) * tick := by ring
      _ ≤ (n : ℝ) * tick :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn1) htick.le
  · exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hnQ) htick.le
  · rw [summablePurePointSurvivalDeviation_nat_mul_tick_eq_scaled]
    simpa only [tick] using hreturn

/--
**Universal countable pure-point survival escape--return dichotomy.**

At every nonempty finite-head resolution, the packet either never exits the
guaranteed survival neighborhood or every witnessed exit has a strictly
later return before the same projective deadline.
-/
theorem summablePurePointSurvival_neverExits_or_postExit_return
    (p omega : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M Q : ℕ) (hM : 1 ≤ M)
    (guardTime : ℝ) (hguard : 0 < guardTime) :
    (∀ t : ℝ, 0 ≤ t →
      summablePurePointSurvivalDeviation p omega t ≤
        summablePurePointSurvivalRecurrenceBudget p M Q) ∨
    ∃ exitTime : ℝ, ∃ n : ℕ,
      0 ≤ exitTime ∧
      0 < n ∧ n ≤ (Q + 1) ^ (M - 1) ∧
      summablePurePointSurvivalRecurrenceBudget p M Q <
        summablePurePointSurvivalDeviation p omega exitTime ∧
      exitTime < (n : ℝ) * (exitTime + guardTime) ∧
      (n : ℝ) * (exitTime + guardTime) ≤
        (((Q + 1) ^ (M - 1) : ℕ) : ℝ) *
          (exitTime + guardTime) ∧
      summablePurePointSurvivalDeviation p omega
          ((n : ℝ) * (exitTime + guardTime)) ≤
        summablePurePointSurvivalRecurrenceBudget p M Q := by
  classical
  by_cases hnever :
      ∀ t : ℝ, 0 ≤ t →
        summablePurePointSurvivalDeviation p omega t ≤
          summablePurePointSurvivalRecurrenceBudget p M Q
  · exact Or.inl hnever
  · right
    push Not at hnever
    obtain ⟨exitTime, hexitTime, hexit⟩ := hnever
    obtain ⟨n, hn0, hnQ, hpost, hdeadline, _hexit, hreturn⟩ :=
      exists_summablePurePointSurvival_postExit_recurrence
        p omega hp hsum htotal M Q hM exitTime guardTime
        hexitTime hguard hexit
    exact
      ⟨exitTime, n, hexitTime, hn0, hnQ, hexit,
        hpost, hdeadline, hreturn⟩

end RHTower
