import GaloisForLFunctions.TransHorizonIncidenceMechanics.SuccessorStateObstructionAndPhaseRefinement
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ArithmeticUncertaintyAndSpikeCancellation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.AllHorizonRadicalSawtoothAndDefectReduction
import Mathlib.Data.Nat.Periodic
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Period energy, affine defect drift, and full-period moving averages

The response returns to its phase after a horizon modulus, but its cumulative
defect loses exactly half the period Dirichlet energy. This energy is independent
of phase and vanishes exactly for constant responses. Every other response gives
exact linear escape along every phase subsequence. Averaging a full observation
period removes phase fluctuations even under a single-step window shift.
-/

open Finset Filter
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Total successor oscillation energy in one complete observation period. -/
def horizonPeriodDirichletEnergy (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (horizonObservationModulus N),
    (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)

/-- The sum of all defect phases in a moving observation-period window. -/
def horizonPeriodDefectWindow (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (horizonObservationModulus N), sieveRenormalizedPrefixDefect N (M + j) c

private theorem response_periodic (N : ℕ) (c : ℕ → ℝ) :
    Function.Periodic (sieveSeq N c) (horizonObservationModulus N) := by
  intro k
  apply (horizonObservationState_eq_iff_all_sieveSeq N _ _).mp
  simpa only [one_mul] using horizonObservationState_add_modulus N k 1

private theorem oscillation_periodic (N : ℕ) (c : ℕ → ℝ) :
    Function.Periodic
      (fun k => (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ))
      (horizonObservationModulus N) := by
  intro k
  change (sieveSeq N c (k + horizonObservationModulus N + 1) -
    sieveSeq N c (k + horizonObservationModulus N)) ^ (2 : ℕ) =
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)
  rw [show k + horizonObservationModulus N + 1 =
    (k + 1) + horizonObservationModulus N by omega,
    response_periodic N c (k + 1), response_periodic N c k]

private theorem window_shift_balance (f : ℕ → ℝ) (a r : ℕ) :
    (∑ j ∈ range r, f (a + 1 + j)) - (∑ j ∈ range r, f (a + j)) =
      f (a + r) - f a := by
  have h₁ := Finset.sum_range_succ (fun j => f (a + j)) r
  have h₂ := Finset.sum_range_succ' (fun j => f (a + j)) r
  simp only [Nat.add_zero] at h₂
  have hs : (∑ j ∈ range r, f (a + 1 + j)) =
      ∑ j ∈ range r, f (a + (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1; omega
  rw [hs]
  linarith

/-- Every starting phase carries the same complete-period oscillation energy. -/
theorem sum_range_horizonPeriodDirichletEnergy (N a : ℕ) (c : ℕ → ℝ) :
    (∑ j ∈ range (horizonObservationModulus N),
      (sieveSeq N c (a + j + 1) - sieveSeq N c (a + j)) ^ (2 : ℕ)) =
      horizonPeriodDirichletEnergy N c := by
  induction a with
  | zero => simp only [zero_add, horizonPeriodDirichletEnergy]
  | succ a ih =>
    have h := window_shift_balance
      (fun k => (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ))
      a (horizonObservationModulus N)
    have hp := oscillation_periodic N c a
    dsimp only at hp
    rw [hp] at h
    change (∑ j ∈ range (horizonObservationModulus N),
      (sieveSeq N c (a + 1 + j + 1) - sieveSeq N c (a + 1 + j)) ^ (2 : ℕ)) = _
    linarith

/-- Interval form of phase-independent period energy, with the prefix endpoint shift explicit. -/
theorem sum_Icc_horizonPeriodDirichletEnergy (N M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Icc (M + 1) (M + horizonObservationModulus N),
      (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) =
      horizonPeriodDirichletEnergy N c := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  rw [show M + horizonObservationModulus N + 1 - (M + 1) =
    horizonObservationModulus N by omega]
  exact sum_range_horizonPeriodDirichletEnergy N (M + 1) c

theorem horizonPeriodDirichletEnergy_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ horizonPeriodDirichletEnergy N c :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Requested period-shift law: the returned boundary leaves exactly negative period energy. -/
theorem two_mul_sieveRenormalizedPrefixDefect_period_sub (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (c : ℕ → ℝ) :
    2 * (sieveRenormalizedPrefixDefect N (M + horizonObservationModulus N) c -
      sieveRenormalizedPrefixDefect N M c) =
      -(∑ k ∈ Icc (M + 1) (M + horizonObservationModulus N),
        (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) := by
  have heq : sieveSeq N c (M + horizonObservationModulus N + 1) =
      sieveSeq N c (M + 1) := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      response_periodic N c (M + 1)
  have h := two_mul_sieveRenormalizedPrefixDefect_sub_of_sieveSeq_eq N c
    (by omega : 2 ≤ M + 1) (by omega : M + 1 ≤ M + horizonObservationModulus N + 1) heq
  simpa only [Nat.add_sub_cancel] using h

/-- The period-shift law also includes the empty prefix, with no endpoint restriction. -/
theorem two_mul_sieveRenormalizedPrefixDefect_period_sub_all (N M : ℕ) (c : ℕ → ℝ) :
    2 * (sieveRenormalizedPrefixDefect N (M + horizonObservationModulus N) c -
      sieveRenormalizedPrefixDefect N M c) =
      -(∑ k ∈ Icc (M + 1) (M + horizonObservationModulus N),
        (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) := by
  rcases M with _ | M
  · have hz : sieveRenormalizedPrefixDefect N 0 c = 0 := by
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
    have hp := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N
      (horizonObservationModulus_pos N) c
    have heq : sieveSeq N c (horizonObservationModulus N + 1) = sieveSeq N c 1 := by
      simpa only [Nat.add_comm] using response_periodic N c 1
    rw [heq] at hp
    simp only [zero_add, hz, sub_zero]
    linarith
  · exact two_mul_sieveRenormalizedPrefixDefect_period_sub N (by omega) c

/-- Exact defect drift over an arbitrary number of complete periods. -/
theorem sieveRenormalizedPrefixDefect_add_period_mul (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (q : ℕ) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N (M + q * horizonObservationModulus N) c =
      sieveRenormalizedPrefixDefect N M c - (q : ℝ) * horizonPeriodDirichletEnergy N c / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h := two_mul_sieveRenormalizedPrefixDefect_period_sub N
      (by omega : 1 ≤ M + q * horizonObservationModulus N) c
    rw [sum_Icc_horizonPeriodDirichletEnergy, ih] at h
    rw [Nat.succ_mul, ← Nat.add_assoc, Nat.cast_succ]
    linarith

/-- Period multiples never increase the defect, for every real arithmetic weight. -/
theorem sieveRenormalizedPrefixDefect_add_period_mul_le (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (q : ℕ) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N (M + q * horizonObservationModulus N) c ≤
      sieveRenormalizedPrefixDefect N M c := by
  rw [sieveRenormalizedPrefixDefect_add_period_mul N hM q c]
  have h := horizonPeriodDirichletEnergy_nonneg N c
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith [mul_nonneg hq h]

/-- Every phase subsequence is antitone in the number of elapsed periods. -/
theorem sieveRenormalizedPrefixDefect_period_antitone (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (c : ℕ → ℝ) :
    Antitone (fun q : ℕ => sieveRenormalizedPrefixDefect N
      (M + q * horizonObservationModulus N) c) := by
  intro a b hab
  change sieveRenormalizedPrefixDefect N (M + b * horizonObservationModulus N) c ≤
    sieveRenormalizedPrefixDefect N (M + a * horizonObservationModulus N) c
  rw [sieveRenormalizedPrefixDefect_add_period_mul N hM b c,
    sieveRenormalizedPrefixDefect_add_period_mul N hM a c]
  have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
  have he := horizonPeriodDirichletEnergy_nonneg N c
  nlinarith [mul_le_mul_of_nonneg_left hcast he]

/-- Quantitative oscillation control within any one-period window. -/
theorem sieve_period_oscillation_bound (N a t : ℕ) (c : ℕ → ℝ)
    (ht : t ≤ horizonObservationModulus N) :
    (sieveSeq N c (a + t) - sieveSeq N c a) ^ (2 : ℕ) ≤
      (t : ℝ) * horizonPeriodDirichletEnergy N c := by
  have hp := sq_sub_le_length_mul_sum_range_addDiff_sq (sieveSeq N c) a t
  have hs : (∑ j ∈ range t,
      (sieveSeq N c (a + j + 1) - sieveSeq N c (a + j)) ^ (2 : ℕ)) ≤
      ∑ j ∈ range (horizonObservationModulus N),
        (sieveSeq N c (a + j + 1) - sieveSeq N c (a + j)) ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht) (fun _ _ _ => sq_nonneg _)
  rw [sum_range_horizonPeriodDirichletEnergy] at hs
  exact hp.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg t))

/-- No hidden zero-energy modes: the entire response must be constant. -/
theorem horizonPeriodDirichletEnergy_eq_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    horizonPeriodDirichletEnergy N c = 0 ↔ ∀ k, sieveSeq N c k = sieveSeq N c 0 := by
  constructor
  · intro h k
    have hp := sieve_period_oscillation_bound N 0 (k % horizonObservationModulus N) c
      (Nat.mod_lt k (horizonObservationModulus_pos N)).le
    rw [zero_add, h, mul_zero] at hp
    have heq : sieveSeq N c (k % horizonObservationModulus N) = sieveSeq N c 0 :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hp (sq_nonneg _)))
    exact ((response_periodic N c).map_mod_nat k).symm.trans heq
  · intro h
    unfold horizonPeriodDirichletEnergy
    apply Finset.sum_eq_zero
    intro k _
    rw [h (k + 1), h k, sub_self, zero_pow (by omega : 2 ≠ 0)]

/-- Nonconstancy on a single period is exactly strict energy positivity. -/
theorem horizonPeriodDirichletEnergy_pos_iff (N : ℕ) (c : ℕ → ℝ) :
    0 < horizonPeriodDirichletEnergy N c ↔
      ∃ k ∈ range (horizonObservationModulus N), sieveSeq N c k ≠ sieveSeq N c 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hc : ∀ k, sieveSeq N c k = sieveSeq N c 0 := fun k =>
      ((response_periodic N c).map_mod_nat k).symm.trans
        (hn _ (mem_range.mpr (Nat.mod_lt k (horizonObservationModulus_pos N))))
    have hz := (horizonPeriodDirichletEnergy_eq_zero_iff N c).mpr hc
    linarith
  · rintro ⟨k, _, hk⟩
    have he := horizonPeriodDirichletEnergy_nonneg N c
    by_contra hn
    have hz : horizonPeriodDirichletEnergy N c = 0 := by linarith
    exact hk ((horizonPeriodDirichletEnergy_eq_zero_iff N c).mp hz k)

/-- The zero-energy sector has identically zero prefix defect. -/
theorem sieveRenormalizedPrefixDefect_eq_zero_of_periodEnergy_eq_zero (N M : ℕ)
    (c : ℕ → ℝ) (h : horizonPeriodDirichletEnergy N c = 0) :
    sieveRenormalizedPrefixDefect N M c = 0 := by
  have hc := (horizonPeriodDirichletEnergy_eq_zero_iff N c).mp h
  rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  apply Finset.sum_eq_zero
  intro k _
  rw [hc (k + 1), hc k, sub_self, mul_zero]

/-- Returning to the same response phase preserves the cumulative defect exactly
in the constant-response sector; otherwise phase alone loses traversal energy. -/
theorem sieveRenormalizedPrefixDefect_period_eq_iff (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N (M + horizonObservationModulus N) c =
      sieveRenormalizedPrefixDefect N M c ↔ ∀ k, sieveSeq N c k = sieveSeq N c 0 := by
  rw [← horizonPeriodDirichletEnergy_eq_zero_iff]
  have h := two_mul_sieveRenormalizedPrefixDefect_period_sub N hM c
  rw [sum_Icc_horizonPeriodDirichletEnergy] at h
  constructor <;> intro heq <;> linarith

/-- Exact linear drift gives genuine convergence to negative infinity on every phase. -/
theorem sieveRenormalizedPrefixDefect_period_tendsto_atBot (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (c : ℕ → ℝ)
    (hc : ∃ k ∈ range (horizonObservationModulus N), sieveSeq N c k ≠ sieveSeq N c 0) :
    Tendsto (fun q : ℕ => sieveRenormalizedPrefixDefect N
      (M + q * horizonObservationModulus N) c) atTop atBot := by
  have hE := (horizonPeriodDirichletEnergy_pos_iff N c).mpr hc
  apply Filter.tendsto_atBot.mpr
  intro B
  obtain ⟨q₀, hq₀⟩ := exists_nat_gt
    ((sieveRenormalizedPrefixDefect N M c - B) / (horizonPeriodDirichletEnergy N c / 2))
  apply Filter.eventually_atTop.mpr
  refine ⟨q₀, fun q hq => ?_⟩
  have hcast : (q₀ : ℝ) ≤ q := by exact_mod_cast hq
  have hm := (div_lt_iff₀ (by positivity : 0 < horizonPeriodDirichletEnergy N c / 2)).mp hq₀
  rw [sieveRenormalizedPrefixDefect_add_period_mul N hM q c]
  nlinarith [mul_le_mul_of_nonneg_left hcast hE.le]

/-- Unconditional classification: the flat response has zero defect; every other
response loses positive period energy and escapes along every phase. -/
theorem sieveRenormalizedPrefixDefect_period_dichotomy (N : ℕ) (c : ℕ → ℝ) :
    ((∀ k, sieveSeq N c k = sieveSeq N c 0) ∧
      ∀ M, sieveRenormalizedPrefixDefect N M c = 0) ∨
    (0 < horizonPeriodDirichletEnergy N c ∧ ∀ M, 1 ≤ M →
      Tendsto (fun q : ℕ => sieveRenormalizedPrefixDefect N
        (M + q * horizonObservationModulus N) c) atTop atBot) := by
  by_cases h : horizonPeriodDirichletEnergy N c = 0
  · exact Or.inl ⟨(horizonPeriodDirichletEnergy_eq_zero_iff N c).mp h,
      fun M => sieveRenormalizedPrefixDefect_eq_zero_of_periodEnergy_eq_zero N M c h⟩
  · have he := horizonPeriodDirichletEnergy_nonneg N c
    have hp : 0 < horizonPeriodDirichletEnergy N c := by
      rcases lt_or_eq_of_le he with hp | hz
      · exact hp
      · exact False.elim (h hz.symm)
    exact Or.inr ⟨hp, fun _ hM => sieveRenormalizedPrefixDefect_period_tendsto_atBot N hM c
      ((horizonPeriodDirichletEnergy_pos_iff N c).mp hp)⟩

/-- A one-step window shift loses exactly half the period energy: all phases cancel. -/
theorem two_mul_horizonPeriodDefectWindow_succ_sub (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (c : ℕ → ℝ) :
    2 * (horizonPeriodDefectWindow N (M + 1) c - horizonPeriodDefectWindow N M c) =
      -horizonPeriodDirichletEnergy N c := by
  have h := window_shift_balance (fun k => sieveRenormalizedPrefixDefect N k c)
    M (horizonObservationModulus N)
  have hp := two_mul_sieveRenormalizedPrefixDefect_period_sub N hM c
  rw [sum_Icc_horizonPeriodDirichletEnergy] at hp
  change 2 * ((∑ j ∈ range (horizonObservationModulus N),
    sieveRenormalizedPrefixDefect N (M + 1 + j) c) -
    (∑ j ∈ range (horizonObservationModulus N), sieveRenormalizedPrefixDefect N (M + j) c)) = _
  linarith

/-- Full-period window totals are exactly affine under arbitrary additive shifts. -/
theorem horizonPeriodDefectWindow_add (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (t : ℕ) (c : ℕ → ℝ) :
    horizonPeriodDefectWindow N (M + t) c = horizonPeriodDefectWindow N M c -
      (t : ℝ) * horizonPeriodDirichletEnergy N c / 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := two_mul_horizonPeriodDefectWindow_succ_sub N (by omega : 1 ≤ M + t) c
    rw [ih] at h
    rw [Nat.add_succ, Nat.cast_succ]
    linarith

/-- The normalized full-period moving average has the exact slope `-E / (2L)`. -/
theorem horizonPeriodDefectWindow_average_add (N : ℕ) {M : ℕ}
    (hM : 1 ≤ M) (t : ℕ) (c : ℕ → ℝ) :
    horizonPeriodDefectWindow N (M + t) c / (horizonObservationModulus N : ℝ) =
      horizonPeriodDefectWindow N M c / (horizonObservationModulus N : ℝ) -
        (t : ℝ) * horizonPeriodDirichletEnergy N c /
          (2 * (horizonObservationModulus N : ℝ)) := by
  rw [horizonPeriodDefectWindow_add N hM t c]
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
