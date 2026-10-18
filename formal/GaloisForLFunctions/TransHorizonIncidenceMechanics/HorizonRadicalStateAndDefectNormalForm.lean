import GaloisForLFunctions.TransHorizonIncidenceMechanics.AllHorizonRadicalSawtoothAndDefectReduction
import Mathlib.NumberTheory.Primorial

/-!
# The finite radical state and its defect normal form

For squarefree-supported observers the canonical state is `gcd(k, primorial N)`.
It is the smallest positive representative of the complete observation class, and
multiplication descends to lcm. Both active sawtooth endpoints factor through this
state. The prefix defect additionally remembers an exact nonnegative additive energy:
the canonical representative maximizes the defect in its observation class.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The visible squarefree prime support of an observation integer. -/
def horizonRadicalState (N k : ℕ) : ℕ := Nat.gcd k (primorial N)

/-- The state is positive, including at observation zero and horizon zero. -/
theorem horizonRadicalState_pos (N k : ℕ) : 0 < horizonRadicalState N k :=
  Nat.gcd_pos_of_pos_right k (primorial_pos N)

/-- Every state divides its observation integer. -/
theorem horizonRadicalState_dvd (N k : ℕ) : horizonRadicalState N k ∣ k :=
  Nat.gcd_dvd_left k (primorial N)

/-- Every state is a divisor of the finite primorial. -/
theorem horizonRadicalState_dvd_primorial (N k : ℕ) :
    horizonRadicalState N k ∣ primorial N := Nat.gcd_dvd_right k (primorial N)

/-- No prime valuation above one survives in the state. -/
theorem horizonRadicalState_squarefree (N k : ℕ) : Squarefree (horizonRadicalState N k) :=
  (squarefree_primorial N).squarefree_of_dvd (horizonRadicalState_dvd_primorial N k)

/-- The state preserves every squarefree divisibility test visible at the horizon. -/
theorem dvd_horizonRadicalState_iff {N d : ℕ} (k : ℕ) (hd : Squarefree d) (hdN : d ≤ N) :
    d ∣ horizonRadicalState N k ↔ d ∣ k := by
  have hdP : d ∣ primorial N := hd.dvd_primorial.trans (primorial_dvd_primorial hdN)
  simp only [horizonRadicalState, Nat.dvd_gcd_iff, hdP, and_true]

/-- Prime divisibility in the state is exactly visible prime divisibility of the input. -/
theorem prime_dvd_horizonRadicalState_iff (N k : ℕ) {p : ℕ} (hp : p.Prime) :
    p ∣ horizonRadicalState N k ↔ p ∣ k ∧ p ≤ N := by
  rw [horizonRadicalState, Nat.dvd_gcd_iff, hp.dvd_primorial_iff]

/-- All squarefree-supported sieve responses factor through the state. -/
theorem sieveSeq_horizonRadicalState (N k : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) :
    sieveSeq N c (horizonRadicalState N k) = sieveSeq N c k := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  by_cases hsq : Squarefree d
  · simp only [dvd_horizonRadicalState_iff k hsq (Finset.mem_Icc.mp hd).2]
  · rw [hc d hsq]
    split_ifs <;> rfl

/-- Equality of states is exactly equality of all squarefree-supported observations. -/
theorem horizonRadicalState_eq_iff_all_squarefree_sieveSeq (N k l : ℕ) :
    horizonRadicalState N k = horizonRadicalState N l ↔
      ∀ c : ℕ → ℝ, (∀ d : ℕ, ¬ Squarefree d → c d = 0) →
        sieveSeq N c k = sieveSeq N c l := by
  constructor
  · intro h c hc
    rw [← sieveSeq_horizonRadicalState N k hc,
      ← sieveSeq_horizonRadicalState N l hc, h]
  · intro h
    apply (Nat.Squarefree.ext_iff (horizonRadicalState_squarefree N k)
      (horizonRadicalState_squarefree N l)).mpr
    intro p hp
    rw [prime_dvd_horizonRadicalState_iff N k hp, prime_dvd_horizonRadicalState_iff N l hp]
    by_cases hpN : p ≤ N
    · have hpI : p ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hp.one_le, hpN⟩
      have hc : ∀ d : ℕ, ¬ Squarefree d → (if d = p then (1 : ℝ) else 0) = 0 := by
        intro d hd
        split_ifs with hdp
        · subst d
          exact (hd hp.squarefree).elim
        · rfl
      have ht := h (fun d => if d = p then 1 else 0) hc
      simp only [sieveSeq, Finset.sum_ite_eq', Finset.mem_filter, hpI, true_and] at ht
      by_cases hk : p ∣ k <;> by_cases hl : p ∣ l <;> simp_all
    · simp [hpN]

/-- The quotient image is exactly the divisor set of the primorial. -/
theorem horizonRadicalState_range_iff (N r : ℕ) :
    (∃ k, horizonRadicalState N k = r) ↔ r ∣ primorial N := by
  constructor
  · rintro ⟨k, rfl⟩
    exact horizonRadicalState_dvd_primorial N k
  · intro hr
    exact ⟨r, Nat.gcd_eq_left hr⟩

/-- Taking the canonical state twice has no further effect. -/
theorem horizonRadicalState_idempotent (N k : ℕ) :
    horizonRadicalState N (horizonRadicalState N k) = horizonRadicalState N k :=
  Nat.gcd_eq_left (horizonRadicalState_dvd_primorial N k)

/-- The canonical state is the smallest positive representative of its class. -/
theorem horizonRadicalState_isLeast (N k : ℕ) :
    IsLeast {l : ℕ | 0 < l ∧ horizonRadicalState N l = horizonRadicalState N k}
      (horizonRadicalState N k) := by
  refine ⟨⟨horizonRadicalState_pos N k, horizonRadicalState_idempotent N k⟩, ?_⟩
  intro l hl
  rw [← hl.2]
  exact Nat.le_of_dvd hl.1 (horizonRadicalState_dvd N l)

/-- Multiplication becomes the join operation on squarefree divisors of the primorial. -/
theorem horizonRadicalState_mul (N k l : ℕ) :
    horizonRadicalState N (k * l) =
      Nat.lcm (horizonRadicalState N k) (horizonRadicalState N l) := by
  have hsq : Squarefree (Nat.lcm (horizonRadicalState N k) (horizonRadicalState N l)) :=
    (squarefree_primorial N).squarefree_of_dvd
      (Nat.lcm_dvd (horizonRadicalState_dvd_primorial N k) (horizonRadicalState_dvd_primorial N l))
  apply (Nat.Squarefree.ext_iff (horizonRadicalState_squarefree N (k * l)) hsq).mpr
  intro p hp
  rw [prime_dvd_horizonRadicalState_iff N (k * l) hp, hp.dvd_mul, hp.dvd_lcm,
    prime_dvd_horizonRadicalState_iff N k hp, prime_dvd_horizonRadicalState_iff N l hp]
  tauto

/-- Positive powers are idempotent in the squarefree observation quotient. -/
theorem horizonRadicalState_pow (N k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    horizonRadicalState N (k ^ m) = horizonRadicalState N k := by
  apply (horizonRadicalState_eq_iff_all_squarefree_sieveSeq N (k ^ m) k).mpr
  intro c hc
  exact sieveSeq_pow_of_squarefree_support N hc k hm

/-- Both active sawtooth endpoints descend to the same minimal radical state. -/
theorem activeCenteredSawtoothSum_horizonRadicalState (N : ℕ) {k : ℕ} (hk : 1 ≤ k)
    {c : ℕ → ℝ} (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) :
    activeCenteredSawtoothSum N c k (k - 1) =
        activeCenteredSawtoothSum N c (horizonRadicalState N k) (horizonRadicalState N k - 1) ∧
      activeCenteredSawtoothSum N c k k =
        activeCenteredSawtoothSum N c (horizonRadicalState N k) (horizonRadicalState N k) := by
  have hkadd := Nat.sub_add_cancel hk
  have hradd := Nat.sub_add_cancel (horizonRadicalState_pos N k)
  constructor
  · have hk' := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (k - 1)
    have hr' := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c (horizonRadicalState N k - 1)
    rw [hkadd] at hk'
    rw [hradd, sieveSeq_horizonRadicalState N k hc,
      sieveSeq_horizonRadicalState N k (squarefree_support_harmonic hc)] at hr'
    exact hk'.trans hr'.symm
  · have hk' := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (k - 1)
    have hr' := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c (horizonRadicalState N k - 1)
    rw [hkadd] at hk'
    rw [hradd, sieveSeq_horizonRadicalState N k hc,
      sieveSeq_horizonRadicalState N k (squarefree_support_harmonic hc)] at hr'
    exact hk'.trans hr'.symm

private theorem polarization_all_prefixes (N M : ℕ) (c : ℕ → ℝ) :
    2 * sieveRenormalizedPrefixDefect N M c =
      -(∑ j ∈ Finset.Icc 1 M, (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)) +
        sieveSeq N c (M + 1) ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) := by
  cases M with
  | zero => simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  | succ M =>
    exact two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N (by omega) c

/-- Exact defect normal form: the canonical representative plus negative additive energy. -/
theorem two_mul_sieveRenormalizedPrefixDefect_sub_horizonRadicalState (N : ℕ)
    {k : ℕ} (hk : 1 ≤ k) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) :
    2 * (sieveRenormalizedPrefixDefect N (k - 1) c -
        sieveRenormalizedPrefixDefect N (horizonRadicalState N k - 1) c) =
      -(∑ j ∈ Finset.Icc (horizonRadicalState N k) (k - 1),
        (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)) := by
  have hr := horizonRadicalState_pos N k
  have hrk := Nat.le_of_dvd hk (horizonRadicalState_dvd N k)
  have h₁ := polarization_all_prefixes N (k - 1) c
  have h₂ := polarization_all_prefixes N (horizonRadicalState N k - 1) c
  have hsplit : Finset.Icc 1 (k - 1) = Finset.Icc 1 (horizonRadicalState N k - 1) ∪
      Finset.Icc (horizonRadicalState N k) (k - 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (horizonRadicalState N k - 1))
      (Finset.Icc (horizonRadicalState N k) (k - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Finset.mem_Icc] at hj₁ hj₂
    omega
  rw [Nat.sub_add_cancel hk, hsplit, Finset.sum_union hdisj] at h₁
  rw [Nat.sub_add_cancel hr, sieveSeq_horizonRadicalState N k hc] at h₂
  linarith

/-- The minimal positive representative maximizes the defect throughout its radical class. -/
theorem sieveRenormalizedPrefixDefect_le_horizonRadicalState (N : ℕ) {k : ℕ}
    (hk : 1 ≤ k) {c : ℕ → ℝ} (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) :
    sieveRenormalizedPrefixDefect N (k - 1) c ≤
      sieveRenormalizedPrefixDefect N (horizonRadicalState N k - 1) c := by
  have h := two_mul_sieveRenormalizedPrefixDefect_sub_horizonRadicalState N hk hc
  have hE : 0 ≤ ∑ j ∈ Finset.Icc (horizonRadicalState N k) (k - 1),
      (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- Equality with the canonical defect is equivalent to complete additive flatness in between. -/
theorem sieveRenormalizedPrefixDefect_eq_horizonRadicalState_iff (N : ℕ) {k : ℕ}
    (hk : 1 ≤ k) {c : ℕ → ℝ} (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) :
    sieveRenormalizedPrefixDefect N (k - 1) c =
        sieveRenormalizedPrefixDefect N (horizonRadicalState N k - 1) c ↔
      ∀ j ∈ Finset.Icc (horizonRadicalState N k) (k - 1),
        sieveSeq N c (j + 1) = sieveSeq N c j := by
  have h := two_mul_sieveRenormalizedPrefixDefect_sub_horizonRadicalState N hk hc
  have hzero : (∑ j ∈ Finset.Icc (horizonRadicalState N k) (k - 1),
      (sieveSeq N c (j + 1) - sieveSeq N c j) ^ (2 : ℕ)) = 0 ↔
      ∀ j ∈ Finset.Icc (horizonRadicalState N k) (k - 1),
        sieveSeq N c (j + 1) = sieveSeq N c j := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
    simp only [sq_eq_zero_iff, sub_eq_zero]
  constructor
  · intro heq
    apply hzero.mp
    linarith
  · intro hflat
    have hz := hzero.mpr hflat
    linarith

/-- A global upper bound for every prefix is equivalent to its finite set of tests
at predecessors of divisors of the primorial. -/
theorem sieveRenormalizedPrefixDefect_global_upper_bound_iff_radical_states
    (N : ℕ) {c : ℕ → ℝ} (hc : ∀ d : ℕ, ¬ Squarefree d → c d = 0) (B : ℝ) :
    (∀ M : ℕ, sieveRenormalizedPrefixDefect N M c ≤ B) ↔
      ∀ r : ℕ, r ∣ primorial N → sieveRenormalizedPrefixDefect N (r - 1) c ≤ B := by
  constructor
  · intro h r _
    exact h (r - 1)
  · intro h M
    have hle := sieveRenormalizedPrefixDefect_le_horizonRadicalState N
      (by omega : 1 ≤ M + 1) hc
    have hbound := h (horizonRadicalState N (M + 1))
      (horizonRadicalState_dvd_primorial N (M + 1))
    simpa only [Nat.add_sub_cancel] using hle.trans hbound

/-- Every radical class whose representative lies in the first two horizon widths
has nonpositive damped defect, with no size bound on the observation integer. -/
theorem sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos_of_radicalState
    {ε : ℝ} (hε : 0 ≤ ε) {N k : ℕ} (hk : 1 ≤ k)
    (hrN : horizonRadicalState N k ≤ 2 * N) :
    sieveRenormalizedPrefixDefect N (k - 1) (pmPowerDampedRealWeight ε) ≤ 0 := by
  have hle := sieveRenormalizedPrefixDefect_le_horizonRadicalState N hk
    (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)
  apply hle.trans
  have hr := horizonRadicalState_pos N k
  by_cases hr1 : horizonRadicalState N k = 1
  · simp [hr1, sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  · have hbound := sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_pow_nonpos
      hε (by omega : 2 ≤ horizonRadicalState N k) hrN (le_refl 1)
    simpa only [pow_one] using hbound

/-- Möbius defect nonpositivity depends on the finite radical state, not on observation size. -/
theorem sieveRenormalizedPrefixDefect_moebiusReal_nonpos_of_radicalState {N k : ℕ}
    (hk : 1 ≤ k) (hrN : horizonRadicalState N k ≤ 2 * N) :
    sieveRenormalizedPrefixDefect N (k - 1) moebiusReal ≤ 0 := by
  have hw : pmPowerDampedRealWeight 0 = moebiusReal := by
    funext d
    simp [pmPowerDampedRealWeight]
  simpa only [hw] using
    sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos_of_radicalState
      (le_refl 0) hk hrN

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
