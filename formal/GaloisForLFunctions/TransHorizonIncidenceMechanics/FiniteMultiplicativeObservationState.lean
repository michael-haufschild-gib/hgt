import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Complete finite observation states and multiplicative evolution

The lcm of active divisors is a complete invariant of an observation integer for
all real sieve weights at a fixed horizon. Multiplication descends exactly to
these states. Every state has representatives beyond every prescribed bound;
the classification therefore applies across arbitrarily many horizon bands.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The lcm of all positive divisors that the horizon can observe. -/
def horizonObservationModulus (N : ℕ) : ℕ := (Icc 1 N).lcm id

/-- Canonical multiplicative state retained by every sieve weight at horizon `N`. -/
def horizonObservationState (N k : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun d => d ∣ k)).lcm id

theorem horizonObservationState_dvd (N k : ℕ) : horizonObservationState N k ∣ k := by
  exact Finset.lcm_dvd fun _ hd => (mem_filter.mp hd).2

theorem horizonObservationState_dvd_modulus (N k : ℕ) :
    horizonObservationState N k ∣ horizonObservationModulus N := by
  exact Finset.lcm_mono (filter_subset _ _)

theorem horizonObservationModulus_pos (N : ℕ) : 0 < horizonObservationModulus N := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.mpr
  intro d hd
  have hdpos := (mem_Icc.mp hd).1
  change d ≠ 0
  omega

/-- Only positive divisors of a fixed modulus can occur as states. -/
theorem horizonObservationState_bounds (N k : ℕ) :
    0 < horizonObservationState N k ∧
      horizonObservationState N k ≤ horizonObservationModulus N := by
  exact ⟨Nat.pos_of_dvd_of_pos (horizonObservationState_dvd_modulus N k)
    (horizonObservationModulus_pos N),
    Nat.le_of_dvd (horizonObservationModulus_pos N)
      (horizonObservationState_dvd_modulus N k)⟩

/-- The state preserves each active divisibility test, including at observation zero. -/
theorem dvd_horizonObservationState_iff (N k d : ℕ) (hd : d ∈ Icc 1 N) :
    d ∣ horizonObservationState N k ↔ d ∣ k := by
  constructor
  · exact fun h => h.trans (horizonObservationState_dvd N k)
  · intro h
    exact Finset.dvd_lcm (f := id) (mem_filter.mpr ⟨hd, h⟩)

private theorem observationState_eq_of_tests (N k l : ℕ)
    (h : ∀ d ∈ Icc 1 N, d ∣ k ↔ d ∣ l) :
    horizonObservationState N k = horizonObservationState N l := by
  have hs : (Icc 1 N).filter (fun d => d ∣ k) =
      (Icc 1 N).filter (fun d => d ∣ l) := by
    ext d
    simp only [mem_filter]
    exact and_congr_right (h d)
  unfold horizonObservationState
  rw [hs]

/-- Every sieve response factors through the finite multiplicative state. -/
theorem sieveSeq_horizonObservationState (N k : ℕ) (c : ℕ → ℝ) :
    sieveSeq N c (horizonObservationState N k) = sieveSeq N c k := by
  unfold sieveSeq
  congr 1
  ext d
  simp only [mem_filter]
  exact and_congr_right (dvd_horizonObservationState_iff N k d)

/-- Equality of states is exactly indistinguishability by all arithmetic weights. -/
theorem horizonObservationState_eq_iff_all_sieveSeq (N k l : ℕ) :
    horizonObservationState N k = horizonObservationState N l ↔
      ∀ c : ℕ → ℝ, sieveSeq N c k = sieveSeq N c l := by
  constructor
  · intro h c
    rw [← sieveSeq_horizonObservationState N k c,
      ← sieveSeq_horizonObservationState N l c, h]
  · intro h
    apply observationState_eq_of_tests N k l
    intro d hd
    have ht := h (fun e => if e = d then 1 else 0)
    simp only [sieveSeq, Finset.sum_ite_eq', mem_filter, hd, true_and] at ht
    by_cases hk : d ∣ k <;> by_cases hl : d ∣ l <;> simp_all

theorem horizonObservationState_idempotent (N k : ℕ) :
    horizonObservationState N (horizonObservationState N k) =
      horizonObservationState N k := by
  apply observationState_eq_of_tests
  exact fun d hd => dvd_horizonObservationState_iff N k d hd

private theorem gcd_dvd_observationState (N d k : ℕ) (hd : d ∈ Icc 1 N) :
    Nat.gcd d k ∣ horizonObservationState N k := by
  apply (dvd_horizonObservationState_iff N k _ ?_).mpr (Nat.gcd_dvd_right d k)
  exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left k (mem_Icc.mp hd).1,
    (Nat.gcd_le_left k (mem_Icc.mp hd).1).trans (mem_Icc.mp hd).2⟩

/-- Multiplication of arbitrary observation integers descends to their states. -/
theorem horizonObservationState_mul (N k l : ℕ) :
    horizonObservationState N (k * l) =
      horizonObservationState N
        (horizonObservationState N k * horizonObservationState N l) := by
  apply observationState_eq_of_tests
  intro d hd
  constructor
  · intro h
    have hg : d ∣ Nat.gcd d k * Nat.gcd d l := by
      have hg := gcd_mul_dvd_mul_gcd d k l
      simpa only [gcd_eq_nat_gcd, Nat.gcd_eq_left h] using hg
    exact hg.trans (Nat.mul_dvd_mul
      (gcd_dvd_observationState N d k hd) (gcd_dvd_observationState N d l hd))
  · exact fun h => h.trans (Nat.mul_dvd_mul
      (horizonObservationState_dvd N k) (horizonObservationState_dvd N l))

/-- Common multiples of the active divisors give exact recurrence of states. -/
theorem horizonObservationState_add_modulus (N k t : ℕ) :
    horizonObservationState N (k + t * horizonObservationModulus N) =
      horizonObservationState N k := by
  apply observationState_eq_of_tests
  intro d hd
  have hm : d ∣ t * horizonObservationModulus N :=
    dvd_mul_of_dvd_right (Finset.dvd_lcm (f := id) hd) t
  exact (Nat.dvd_add_iff_left hm).symm

/-- Every complete observation state occurs cofinally, with no relation between window and horizon. -/
theorem exists_gt_horizonObservationState_eq (N k B : ℕ) :
    ∃ m, B < m ∧ horizonObservationState N m = horizonObservationState N k := by
  refine ⟨k + (B + 1) * horizonObservationModulus N, ?_,
    horizonObservationState_add_modulus N k (B + 1)⟩
  have hpos := horizonObservationModulus_pos N
  nlinarith

/-- Multiplicative contexts add no distinguishing power beyond the complete state. -/
theorem horizonObservationState_eq_iff_all_multiplicative_contexts (N k l : ℕ) :
    horizonObservationState N k = horizonObservationState N l ↔
      ∀ r (c : ℕ → ℝ), sieveSeq N c (k * r) = sieveSeq N c (l * r) := by
  constructor
  · intro h r
    apply (horizonObservationState_eq_iff_all_sieveSeq N (k * r) (l * r)).mp
    rw [horizonObservationState_mul N k r, horizonObservationState_mul N l r, h]
  · intro h
    apply (horizonObservationState_eq_iff_all_sieveSeq N k l).mpr
    simpa only [mul_one] using h 1

/-- The canonical state divides every integer with the same complete observation. -/
theorem horizonObservationState_dvd_of_all_sieveSeq_eq (N k l : ℕ)
    (h : ∀ c : ℕ → ℝ, sieveSeq N c k = sieveSeq N c l) :
    horizonObservationState N k ∣ l := by
  rw [(horizonObservationState_eq_iff_all_sieveSeq N k l).mpr h]
  exact horizonObservationState_dvd N l

/-- Every multiplicative observation class recurs beyond every horizon and window. -/
theorem exists_gt_all_multiplicative_sieveSeq_eq (N k B : ℕ) :
    ∃ m, N + B < m ∧
      ∀ r (c : ℕ → ℝ), sieveSeq N c (m * r) = sieveSeq N c (k * r) := by
  obtain ⟨m, hm, heq⟩ := exists_gt_horizonObservationState_eq N k (N + B)
  exact ⟨m, hm,
    (horizonObservationState_eq_iff_all_multiplicative_contexts N m k).mp heq⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
