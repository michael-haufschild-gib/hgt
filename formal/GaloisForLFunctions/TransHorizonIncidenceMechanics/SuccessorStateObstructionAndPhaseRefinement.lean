import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteMultiplicativeObservationState
import Mathlib.Data.Nat.ModEq

/-!
# Successor obstruction and complete phase refinement

The complete multiplicative observation state admits deterministic successor
evolution exactly at horizons at most two. Beyond that threshold, indistinguishable
states with different successors occur arbitrarily far beyond the horizon.

The positive refinement is residue phase modulo the lcm of active divisors.
Phase equality is equivalent to equality of every future sieve observation;
already the first `N` observations suffice. Addition and multiplication both
descend to this phase. No optimality of the observation length `N` is asserted.
-/

open Finset
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- Equality of complete multiplicative states is equality of active divisor tests. -/
theorem horizonObservationState_eq_iff_tests (N k l : ℕ) :
    horizonObservationState N k = horizonObservationState N l ↔
      ∀ d ∈ Icc 1 N, d ∣ k ↔ d ∣ l := by
  constructor
  · intro h d hd
    rw [← dvd_horizonObservationState_iff N k d hd,
      ← dvd_horizonObservationState_iff N l d hd, h]
  · intro h
    have hs : (Icc 1 N).filter (fun d => d ∣ k) =
        (Icc 1 N).filter (fun d => d ∣ l) := by
      ext d
      simp only [mem_filter]
      exact and_congr_right (h d)
    unfold horizonObservationState
    rw [hs]

/-- Residue phase retains the information needed for every future observation. -/
def horizonObservationPhase (N k : ℕ) : ℕ := k % horizonObservationModulus N

/-- The common residue phase is exactly the collection of all active residues. -/
theorem horizonObservationPhase_eq_iff_residues (N k l : ℕ) :
    horizonObservationPhase N k = horizonObservationPhase N l ↔
      ∀ d ∈ Icc 1 N, Nat.ModEq d k l := by
  constructor
  · intro h d hd
    exact Nat.ModEq.of_dvd (Finset.dvd_lcm (f := id) hd) h
  · intro h
    change Nat.ModEq (horizonObservationModulus N) k l
    rcases le_total k l with hkl | hlk
    · apply (Nat.modEq_iff_dvd' hkl).mpr
      exact Finset.lcm_dvd fun d hd => (Nat.modEq_iff_dvd' hkl).mp (h d hd)
    · apply Nat.ModEq.symm
      apply (Nat.modEq_iff_dvd' hlk).mpr
      exact Finset.lcm_dvd fun d hd => (Nat.modEq_iff_dvd' hlk).mp (h d hd).symm

private theorem state_eq_of_phase_eq (N k l : ℕ)
    (h : horizonObservationPhase N k = horizonObservationPhase N l) :
    horizonObservationState N k = horizonObservationState N l := by
  apply (horizonObservationState_eq_iff_tests N k l).mpr
  intro d hd
  exact ((horizonObservationPhase_eq_iff_residues N k l).mp h d hd).dvd_iff dvd_rfl

private theorem exists_short_divisibility_return (d k : ℕ) (hd : 0 < d) :
    ∃ t, t < d ∧ d ∣ k + t := by
  refine ⟨(d - k % d) % d, Nat.mod_lt _ hd, ?_⟩
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod_mod, ← Nat.mod_add_mod k d (d - k % d),
    Nat.add_sub_of_le (Nat.mod_lt k hd).le, Nat.mod_self]

/-- A finite observation trace recovers the complete residue phase. -/
theorem horizonObservationPhase_eq_iff_finite_trace (N k l : ℕ) :
    horizonObservationPhase N k = horizonObservationPhase N l ↔
      ∀ t, t < N → ∀ c : ℕ → ℝ, sieveSeq N c (k + t) = sieveSeq N c (l + t) := by
  constructor
  · intro h t _
    apply (horizonObservationState_eq_iff_all_sieveSeq N (k + t) (l + t)).mp
    apply state_eq_of_phase_eq
    exact Nat.ModEq.add_right t h
  · intro h
    apply (horizonObservationPhase_eq_iff_residues N k l).mpr
    intro d hd
    obtain ⟨t, htd, hkt⟩ := exists_short_divisibility_return d k (mem_Icc.mp hd).1
    have heq := (horizonObservationState_eq_iff_all_sieveSeq N (k + t) (l + t)).mpr
      (h t (htd.trans_le (mem_Icc.mp hd).2))
    have hlt : d ∣ l + t :=
      ((horizonObservationState_eq_iff_tests N (k + t) (l + t)).mp heq d hd).mp hkt
    exact Nat.ModEq.add_right_cancel' t
      ((Nat.modEq_zero_iff_dvd.mpr hkt).trans (Nat.modEq_zero_iff_dvd.mpr hlt).symm)

/-- Phase is the complete invariant of all future sieve responses, for every weight. -/
theorem horizonObservationPhase_eq_iff_all_future (N k l : ℕ) :
    horizonObservationPhase N k = horizonObservationPhase N l ↔
      ∀ t (c : ℕ → ℝ), sieveSeq N c (k + t) = sieveSeq N c (l + t) := by
  constructor
  · intro h t
    apply (horizonObservationState_eq_iff_all_sieveSeq N (k + t) (l + t)).mp
    exact state_eq_of_phase_eq N (k + t) (l + t) (Nat.ModEq.add_right t h)
  · intro h
    exact (horizonObservationPhase_eq_iff_finite_trace N k l).mpr fun t _ => h t

/-- Phase carries exact deterministic successor evolution. -/
theorem horizonObservationPhase_succ (N k : ℕ) :
    horizonObservationPhase N (k + 1) =
      horizonObservationPhase N (horizonObservationPhase N k + 1) := by
  exact (Nat.mod_add_mod k (horizonObservationModulus N) 1).symm

/-- Addition descends to the complete future-observation phase. -/
theorem horizonObservationPhase_add (N k l : ℕ) :
    horizonObservationPhase N (k + l) =
      horizonObservationPhase N (horizonObservationPhase N k + horizonObservationPhase N l) := by
  simp only [horizonObservationPhase, Nat.add_mod, Nat.mod_mod]

/-- Multiplication also descends to the phase refinement. -/
theorem horizonObservationPhase_mul (N k l : ℕ) :
    horizonObservationPhase N (k * l) =
      horizonObservationPhase N (horizonObservationPhase N k * horizonObservationPhase N l) := by
  simp only [horizonObservationPhase, Nat.mul_mod, Nat.mod_mod]

private theorem reflected_unit_state (N : ℕ) :
    horizonObservationState N (horizonObservationModulus N - 1) =
      horizonObservationState N 1 := by
  apply (horizonObservationState_eq_iff_tests _ _ _).mpr
  intro d hd
  constructor
  · intro h
    have hm : d ∣ horizonObservationModulus N := Finset.dvd_lcm (f := id) hd
    have hp := horizonObservationModulus_pos N
    have hs : d ∣ (horizonObservationModulus N - 1) + 1 := by
      rwa [Nat.sub_add_cancel hp]
    exact (Nat.dvd_add_iff_right h).mpr hs
  · intro h
    rw [Nat.eq_one_of_dvd_one h]
    exact one_dvd _

private theorem reflected_successors_ne (N : ℕ) (hN : 2 < N) :
    horizonObservationState N 2 ≠
      horizonObservationState N (horizonObservationModulus N) := by
  intro heq
  have hd : N ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hn : N ∣ horizonObservationModulus N := Finset.dvd_lcm (f := id) hd
  have ht := (horizonObservationState_eq_iff_tests _ _ _).mp heq N hd
  have hn2 : N ∣ 2 := ht.mpr hn
  have := Nat.le_of_dvd (by omega : 0 < 2) hn2
  omega

/-- Equal multiplicative states with unequal successors occur beyond every window. -/
theorem exists_transHorizon_successor_state_collision (N B : ℕ) (hN : 2 < N) :
    ∃ k l, N + B < k ∧ N + B < l ∧
      horizonObservationState N k = horizonObservationState N l ∧
      horizonObservationState N (k + 1) ≠ horizonObservationState N (l + 1) := by
  let t := N + B + 1
  let L := horizonObservationModulus N
  have hL : 0 < L := horizonObservationModulus_pos N
  refine ⟨1 + t * L, (L - 1) + t * L, ?_, ?_, ?_, ?_⟩
  · dsimp [t]; nlinarith
  · dsimp [t]; nlinarith
  · rw [horizonObservationState_add_modulus, horizonObservationState_add_modulus]
    exact (reflected_unit_state N).symm
  · have hk : 1 + t * L + 1 = 2 + t * L := by omega
    have hl : (L - 1) + t * L + 1 = L + t * L := by omega
    rw [hk, hl, horizonObservationState_add_modulus, horizonObservationState_add_modulus]
    exact reflected_successors_ne N hN

private theorem state_succ_congr_of_le_two (N k l : ℕ) (hN : N ≤ 2)
    (h : horizonObservationState N k = horizonObservationState N l) :
    horizonObservationState N (k + 1) = horizonObservationState N (l + 1) := by
  apply (horizonObservationState_eq_iff_tests _ _ _).mpr
  intro d hd
  have ht := (horizonObservationState_eq_iff_tests N k l).mp h d hd
  have hd12 : d = 1 ∨ d = 2 := by have := mem_Icc.mp hd; omega
  rcases hd12 with rfl | rfl
  · simp only [one_dvd]
  · simp only [Nat.dvd_iff_mod_eq_zero] at ht ⊢
    omega

/-- The exact horizon boundary for successor to respect the multiplicative quotient. -/
theorem horizonObservationState_successor_congr_iff (N : ℕ) :
    (∀ k l, horizonObservationState N k = horizonObservationState N l →
      horizonObservationState N (k + 1) = horizonObservationState N (l + 1)) ↔ N ≤ 2 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, l, _, _, heq, hne⟩ :=
      exists_transHorizon_successor_state_collision N 0 (by omega)
    exact hne (h k l heq)
  · exact fun hN k l => state_succ_congr_of_le_two N k l hN

/-- Even an arbitrary nonlinear update on multiplicative states exists exactly below the boundary. -/
theorem horizonObservationState_successor_update_exists_iff (N : ℕ) :
    (∃ F : ℕ → ℕ, ∀ k,
      horizonObservationState N (k + 1) = F (horizonObservationState N k)) ↔ N ≤ 2 := by
  constructor
  · rintro ⟨F, hF⟩
    apply (horizonObservationState_successor_congr_iff N).mp
    intro k l heq
    rw [hF k, hF l, heq]
  · intro hN
    refine ⟨fun x => horizonObservationState N (x + 1), fun k => ?_⟩
    exact state_succ_congr_of_le_two N k (horizonObservationState N k) hN
      (horizonObservationState_idempotent N k).symm

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
