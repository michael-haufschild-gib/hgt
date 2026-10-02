import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMovingHeadIntegerEscape
import GaloisForLFunctions.RHTower.MobiusDivisorAdaptiveTerminalCriticalSource

/-!
# The canonical square-root core and its necessary signed correction

The literal core processing exactly the active primes with square at most
the cutoff has unbounded energy after quadratic normalization. At the
same cutoffs, any terminal extension either keeps a large negative head
or absorbs a large negative signed child sum. The latter is a necessary
source cancellation law for adaptive extensions, not an RH estimate.
-/

noncomputable section
open Finset
namespace RHTower

/-- The literal active-prime core, including the prime-square boundary. -/
def criticalMovingSquareCore (N : ℕ) : Finset ℕ :=
  (mobiusDivisorSelectionPrimes N).filter (fun p => p * p ≤ N)

private theorem square_core_cover (N : ℕ) :
    ∀ p ∈ mobiusDivisorSelectionPrimes N, p * p ≤ N →
      p ∈ criticalMovingSquareCore N := by
  intro p hp hsq
  exact mem_filter.mpr ⟨hp, hsq⟩

private theorem square_core_terminal (N : ℕ) :
    mobiusDivisorSmallSelectionPrimes N ⊆ criticalMovingSquareCore N := by
  intro p hp
  obtain ⟨hp, hsq⟩ := mem_filter.mp hp
  exact square_core_cover N p hp hsq.le

/-- Exact integer identification with the actual selection fibre. The
extra endpoint p=N in the continuous representation has zero child. -/
theorem criticalMovingPrimeHead_eq_selectionFibre (N : ℕ) (hN : 2 ≤ N) :
    criticalMovingPrimeHead N =
      mobiusDivisorSelectionFibre N (criticalMovingSquareCore N) ∅ := by
  rw [criticalMovingPrimeHead_eq_cell_source hN le_rfl
      (by exact_mod_cast Nat.lt_succ_self N),
    adaptive_terminal_head_source N _ (square_core_cover N),
    ← criticalContinuousAbel_nat_eq_dilation_sum N (by omega)]
  congr 1
  symm
  apply sum_subset
  · intro p hp
    obtain ⟨hpA, hpC⟩ := mem_sdiff.mp hp
    obtain ⟨hpR, hpp⟩ := mem_filter.mp hpA
    have hpN : p < N := mem_range.mp hpR
    have hsq : N < p * p := by
      by_contra h
      exact hpC (square_core_cover N p (mem_filter.mpr ⟨hpR, hpp⟩) (by omega))
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.pos, hpN.le⟩, hpp, hsq⟩
  · intro p hp hn
    obtain ⟨hpI, hpp, hsq⟩ := mem_filter.mp hp
    have hpN := (mem_Icc.mp hpI).2
    have hpeq : p = N := by
      by_contra hne
      apply hn
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩, ?_⟩
      intro hc
      exact (not_le.mpr hsq) (mem_filter.mp hc).2
    subst p
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    rw [div_self hN0, criticalContinuousAbel_eq_zero_le_one le_rfl, mul_zero]

/-- Exact signed source balance for every extension of the canonical core. -/
theorem criticalMovingSquareCore_extension_balance (N : ℕ) (hN : 2 ≤ N)
    (U : Finset ℕ) (hU : U ⊆ mobiusDivisorSelectionPrimes N \ criticalMovingSquareCore N) :
    mobiusDivisorSelectionFibre N (criticalMovingSquareCore N ∪ U) ∅ =
      criticalMovingPrimeHead N -
        ∑ p ∈ U, Real.sqrt p * criticalContinuousAbel ((N : ℝ) / p) := by
  rw [mobiusDivisorSelectionHead_union_terminal N _ U (square_core_terminal N),
    ← criticalMovingPrimeHead_eq_selectionFibre N hN]
  have hs (p : ℕ) (hp : p ∈ U) :=
    adaptive_terminal_singleton_source N _ (square_core_cover N) (hU hp)
  rw [sum_congr rfl hs]
  simp only [neg_mul, sum_neg_distrib, sub_eq_add_neg]

/-- No uniform quadratic energy bound exists for the canonical square-root
core. The cutoffs are actual integers and can exceed any prescribed bound. -/
theorem criticalMovingSquareCore_energy_escape (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧
      C * (N : ℝ) ^ 2 < mobiusDivisorSelectionEnergy N (criticalMovingSquareCore N) := by
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hBC : C < B ^ 2 := by
    dsimp [B]
    nlinarith [le_max_left C 0, le_max_right C 0, sq_nonneg (max C 0)]
  obtain ⟨N, hNN, hN, hneg⟩ := criticalMovingPrimeHead_integer_negative_escape B N₀
  refine ⟨N, hNN, hN, ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBT : 0 < B * N := mul_pos hB hNr
  have hleft : 0 < -criticalMovingPrimeHead N - B * N := by linarith
  have hright : 0 < -criticalMovingPrimeHead N + B * N := by linarith
  have hprod := mul_pos hleft hright
  have htarget := mul_lt_mul_of_pos_right hBC (sq_pos_of_pos hNr)
  have he := sum_mobiusDivisorSelectionFibre_sq_le_energy N (criticalMovingSquareCore N) {∅}
  simp only [sum_singleton, ← criticalMovingPrimeHead_eq_selectionFibre N hN] at he
  nlinarith

/-- At cofinally many cutoffs, every adaptive extension either retains a
large negative head or processes a large negative signed child mass.
The same cutoff works for all extensions. -/
theorem criticalMovingSquareCore_signed_correction_necessary (B C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ 2 ≤ N ∧ ∀ U : Finset ℕ,
      U ⊆ mobiusDivisorSelectionPrimes N \ criticalMovingSquareCore N →
      mobiusDivisorSelectionFibre N (criticalMovingSquareCore N ∪ U) ∅ < -B * N ∨
        (∑ p ∈ U, Real.sqrt p * criticalContinuousAbel ((N : ℝ) / p)) < -C * N := by
  obtain ⟨N, hNN, hN, hneg⟩ := criticalMovingPrimeHead_integer_negative_escape (B + C) N₀
  refine ⟨N, hNN, hN, ?_⟩
  intro U hU
  have hb := criticalMovingSquareCore_extension_balance N hN U hU
  by_cases hh : mobiusDivisorSelectionFibre N (criticalMovingSquareCore N ∪ U) ∅ < -B * N
  · exact Or.inl hh
  · right
    have hh' := le_of_not_gt hh
    linarith

end RHTower
