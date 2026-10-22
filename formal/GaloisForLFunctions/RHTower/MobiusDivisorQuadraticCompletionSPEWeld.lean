import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.MobiusDivisorBernoulliPrimeEnergy

/-!
# Quadratic full-selection completion as an SP-E producer

The signed Möbius--divisor producer is the exact SP-E half-order Abel
current.  Prime-selection arguments only become RH-bearing when they give
one genuine completion of every finite source, with a quadratic energy cap
at every prefix.  This module records that precise handoff.  It deliberately
does not replace the signed source by an absolute estimate or weaken a full
completion to a fixed-core or finite-batch result.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace RHTower

/-- A literal complete prime-insertion path whose entire energy profile has one
quadratic cap.  The cap is uniform in the cutoff; the path itself may depend
on that cutoff. -/
def MobiusDivisorQuadraticEnergyCompletion : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, ∃ N : ℕ, ∃ Q : ℕ → Finset ℕ,
    Q 0 = ∅ ∧
      Q N = mobiusDivisorSelectionPrimes M ∧
      (∀ k < N, ∃ p ∈ mobiusDivisorSelectionPrimes M \ Q k,
        Q (k + 1) = insert p (Q k)) ∧
      ∀ k ≤ N, mobiusDivisorSelectionEnergy M (Q k) ≤ C * (M : ℝ) ^ (2 : ℕ)

private theorem mobiusDivisorDilationChannel_terminal_zero (M : ℕ) :
    mobiusDivisorDilationChannel M M = 0 := by
  by_cases hM : M = 0
  · subst M
    simp [mobiusDivisorDilationChannel]
  · simp [mobiusDivisorDilationChannel,
      Finset.Icc_eq_empty_of_lt (by omega : M - 1 < M)]

private theorem sum_mobiusDivisorDilationChannel_extend (M : ℕ) :
    (∑ d ∈ Icc 1 (M - 1), mobiusDivisorDilationChannel M d) =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
  apply sum_subset (Icc_subset_Icc le_rfl (by omega))
  intro d hd hnot
  have hdM : d = M := by
    simp only [mem_Icc] at hd hnot
    omega
  subst d
  exact mobiusDivisorDilationChannel_terminal_zero M

/-- A quadratic energy cap through an actual complete prime insertion for
every cutoff bounds the exact signed SP-E Abel producer, hence proves RH.
This is a source-to-endpoint bridge: it makes no positivity, monotonicity,
fixed-core, or clock-independent cancellation assumption. -/
theorem riemannHypothesis_of_mobiusDivisorQuadraticEnergyCompletion
    (hcompletion : MobiusDivisorQuadraticEnergyCompletion) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded]
  obtain ⟨C, hC, hcompletion⟩ := hcompletion
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro M hM
  obtain ⟨N, Q, _hQzero, hQfull, _hstep, henergy⟩ := hcompletion M
  have hfull := henergy N le_rfl
  rw [hQfull, mobiusDivisorSelectionEnergy_full] at hfull
  have hMpos : (0 : ℝ) < M := by positivity
  have hsum : mobiusDivisorSquareRootAbelMoment M =
      ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d := by
    rw [mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels,
      sum_mobiusDivisorDilationChannel_extend]
  rw [hsum, abs_div, abs_of_pos hMpos]
  apply (div_le_iff₀ hMpos).mpr
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hMpos.le)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hC]
  exact hfull

end RHTower
