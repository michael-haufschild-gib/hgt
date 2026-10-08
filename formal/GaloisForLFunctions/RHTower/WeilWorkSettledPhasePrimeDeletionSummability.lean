import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePrimeDeletionVariance

/-!
# Summable prime deletion deviations of the actual source

The finite variance budget yields a summable weighted square error. This does
not assert equality of any individual deletion endpoint with its canonical value.
-/

open Complex Filter Finset
open scoped Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

def primeDeletionDeviationEnergy (r : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p.Prime then (p : ℝ) ^ 2 / ((p : ℝ) - 1) *
    (r p - (1 - (p : ℝ)⁻¹)) ^ 2 else 0

theorem primeDeletionDeviationEnergy_nonneg (r : ℕ → ℝ) (p : ℕ) :
    0 ≤ primeDeletionDeviationEnergy r p := by
  unfold primeDeletionDeviationEnergy
  split_ifs with hp
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact mul_nonneg (div_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _)
  · exact le_rfl

/-- The actual prime endpoint errors have finite weighted square sum. -/
theorem exists_forward_prime_deletion_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ (V : ℝ) (r : ℕ → ℝ), 0 ≤ V ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N,
        ‖sourceCoeff lam n - sourceCompletion hW 1‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 V) ∧
      (∀ Q : ℕ, Q ≠ 0 → 0 < r Q ∧
        Tendsto (fun s : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r Q : ℂ))) ∧
      Summable (primeDeletionDeviationEnergy r) ∧
      ‖sourceCompletion hW 1‖ ^ 2 * ∑' p : ℕ, primeDeletionDeviationEnergy r p ≤ V := by
  classical
  obtain ⟨V, r, hV0, hV, hr, hb⟩ := exists_forward_prime_deletion_variance hW
  have hB : sourceCompletion hW 1 ≠ 0 := by
    dsimp [sourceCompletion]
    exact mul_ne_zero (IntegerMassRigidity.bigG_ne_zero lam (by norm_num))
      (Complex.exp_ne_zero _)
  have hB2 : 0 < ‖sourceCompletion hW 1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hB)
  have hsum (S : Finset ℕ) :
      ∑ p ∈ S, primeDeletionDeviationEnergy r p ≤ V / ‖sourceCompletion hW 1‖ ^ 2 := by
    apply (le_div_iff₀ hB2).mpr
    have ht := hb (S.filter Nat.Prime) (fun _ hp => (Finset.mem_filter.mp hp).2)
    rw [Finset.sum_filter] at ht
    simpa only [primeDeletionDeviationEnergy, mul_comm] using ht
  have hs : Summable (primeDeletionDeviationEnergy r) :=
    summable_of_sum_le (primeDeletionDeviationEnergy_nonneg r) hsum
  refine ⟨V, r, hV0, hV, hr, hs, ?_⟩
  have ht := (le_div_iff₀ hB2).mp
    (Real.tsum_le_of_sum_le (primeDeletionDeviationEnergy_nonneg r) hsum)
  simpa only [mul_comm] using ht

end RHTower.WeilSingularArithmetic
