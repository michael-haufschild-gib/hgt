import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceUniform
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleBoxLowerBound

/-!
# The pretentious distance at every frequency below `z²`

Below `|t| = 9` the compactness bound across the pole
(`Sieve/ZetaPoleBoxLowerBound.exists_sum_cos_div_prime_ge_small`) costs only an absolute constant, so
the distance is `log log z − O(1)` there; above it the two halves of
`Sieve/MoebiusDistanceUniform` apply.  The result is the uniform lower bound that the corpus's
Halász machinery consumes.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The pretentious distance, uniformly over `|t| ≤ z²`.** -/
theorem exists_mulDistSqPair_ge_allFreq :
    ∃ A delta C C₀ : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (z : ℕ) (t : ℝ) (f : ℕ → ℂ), 2 ≤ z → 1 ≤ Real.log (z : ℝ) →
        Real.log (9 * C * (1 + (4 + 2 * Real.log (z : ℝ)) * routeTBudgetHat A (Real.log (z : ℝ))
              + 2 * Real.log (z : ℝ)) * (9 * (2 + Real.log (z : ℝ))))
            * (6 * routeTBudgetHat A (Real.log (z : ℝ)))
          ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) →
        routeTTruncHat (Real.log (z : ℝ)) * Real.log (z : ℝ)
            + Real.log (9 * C * (3 : ℝ) ^ routeTTruncHat (Real.log (z : ℝ))
                * (2 + (Real.log (z : ℝ)) ^ 2 + (4 + 2 * Real.log (z : ℝ))
                    * routeTBudgetHat A (Real.log (z : ℝ)))
                * (9 * (2 + Real.log (z : ℝ))))
          ≤ (Real.log (z : ℝ)) ^ (0.6 : ℝ) →
        Real.log (216 * (2 + Real.log (z : ℝ))) ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) / 4 →
        1 / routeTBudgetHat A (Real.log (z : ℝ)) ≤ delta →
        126 * Real.exp 9 * (2 + Real.log (z : ℝ))
          ≤ Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) →
        Real.log (16 * Real.pi / 3) ≤ (Real.log (z : ℝ)) ^ (0.6 : ℝ) →
        Real.log |t| ≤ 2 * Real.log (z : ℝ) →
        (∀ p ∈ Nat.primesLE z, f p = -1) →
        0.01 * Real.log (Real.log (z : ℝ)) - C₀
          ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨A, delta, C, C₀, hdelta, hC, hfull⟩ := exists_mulDistSqPair_ge_full
  obtain ⟨Cs, hs⟩ := exists_sum_cos_div_prime_ge_small
  refine ⟨A, delta, C, max C₀ (Cs + mertensSecondLowerConst), hdelta, hC, ?_⟩
  intro z t f hz2 hLz1 hcon htru hcheb hinv hgro hpi hthi hf
  have hLz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hloglogz : (0 : ℝ) ≤ Real.log (Real.log (z : ℝ)) := Real.log_nonneg hLz1
  rcases le_or_gt |t| 9 with hsmall | hbig
  · -- the pole box
    have hz3 : 3 ≤ z := by
      have hzpos : (0 : ℝ) < (z : ℝ) := by
        have : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
        linarith
      have hexp : Real.exp 1 ≤ (z : ℝ) := by
        have h := Real.exp_le_exp.2 hLz1
        rwa [Real.exp_log hzpos] at h
      have he : (2 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have h2z : (2 : ℝ) < (z : ℝ) := by linarith
      have : 2 < z := by exact_mod_cast h2z
      omega
    have hcos := hs z hz3 t hsmall
    have hmertens : logLog z - mertensSecondLowerConst ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
      le_mertensS (by omega)
    have hlogLz : logLog z = Real.log (Real.log (z : ℝ)) := rfl
    rw [hlogLz] at hmertens
    rw [mulDistSqPair_neg_one_split hf t]
    have hmax : Cs + mertensSecondLowerConst ≤ max C₀ (Cs + mertensSecondLowerConst) :=
      le_max_right _ _
    linarith [hcos, hmertens, hloglogz, hmax]
  · have hbase := hfull z t f hz2 hLz1 hcon htru hcheb hinv hgro hpi hbig.le hthi hf
    have hmax : C₀ ≤ max C₀ (Cs + mertensSecondLowerConst) := le_max_left _ _
    linarith [hbase, hmax]

end

end RHTower.Sieve
