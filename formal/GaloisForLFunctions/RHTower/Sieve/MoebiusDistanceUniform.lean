import GaloisForLFunctions.RHTower.Sieve.MoebiusDistanceHighFreq
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSumSharp

/-!
# Matomäki–Radziwiłł's Lemma 2 for the Möbius character

The two halves of the frequency range meet: the three-four-one bound of
`Sieve/PrimeCosineSumSharp` covers `log|t| ≤ (log z)^{0.8}` and the Granville–Soundararajan tail of
`Sieve/MoebiusDistanceHighFreq` covers `(log z)^{0.6} ≤ log|t| ≤ 2 log z`.  Together they give a
pretentious lower bound that is a fixed proportion of `log log z` for every `9 ≤ |t| ≤ z²`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **Matomäki–Radziwiłł's Lemma 2 for `μ`, at `κ = 9/10`.** -/
theorem exists_mulDistSqPair_ge_full :
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
        9 ≤ |t| → Real.log |t| ≤ 2 * Real.log (z : ℝ) →
        (∀ p ∈ Nat.primesLE z, f p = -1) →
        0.01 * Real.log (Real.log (z : ℝ)) - C₀
          ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨A, delta, C, C₀, hdelta, hC, hhigh⟩ := exists_mulDistSqPair_ge_highFreq
  obtain ⟨Cq, hq⟩ := exists_mulDistSqPair_ge_quarter
  refine ⟨A, delta, C, max C₀ Cq, hdelta, hC, ?_⟩
  intro z t f hz2 hLz1 hcon htru hcheb hinv hgro hpi ht9 hthi hf
  have hLz0 : (0 : ℝ) < Real.log (z : ℝ) := by linarith
  have hloglogz : (0 : ℝ) ≤ Real.log (Real.log (z : ℝ)) := Real.log_nonneg hLz1
  have hlt0 : (0 : ℝ) < Real.log |t| := by
    have h8 : (8 : ℝ) ≤ |t| := by linarith
    have := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by linarith : (2:ℝ) ≤ |t|)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  rcases le_or_gt (Real.log |t|) ((Real.log (z : ℝ)) ^ (0.8 : ℝ)) with hlow | hhigh'
  · -- the three-four-one range
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
    have hbase := hq f z t hz3 ht9 hf
    have hll : Real.log (Real.log |t|) ≤ 0.8 * Real.log (Real.log (z : ℝ)) := by
      have h1 : Real.log (Real.log |t|)
          ≤ Real.log ((Real.log (z : ℝ)) ^ (0.8 : ℝ)) := Real.log_le_log hlt0 hlow
      rwa [Real.log_rpow hLz0] at h1
    have hlogLz : logLog z = Real.log (Real.log (z : ℝ)) := rfl
    rw [hlogLz] at hbase
    have hmax : Cq ≤ max C₀ Cq := le_max_right _ _
    linarith [hbase, hll, hloglogz, hmax]
  · -- the Granville–Soundararajan range
    have h68 : (Real.log (z : ℝ)) ^ (0.6 : ℝ) ≤ (Real.log (z : ℝ)) ^ (0.8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLz1 (by norm_num)
    have htlo : (Real.log (z : ℝ)) ^ (0.6 : ℝ) ≤ Real.log |t| := by linarith
    have hbase := hhigh z t f hz2 hLz1 hcon htru hcheb hinv hgro hpi htlo hthi hf
    have hmax : C₀ ≤ max C₀ Cq := le_max_left _ _
    linarith [hbase, hmax]

end

end RHTower.Sieve
