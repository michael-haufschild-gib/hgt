import GaloisForLFunctions.RHTower.Sieve.GSTailMass

/-!
# The pretentious distance at high frequency

Route (b) of Matomäki–Radziwiłł's Lemma 2: for frequencies with
`(log z)^{0.6} ≤ log|t| ≤ 2 log z` the Granville–Soundararajan tail is bounded by `1`
(`Sieve/GSTailAssembly`), the surviving harmonic mass is `0.01·log log z − O(1)`
(`Sieve/GSTailMass`), and the distance dominates their sum (`Sieve/MoebiusDistanceTail`).
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- **The pretentious distance at high frequency.** -/
theorem exists_mulDistSqPair_ge_highFreq :
    ∃ A delta C C₀ : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (z : ℕ) (t : ℝ) (f : ℕ → ℂ), 2 ≤ z → 1 ≤ Real.log (z : ℝ) →
        Real.log (9 * C * (1 + (4 + 2 * Real.log (z : ℝ)) * routeTBudgetHat A (Real.log (z : ℝ))
              + 2 * Real.log (z : ℝ)) * (9 * (2 + Real.log (z : ℝ))))
            * (6 * routeTBudgetHat A (Real.log (z : ℝ)))
          ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) →
        routeTTruncHat (Real.log (z : ℝ)) * Real.log (z : ℝ)
            + Real.log (9 * C * (3 : ℝ) ^ routeTTruncHat (Real.log (z : ℝ))
                * (2 + (Real.log (z : ℝ)) ^ (2 : ℕ) + (4 + 2 * Real.log (z : ℝ))
                    * routeTBudgetHat A (Real.log (z : ℝ)))
                * (9 * (2 + Real.log (z : ℝ))))
          ≤ (Real.log (z : ℝ)) ^ (0.6 : ℝ) →
        Real.log (216 * (2 + Real.log (z : ℝ))) ≤ (Real.log (z : ℝ)) ^ (0.99 : ℝ) / 4 →
        1 / routeTBudgetHat A (Real.log (z : ℝ)) ≤ delta →
        126 * Real.exp 9 * (2 + Real.log (z : ℝ))
          ≤ Real.exp ((Real.log (z : ℝ)) ^ (0.99 : ℝ)) →
        Real.log (16 * Real.pi / 3) ≤ (Real.log (z : ℝ)) ^ (0.6 : ℝ) →
        (Real.log (z : ℝ)) ^ (0.6 : ℝ) ≤ Real.log |t| →
        Real.log |t| ≤ 2 * Real.log (z : ℝ) →
        (∀ p ∈ Nat.primesLE z, f p = -1) →
        0.01 * Real.log (Real.log (z : ℝ)) - C₀
          ≤ mulDistSqPair f (charFn t) (Nat.primesLE z) := by
  obtain ⟨A, delta, C, hdelta, hC, htail⟩ := exists_abs_sum_cos_div_gsRange_le
  refine ⟨A, delta, C,
    mertensSecondLowerConst + mertensSecondUpperConst + Real.log 2 + 1, hdelta, hC, ?_⟩
  intro z t f hz2 hLz1 hcon htru hcheb hinv hgro hpi htlo hthi hf
  have hzpos : 0 < z := by omega
  have hyz : gsCutoff z ≤ z := gsCutoff_le hLz1 hzpos
  have hbound := htail z t hz2 hLz1 hcon htru hcheb hinv hgro hpi htlo hthi
  have hcos : (-1 : ℝ)
      ≤ ∑ p ∈ primesRange (gsCutoff z) z, Real.cos (t * Real.log (p : ℝ)) / (p : ℝ) := by
    have := abs_le.1 hbound
    linarith [this.1]
  have hmass := gs_tail_mass_ge hLz1 hz2
  have hdist := mulDistSqPair_ge_tail (f := f) hyz hf t
  linarith [hdist, hmass, hcos]

end

end RHTower.Sieve
