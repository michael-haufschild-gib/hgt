import GaloisForLFunctions.RHTower.ProlateHermiteTrialSpace
import GaloisForLFunctions.RHTower.HermiteWronskianDecayRate

/-!
# A rate for the off-diagonal Gram entries of the rescaled Hermite family

The Gram entry at the Hermite scale is the Hermite inner product truncated at `√c`, so the
truncated-orthogonality rate applies with `R = √c`.  Taking the fourth inverse power gives

```text
|hermiteTrialGram ν c i k|  ≤  K / c²        for `i ≠ k` and `c ≥ 1`,
```

with one constant `K` valid for every index pair.  This replaces the qualitative
`tendsto_hermiteTrialGram_off` wherever a threshold must be exhibited.
-/

noncomputable section

open Filter Topology

namespace RHTower

variable {j : ℕ}

/-- **The off-diagonal Gram entries are quadratically small in the bandwidth.** -/
theorem exists_bound_hermiteTrialGram_off (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ i k : Fin (j + 1), i ≠ k →
      |hermiteTrialGram ν c i k| ≤ K / c ^ (2 : ℕ) := by
  classical
  have hpair : ∀ p : Fin (j + 1) × Fin (j + 1), ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c →
      p.1 ≠ p.2 → |hermiteTrialGram ν c p.1 p.2| ≤ K / c ^ (2 : ℕ) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨0, le_rfl, fun c _ hne => absurd hp hne⟩
    · obtain ⟨K, hK0, hK⟩ :=
        exists_bound_integral_hermiteFun_mul (m := ν p.1) (n := ν p.2)
          (fun h => hp (hinj h)) 4
      refine ⟨K, hK0, fun c hc _ => ?_⟩
      have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
      have hs1 : (1 : ℝ) ≤ Real.sqrt c := by
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hc
      have h := hK (Real.sqrt c) hs1
      have hpow : Real.sqrt c ^ (4 : ℕ) = c ^ (2 : ℕ) := by
        have hsq : Real.sqrt c ^ (2 : ℕ) = c := Real.sq_sqrt hc0.le
        calc Real.sqrt c ^ (4 : ℕ) = (Real.sqrt c ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
          _ = c ^ (2 : ℕ) := by rw [hsq]
      rw [hpow] at h
      rw [hermiteTrialGram]
      exact h
  choose Kf hKf0 hKf using hpair
  obtain ⟨K, hK⟩ := Finite.exists_le Kf
  refine ⟨max K 0, le_max_right _ _, fun c hc i k hik => ?_⟩
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  have hle : Kf (i, k) ≤ max K 0 := le_trans (hK (i, k)) (le_max_left _ _)
  refine le_trans (hKf (i, k) c hc hik) ?_
  gcongr

end RHTower

end
