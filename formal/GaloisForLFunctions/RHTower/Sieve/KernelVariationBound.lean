import GaloisForLFunctions.RHTower.Sieve.KernelDiffMonotone

/-!
# The smooth kernel rises and then falls

Assembling the turning point.  Either `kernelP` stays nonnegative on the whole range — and then the
smooth kernel is monotone — or it turns negative once, and by `neg_of_concave_of_neg` stays
negative, so the smooth kernel rises to that point and falls after.  That is the hypothesis pair of
`variation_le_two_range_of_bimonotone`, whence

```text
∑_j |kernelDiff(j+2) − kernelDiff(j+1)| ≤ 2·(U − L)
```

for any bounds `L ≤ kernelDiff ≤ U` on the range.  On `[√x/2, √x + h]` the smooth kernel lies in
`[−1, 2h]`, so its variation is `O(h)` — the input `abs_weighted_correlation_le` needs.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The smooth kernel rises and then falls.** -/
theorem kernelDiff_bimonotone {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∃ c ≤ N,
      (∀ i, i + 1 ≤ c → kernelDiff x h k (i + 1) ≤ kernelDiff x h k (i + 1 + 1))
        ∧ (∀ i, c ≤ i → i + 1 ≤ N →
            kernelDiff x h k (i + 1 + 1) ≤ kernelDiff x h k (i + 1)) := by
  classical
  have hsign : ∀ j, 0 ≤ kernelP x h k (j + 1) →
      kernelDiff x h k (j + 1) ≤ kernelDiff x h k (j + 1 + 1) := by
    intro j hP
    exact kernelDiff_mono_of_nonneg (by omega) hk hP
  have hsign' : ∀ j, kernelP x h k (j + 1) ≤ 0 →
      kernelDiff x h k (j + 1 + 1) ≤ kernelDiff x h k (j + 1) := by
    intro j hP
    exact kernelDiff_anti_of_nonpos (by omega) hk hP
  by_cases hall : ∀ j, j < N → 0 ≤ kernelP x h k (j + 1)
  · -- monotone throughout: the turning point is the right endpoint
    refine ⟨N, le_rfl, ?_, ?_⟩
    · intro i hi
      exact hsign i (hall i (by omega))
    · intro i hci hin
      omega
  · -- a first negative index exists, and the sign never returns
    simp only [not_forall, not_le] at hall
    obtain ⟨j₀, hj₀N, hj₀⟩ := hall
    have hex : ∃ j, kernelP x h k (j + 1) < 0 := ⟨j₀, hj₀⟩
    set c := Nat.find hex with hcdef
    have hcneg : kernelP x h k (c + 1) < 0 := Nat.find_spec hex
    have hcmin : ∀ j, j < c → 0 ≤ kernelP x h k (j + 1) := by
      intro j hj
      have := Nat.find_min hex hj
      linarith [not_lt.1 this]
    have hafter : ∀ m, c ≤ m → kernelP x h k (m + 1) < 0 := by
      intro m hm
      have hconc : ∀ n, kernelP x h k (n + 2) - kernelP x h k (n + 1)
          ≤ kernelP x h k (n + 1) - kernelP x h k n := fun n => kernelP_concave hx hh k n
      have h0 : 0 ≤ kernelP x h k 0 := kernelP_zero_nonneg hx k
      exact neg_of_concave_of_neg hconc h0 hcneg (m + 1) (by omega)
    refine ⟨min c N, min_le_right _ _, ?_, ?_⟩
    · intro i hi
      exact hsign i (hcmin i (by omega))
    · intro i hci hin
      exact hsign' i (le_of_lt (hafter i (by omega)))

/-- **The smooth kernel's variation is at most twice its range.** -/
theorem kernelDiff_variation_le {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k)
    (N : ℕ) {L U : ℝ}
    (hL : ∀ j, j ≤ N → L ≤ kernelDiff x h k (j + 1))
    (hU : ∀ j, j ≤ N → kernelDiff x h k (j + 1) ≤ U) :
    ∑ j ∈ Finset.range N, |kernelDiff x h k (j + 2) - kernelDiff x h k (j + 1)|
      ≤ 2 * (U - L) := by
  classical
  set w : ℕ → ℝ := fun j => kernelDiff x h k (j + 1) with hwdef
  have hgoal : ∑ j ∈ Finset.range N, |kernelDiff x h k (j + 2) - kernelDiff x h k (j + 1)|
      = ∑ j ∈ Finset.range N, |w (j + 1) - w j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hwdef]
  rw [hgoal]
  obtain ⟨c, hcN, h1, h2⟩ := kernelDiff_bimonotone hx hh hk N
  exact variation_le_two_range_of_bimonotone (w := w) (c := c) hcN h1 h2 hL hU

end RHTower.Sieve

end
