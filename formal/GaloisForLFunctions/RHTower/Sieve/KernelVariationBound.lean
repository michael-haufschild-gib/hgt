import GaloisForLFunctions.RHTower.Sieve.KernelDiffMonotone

/-!
# The smooth kernel's variation is twice its range

Assembling the turning point.  Either `kernelP` stays nonnegative on the whole range — and then the
smooth kernel is monotone — or it turns negative once, and by `neg_of_concave_of_neg` stays
negative, so the smooth kernel rises to that point and falls after.  Either way
`variation_le_two_range_of_bimonotone` applies:

```text
∑_j |kernelDiff(j+2) − kernelDiff(j+1)| ≤ 2·(U − L)
```

for any bounds `L ≤ kernelDiff ≤ U` on the range.  On `[√x/2, √x + h]` the smooth kernel lies in
`[−1, 2h]`, so its variation is `O(h)` — the input `abs_weighted_correlation_le` needs.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

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
  -- the sign of `kernelP` at the shifted index
  have hsign : ∀ j, 0 ≤ kernelP x h k (j + 1) → w j ≤ w (j + 1) := by
    intro j hP
    exact kernelDiff_mono_of_nonneg (by omega) hk hP
  have hsign' : ∀ j, kernelP x h k (j + 1) ≤ 0 → w (j + 1) ≤ w j := by
    intro j hP
    exact kernelDiff_anti_of_nonpos (by omega) hk hP
  by_cases hall : ∀ j, j < N → 0 ≤ kernelP x h k (j + 1)
  · -- monotone throughout: take the turning point at the end
    refine variation_le_two_range_of_bimonotone (w := w) (c := N) le_rfl ?_ ?_ ?_ ?_
    · intro i hi
      exact hsign i (hall i (by omega))
    · intro i hci hin
      omega
    · intro i hi
      exact hL i hi
    · intro i hi
      exact hU i hi
  · -- a first negative index exists
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
    refine variation_le_two_range_of_bimonotone (w := w) (c := min c N)
      (min_le_right _ _) ?_ ?_ ?_ ?_
    · intro i hi
      exact hsign i (hcmin i (by omega))
    · intro i hci hin
      exact hsign' i (le_of_lt (hafter i (by omega)))
    · intro i hi
      exact hL i hi
    · intro i hi
      exact hU i hi

end RHTower.Sieve

end
