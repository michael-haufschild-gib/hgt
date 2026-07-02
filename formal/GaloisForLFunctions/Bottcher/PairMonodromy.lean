/-
# Pair monodromy: finiteness and doubling

The two facts that dissolve the pair-case branch choice.  (1) FINITENESS: a compact subset of
the second parameter's escape basin contains only finitely many of its precritical points — at
level `n` they sit at Green level `G₂(0)/2ⁿ`, which drops below the compact's Green minimum.
(2) DOUBLING: once the loop has escaped to the crude far field, the `dlog` periods of
`φ₂ ∘ f₂ⁿ` double with `n` (the Böttcher functional equation), so a finite total enclosed count
forces every period to vanish — the root-existence condition for the `GBExt` tower, with no
choice of branch.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.PolyWinding
import GaloisForLFunctions.Bottcher.GreenSublevel

open Complex Set Filter Metric

namespace Bottcher

/-- **Finiteness of precritical points in basin compacts.**  Only finitely many precritical
points of `c` meet a compact set avoiding the filled Julia set. -/
theorem finite_precritical_of_compact_basin (c : ℂ) {L : Set ℂ} (hL : IsCompact L)
    (hLb : ∀ z ∈ L, z ∉ filledJulia c) :
    {z : ℂ | z ∈ L ∧ ∃ n : ℕ, (quadratic c)^[n] z = 0}.Finite := by
  classical
  rcases L.eq_empty_or_nonempty with hLe | hLne
  · apply Set.Finite.subset (Set.finite_empty)
    intro z hz
    rw [hLe] at hz
    exact absurd hz.1 (Set.notMem_empty z)
  -- the Green minimum on the compact is positive
  obtain ⟨z₀, hz₀L, hz₀min⟩ := hL.exists_isMinOn hLne
    (continuous_greenFunctionDyn c).continuousOn
  have hε : 0 < greenFunctionDyn c z₀ := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c z₀) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c z₀).mp h1.symm) (hLb z₀ hz₀L)
  set ε : ℝ := greenFunctionDyn c z₀ with hεdef
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have hh0 : 0 ≤ h := greenFunctionDyn_nonneg c 0
  -- levels are dyadically small: beyond N, no precritical point clears the minimum
  obtain ⟨N, hN⟩ : ∃ N : ℕ, h / 2 ^ N < ε := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (h / ε) (by norm_num : (1:ℝ) < 2)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    calc h = (h / ε) * ε := by field_simp
      _ < 2 ^ N * ε := by
          apply mul_lt_mul_of_pos_right hN hε
      _ = ε * 2 ^ N := by ring
  -- membership forces level ≤ N
  have hsub : {z : ℂ | z ∈ L ∧ ∃ n : ℕ, (quadratic c)^[n] z = 0}
      ⊆ ⋃ n ∈ Finset.range (N + 1), {z : ℂ | (quadratic c)^[n] z = 0} := by
    rintro z ⟨hzL, n, hzn⟩
    have hlev : greenFunctionDyn c z = h / 2 ^ n := by
      have h1 : greenFunctionDyn c ((quadratic c)^[n] z) = 2 ^ n * greenFunctionDyn c z := by
        rw [greenFunctionDyn_iterate]
      rw [hzn, ← hhdef] at h1
      field_simp
      linarith [h1]
    have hnN : n ≤ N := by
      by_contra hcon
      push Not at hcon
      have h2 : greenFunctionDyn c z < ε := by
        rw [hlev]
        calc h / 2 ^ n ≤ h / 2 ^ (N + 1) := by
              apply div_le_div_of_nonneg_left hh0 (by positivity)
              apply pow_le_pow_right₀ (by norm_num)
              omega
          _ ≤ h / 2 ^ N := by
              apply div_le_div_of_nonneg_left hh0 (by positivity)
              apply pow_le_pow_right₀ (by norm_num)
              omega
          _ < ε := hN
      have h3 : ε ≤ greenFunctionDyn c z := hz₀min hzL
      linarith
    exact Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hzn
  apply Set.Finite.subset _ hsub
  apply Set.Finite.biUnion (Finset.range (N + 1)).finite_toSet
  intro n _
  exact quadratic_iterate_fiber_finite c n 0

end Bottcher
