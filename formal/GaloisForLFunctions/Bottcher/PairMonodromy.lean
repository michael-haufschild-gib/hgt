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
import GaloisForLFunctions.Bottcher.SectionTowerStep

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

namespace Bottcher

/-- **The period doubling.**  Once the loop's `n`-th iterate image is in the crude far field,
the `dlog` period of `φ_c ∘ f_c^[n+1]` is exactly twice that of `φ_c ∘ f_c^[n]` — the Böttcher
functional equation at the level of logarithmic derivatives. -/
theorem period_logDeriv_double (c : ℂ) (ℓ : C1Loop) (n : ℕ)
    (hfar : ∀ θ : ℝ, (quadratic c)^[n] (ℓ.γ θ) ∈ escapeOpen c) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun z => bottcherCoord c ((quadratic c)^[n+1] z)) (ℓ.γ θ) * ℓ.γ' θ)
      = 2 * ∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv (fun z => bottcherCoord c ((quadratic c)^[n] z)) (ℓ.γ θ) * ℓ.γ' θ := by
  have hquad_an : ∀ j : ℕ, ∀ z : ℂ, AnalyticAt ℂ ((quadratic c)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simpa using analyticAt_id
    | succ m ih =>
        intro z
        have h1 : (quadratic c)^[m+1] = (quadratic c)^[m] ∘ quadratic c := by
          rw [Function.iterate_succ]
        rw [h1]
        have h2 : AnalyticAt ℂ (quadratic c) z := by
          unfold quadratic
          exact (analyticAt_id.pow 2).add analyticAt_const
        exact (ih (quadratic c z)).comp h2
  have hcongr : ∀ θ : ℝ,
      logDeriv (fun z => bottcherCoord c ((quadratic c)^[n+1] z)) (ℓ.γ θ)
      = 2 * logDeriv (fun z => bottcherCoord c ((quadratic c)^[n] z)) (ℓ.γ θ) := by
    intro θ
    -- near the loop point, the (n+1)-composite is the square of the n-composite
    have hopen : IsOpen {z : ℂ | (quadratic c)^[n] z ∈ escapeOpen c} := by
      have h1 : Continuous ((quadratic c)^[n]) := by
        rw [continuous_iff_continuousAt]
        intro z
        exact (hquad_an n z).continuousAt
      exact (isOpen_escapeOpen c).preimage h1
    have hev : (fun z => bottcherCoord c ((quadratic c)^[n+1] z))
        =ᶠ[nhds (ℓ.γ θ)] (fun z => bottcherCoord c ((quadratic c)^[n] z) ^ 2) := by
      filter_upwards [hopen.mem_nhds (hfar θ)] with z hz
      have h1 : (quadratic c)^[n+1] z = quadratic c ((quadratic c)^[n] z) := by
        rw [Function.iterate_succ_apply']
      rw [h1]
      have h2 : max 2 ‖c‖ < ‖(quadratic c)^[n] z‖ := hz
      exact bottcherCoord_quadratic
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) h2))
        (lt_of_le_of_lt (le_max_left _ _) h2)
    rw [logDeriv_congr_of_eventuallyEq hev]
    have hdiff : DifferentiableAt ℂ (fun z => bottcherCoord c ((quadratic c)^[n] z))
        (ℓ.γ θ) := by
      have h1 : AnalyticAt ℂ (bottcherCoord c) ((quadratic c)^[n] (ℓ.γ θ)) :=
        (differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c) _ (hfar θ)
      exact (h1.comp (hquad_an n (ℓ.γ θ))).differentiableAt
    rw [logDeriv_fun_pow hdiff]
    push_cast
    ring
  have hsplit : ∀ θ : ℝ,
      logDeriv (fun z => bottcherCoord c ((quadratic c)^[n+1] z)) (ℓ.γ θ) * ℓ.γ' θ
      = 2 * (logDeriv (fun z => bottcherCoord c ((quadratic c)^[n] z)) (ℓ.γ θ) * ℓ.γ' θ) := by
    intro θ
    rw [hcongr θ]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ)]
  rw [intervalIntegral.integral_const_mul]

end Bottcher
