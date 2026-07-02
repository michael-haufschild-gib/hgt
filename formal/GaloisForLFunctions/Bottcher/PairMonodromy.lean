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

namespace Bottcher

/-- **The period value.**  Far enough out, composing with the Böttcher coordinate does not
change the `dlog` period: `φ_c/z` stays in the right half-plane, so its log is exact and its
period telescopes to zero.  Hence `∮ dlog (φ_c ∘ f^[n]) = ∮ dlog (f^[n])` — the winding sum over
the level-`n` preimages of `0`. -/
theorem exists_period_value_threshold (c : ℂ) :
    ∃ M₀ : ℝ, max 2 ‖c‖ < M₀ ∧
    ∀ (ℓ : C1Loop) (n : ℕ), (∀ θ : ℝ, M₀ < ‖(quadratic c)^[n] (ℓ.γ θ)‖) →
      (∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv (fun z => bottcherCoord c ((quadratic c)^[n] z)) (ℓ.γ θ) * ℓ.γ' θ)
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ) * ℓ.γ' θ := by
  classical
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, ∀ z : ℂ, M₁ < ‖z‖ → ‖bottcherCoord c z - z‖ < 1 := by
    have h := (tendsto_bottcherCoord_sub_id c).eventually
      (Metric.ball_mem_nhds (0:ℂ) one_pos)
    rw [← comap_norm_atTop, eventually_comap] at h
    obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp h
    refine ⟨M₁, fun z hz => ?_⟩
    have := hM₁ ‖z‖ (le_of_lt hz) z rfl
    rwa [dist_zero_right] at this
  set M₀ : ℝ := max (max 2 ‖c‖ + 1) (max M₁ 2) with hM₀def
  have hM₀c : max 2 ‖c‖ < M₀ := by
    have h1 : max 2 ‖c‖ + 1 ≤ M₀ := le_max_left _ _
    linarith
  have hM₀M₁ : M₁ ≤ M₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₀2 : (2:ℝ) ≤ M₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨M₀, hM₀c, ?_⟩
  intro ℓ n hfar
  -- the unit-comparison u := φ/z on the far region
  set u : ℂ → ℂ := fun z => bottcherCoord c z / z with hudef
  have hune : ∀ z : ℂ, M₀ < ‖z‖ → ‖u z - 1‖ < 1 / 2 := by
    intro z hz
    have hzne : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz
      linarith
    have h1 : u z - 1 = (bottcherCoord c z - z) / z := by
      rw [hudef]
      field_simp
    rw [h1, norm_div]
    have h2 : ‖bottcherCoord c z - z‖ < 1 := hM₁ z (lt_of_le_of_lt hM₀M₁ hz)
    have h3 : (2:ℝ) < ‖z‖ := lt_of_le_of_lt (by linarith) hz
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have huslit : ∀ z : ℂ, M₀ < ‖z‖ → u z ∈ Complex.slitPlane := by
    intro z hz
    have h : ‖u z - 1‖ < 1 / 2 := hune z hz
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 : |(u z - 1).re| ≤ ‖u z - 1‖ := Complex.abs_re_le_norm (u z - 1)
    have h2 : (u z - 1).re = (u z).re - 1 := by simp [Complex.sub_re]
    rw [h2] at h1
    have h3 : |(u z).re - 1| < 1 / 2 := lt_of_le_of_lt h1 h
    have h4 := abs_lt.mp h3
    linarith [h4.1]
  have hune0 : ∀ z : ℂ, M₀ < ‖z‖ → u z ≠ 0 := by
    intro z hz h0
    have h1 := hune z hz
    rw [h0] at h1
    simp only [zero_sub, norm_neg, norm_one] at h1
    linarith
  -- u is analytic on the far region
  have hu_an : ∀ z : ℂ, M₀ < ‖z‖ → AnalyticAt ℂ u z := by
    intro z hz
    have hzne : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz
      linarith
    have hφ : AnalyticAt ℂ (bottcherCoord c) z :=
      (differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c) z
        (lt_trans hM₀c hz)
    exact hφ.div analyticAt_id hzne
  -- iterates are analytic everywhere (again)
  have hquad_an : ∀ j : ℕ, ∀ z : ℂ, AnalyticAt ℂ ((quadratic c)^[j]) z := by
    intro j
    induction j with
    | zero => intro z; simpa using analyticAt_id
    | succ m ih =>
        intro z
        have h1 : (quadratic c)^[m+1] = (quadratic c)^[m] ∘ quadratic c := by
          rw [Function.iterate_succ]
        rw [h1]
        exact (ih (quadratic c z)).comp (by
          unfold quadratic
          exact (analyticAt_id.pow 2).add analyticAt_const)
  -- pointwise decomposition of the integrand
  have hne0 : ∀ θ : ℝ, (quadratic c)^[n] (ℓ.γ θ) ≠ 0 := by
    intro θ h0
    have := hfar θ
    rw [h0, norm_zero] at this
    linarith
  have hφcomp_diff : ∀ θ : ℝ,
      DifferentiableAt ℂ (fun z => bottcherCoord c ((quadratic c)^[n] z)) (ℓ.γ θ) := by
    intro θ
    have h1 : AnalyticAt ℂ (bottcherCoord c) ((quadratic c)^[n] (ℓ.γ θ)) :=
      (differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c) _
        (lt_trans hM₀c (hfar θ))
    exact (h1.comp (hquad_an n (ℓ.γ θ))).differentiableAt
  have hsplit : ∀ θ : ℝ,
      logDeriv (fun z => bottcherCoord c ((quadratic c)^[n] z)) (ℓ.γ θ) * ℓ.γ' θ
      = logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ) * ℓ.γ' θ
        + logDeriv u ((quadratic c)^[n] (ℓ.γ θ))
            * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ) := by
    intro θ
    -- φ ∘ f^[n] = (u ∘ f^[n]) · f^[n] pointwise near the loop
    have hev : (fun z => bottcherCoord c ((quadratic c)^[n] z))
        =ᶠ[nhds (ℓ.γ θ)] (fun z => u ((quadratic c)^[n] z) * (quadratic c)^[n] z) := by
      have hopen : IsOpen {z : ℂ | M₀ < ‖(quadratic c)^[n] z‖} := by
        have hcont : Continuous ((quadratic c)^[n]) := by
          rw [continuous_iff_continuousAt]
          intro z
          exact (hquad_an n z).continuousAt
        exact isOpen_lt continuous_const (continuous_norm.comp hcont)
      filter_upwards [hopen.mem_nhds (hfar θ)] with z hz
      have hzne : (quadratic c)^[n] z ≠ 0 := by
        intro h0
        have : M₀ < ‖(quadratic c)^[n] z‖ := hz
        rw [h0, norm_zero] at this
        linarith
      rw [hudef]
      field_simp
    rw [logDeriv_congr_of_eventuallyEq hev]
    have h1 : logDeriv (fun z => u ((quadratic c)^[n] z) * (quadratic c)^[n] z) (ℓ.γ θ)
        = logDeriv (fun z => u ((quadratic c)^[n] z)) (ℓ.γ θ)
          + logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ) :=
      logDeriv_mul (ℓ.γ θ) (hune0 _ (hfar θ)) (hne0 θ)
        ((hu_an _ (hfar θ)).comp (hquad_an n (ℓ.γ θ))).differentiableAt
        (hquad_an n (ℓ.γ θ)).differentiableAt
    have h2 : logDeriv (fun z => u ((quadratic c)^[n] z)) (ℓ.γ θ)
        = logDeriv u ((quadratic c)^[n] (ℓ.γ θ)) * deriv ((quadratic c)^[n]) (ℓ.γ θ) := by
      have h3 : (fun z => u ((quadratic c)^[n] z)) = u ∘ (quadratic c)^[n] := rfl
      rw [h3]
      exact logDeriv_comp (hu_an _ (hfar θ)).differentiableAt
        (hquad_an n (ℓ.γ θ)).differentiableAt
    rw [h1, h2]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ)]
  rw [intervalIntegral.integral_add]
  · -- the u-term telescopes to zero via the exact logarithm
    have hcont_all : Continuous (fun θ => logDeriv u ((quadratic c)^[n] (ℓ.γ θ))
        * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ)) := by
      have hγn : Continuous (fun θ => (quadratic c)^[n] (ℓ.γ θ)) := by
        have h1 : Continuous ((quadratic c)^[n]) := by
          rw [continuous_iff_continuousAt]
          intro z
          exact (hquad_an n z).continuousAt
        exact h1.comp ℓ.cont
      have h2 : Continuous (fun θ => logDeriv u ((quadratic c)^[n] (ℓ.γ θ))) := by
        rw [continuous_iff_continuousAt]
        intro θ
        have h3 : ContinuousAt (logDeriv u) ((quadratic c)^[n] (ℓ.γ θ)) := by
          have h4 : AnalyticAt ℂ u ((quadratic c)^[n] (ℓ.γ θ)) := hu_an _ (hfar θ)
          have h5 : (fun w => logDeriv u w) =ᶠ[nhds ((quadratic c)^[n] (ℓ.γ θ))]
              (fun w => deriv u w / u w) := by
            filter_upwards with w
            rw [logDeriv_apply]
          rw [continuousAt_congr h5]
          exact (h4.deriv.continuousAt).div h4.continuousAt (hune0 _ (hfar θ))
        exact ContinuousAt.comp (x := θ) (g := logDeriv u)
          (f := fun t => (quadratic c)^[n] (ℓ.γ t)) h3 (hγn.continuousAt)
      have h6 : Continuous (fun θ => deriv ((quadratic c)^[n]) (ℓ.γ θ)) := by
        have h7 : Continuous (deriv ((quadratic c)^[n])) := by
          rw [continuous_iff_continuousAt]
          intro z
          exact (hquad_an n z).deriv.continuousAt
        exact h7.comp ℓ.cont
      exact h2.mul (h6.mul ℓ.cont')
    have hzero : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv u ((quadratic c)^[n] (ℓ.γ θ))
          * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ)) = 0 := by
      set Lg : ℝ → ℂ := fun θ => Complex.log (u ((quadratic c)^[n] (ℓ.γ θ))) with hLgdef
      have hLd : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
          HasDerivAt Lg (logDeriv u ((quadratic c)^[n] (ℓ.γ θ))
            * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ)) θ := by
        intro θ hθ
        have hθI : θ ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
          rwa [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at hθ
        have hγd : HasDerivAt ℓ.γ (ℓ.γ' θ) θ := ℓ.deriv θ hθI
        have hfd : HasDerivAt ((quadratic c)^[n])
            (deriv ((quadratic c)^[n]) (ℓ.γ θ)) (ℓ.γ θ) :=
          (hquad_an n (ℓ.γ θ)).differentiableAt.hasDerivAt
        have hcomp1 : HasDerivAt (fun t => (quadratic c)^[n] (ℓ.γ t))
            (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ) θ := hfd.comp θ hγd
        have hud : HasDerivAt u (deriv u ((quadratic c)^[n] (ℓ.γ θ)))
            ((quadratic c)^[n] (ℓ.γ θ)) := (hu_an _ (hfar θ)).differentiableAt.hasDerivAt
        have hcomp2 : HasDerivAt (fun t => u ((quadratic c)^[n] (ℓ.γ t)))
            (deriv u ((quadratic c)^[n] (ℓ.γ θ))
              * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ)) θ := by
          have h8 := HasDerivAt.comp (h₂ := u) θ hud hcomp1
          exact h8
        have hlogd : HasDerivAt Complex.log (u ((quadratic c)^[n] (ℓ.γ θ)))⁻¹
            (u ((quadratic c)^[n] (ℓ.γ θ))) :=
          Complex.hasDerivAt_log (huslit _ (hfar θ))
        have htotal := hlogd.comp θ hcomp2
        have hval : (u ((quadratic c)^[n] (ℓ.γ θ)))⁻¹
            * (deriv u ((quadratic c)^[n] (ℓ.γ θ))
              * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ))
            = logDeriv u ((quadratic c)^[n] (ℓ.γ θ))
              * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ) := by
          rw [logDeriv_apply]
          field_simp
        rw [← hval]
        exact htotal
      have hint : IntervalIntegrable (fun θ => logDeriv u ((quadratic c)^[n] (ℓ.γ θ))
          * (deriv ((quadratic c)^[n]) (ℓ.γ θ) * ℓ.γ' θ))
          MeasureTheory.volume (0:ℝ) (2 * Real.pi) :=
        hcont_all.intervalIntegrable _ _
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hLd hint
      rw [hFTC]
      have hclosed : Lg (2 * Real.pi) = Lg 0 := by
        rw [hLgdef]
        show Complex.log (u ((quadratic c)^[n] (ℓ.γ (2 * Real.pi))))
          = Complex.log (u ((quadratic c)^[n] (ℓ.γ 0)))
        rw [ℓ.closed]
      rw [hclosed]
      ring
    rw [hzero]
    ring
  · -- integrability of the iterate-dlog integrand
    apply Continuous.intervalIntegrable
    have hγn : Continuous (fun θ => (quadratic c)^[n] (ℓ.γ θ)) := by
      have h1 : Continuous ((quadratic c)^[n]) := by
        rw [continuous_iff_continuousAt]
        intro z
        exact (hquad_an n z).continuousAt
      exact h1.comp ℓ.cont
    have h2 : Continuous (fun θ => logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ)) := by
      have h3 : (fun θ => logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ))
          = fun θ => deriv ((quadratic c)^[n]) (ℓ.γ θ) / (quadratic c)^[n] (ℓ.γ θ) := by
        funext θ
        rw [logDeriv_apply]
      rw [h3]
      have h4 : Continuous (fun θ => deriv ((quadratic c)^[n]) (ℓ.γ θ)) := by
        have h5 : Continuous (deriv ((quadratic c)^[n])) := by
          rw [continuous_iff_continuousAt]
          intro z
          exact (hquad_an n z).deriv.continuousAt
        exact h5.comp ℓ.cont
      exact h4.div hγn hne0
    exact h2.mul ℓ.cont'
  · -- integrability of the u-term integrand
    apply Continuous.intervalIntegrable
    have hγn : Continuous (fun θ => (quadratic c)^[n] (ℓ.γ θ)) := by
      have h1 : Continuous ((quadratic c)^[n]) := by
        rw [continuous_iff_continuousAt]
        intro z
        exact (hquad_an n z).continuousAt
      exact h1.comp ℓ.cont
    have h2 : Continuous (fun θ => logDeriv u ((quadratic c)^[n] (ℓ.γ θ))) := by
      rw [continuous_iff_continuousAt]
      intro θ
      have h3 : ContinuousAt (logDeriv u) ((quadratic c)^[n] (ℓ.γ θ)) := by
        have h4 : AnalyticAt ℂ u ((quadratic c)^[n] (ℓ.γ θ)) := hu_an _ (hfar θ)
        have h5 : (fun w => logDeriv u w) =ᶠ[nhds ((quadratic c)^[n] (ℓ.γ θ))]
            (fun w => deriv u w / u w) := by
          filter_upwards with w
          rw [logDeriv_apply]
        rw [continuousAt_congr h5]
        exact (h4.deriv.continuousAt).div h4.continuousAt (hune0 _ (hfar θ))
      exact ContinuousAt.comp (x := θ) (g := logDeriv u)
        (f := fun t => (quadratic c)^[n] (ℓ.γ t)) h3 (hγn.continuousAt)
    have h6 : Continuous (fun θ => deriv ((quadratic c)^[n]) (ℓ.γ θ)) := by
      have h7 : Continuous (deriv ((quadratic c)^[n])) := by
        rw [continuous_iff_continuousAt]
        intro z
        exact (hquad_an n z).deriv.continuousAt
      exact h7.comp ℓ.cont
    exact h2.mul (h6.mul ℓ.cont')

end Bottcher

namespace Bottcher

/-- **The disjointness gap.**  When the filled Julia sets are disjoint, the second one sits at a
positive Green level of the first: below that level, nothing belongs to `K₂`. -/
theorem exists_green_gap_of_disjoint (c₁ c₂ : ℂ)
    (hdisj : ∀ z, z ∈ filledJulia c₂ → z ∉ filledJulia c₁) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ z : ℂ, greenFunctionDyn c₁ z ≤ ε₀ → z ∉ filledJulia c₂ := by
  classical
  rcases (filledJulia c₂).eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun z _ hz => by rw [hKe] at hz; exact absurd hz (Set.notMem_empty z)⟩
  obtain ⟨z₀, hz₀K, hz₀min⟩ := (isCompact_filledJulia c₂).exists_isMinOn hKne
    (continuous_greenFunctionDyn c₁).continuousOn
  have hz₀pos : 0 < greenFunctionDyn c₁ z₀ := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c₁ z₀) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c₁ z₀).mp h1.symm) (hdisj z₀ hz₀K)
  refine ⟨greenFunctionDyn c₁ z₀ / 2, by positivity, ?_⟩
  intro z hz hzK
  have h1 : greenFunctionDyn c₁ z₀ ≤ greenFunctionDyn c₁ z := hz₀min hzK
  linarith

/-- **Uniform escape.**  A compact set in the basin escapes uniformly: beyond some iterate,
the whole set is past any prescribed radius. -/
theorem exists_uniform_escape (c : ℂ) {L : Set ℂ} (hL : IsCompact L) (hLne : L.Nonempty)
    (hLb : ∀ z ∈ L, z ∉ filledJulia c) (M : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z ∈ L, M < ‖(quadratic c)^[n] z‖ := by
  classical
  obtain ⟨z₀, hz₀L, hz₀min⟩ := hL.exists_isMinOn hLne
    (continuous_greenFunctionDyn c).continuousOn
  have hε : 0 < greenFunctionDyn c z₀ := by
    rcases lt_or_eq_of_le (greenFunctionDyn_nonneg c z₀) with h1 | h1
    · exact h1
    · exact absurd ((greenFunctionDyn_eq_zero_iff c z₀).mp h1.symm) (hLb z₀ hz₀L)
  set ε : ℝ := greenFunctionDyn c z₀ with hεdef
  -- the Green bound on the crude ball
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ w : ℂ, ‖w‖ ≤ max 2 ‖c‖ → greenFunctionDyn c w ≤ Cb := by
    have hcpt : IsCompact {w : ℂ | ‖w‖ ≤ max 2 ‖c‖} := by
      have h1 : {w : ℂ | ‖w‖ ≤ max 2 ‖c‖} = Metric.closedBall 0 (max 2 ‖c‖) := by
        ext w
        simp [Metric.mem_closedBall, dist_zero_right]
      rw [h1]
      exact isCompact_closedBall 0 _
    rcases {w : ℂ | ‖w‖ ≤ max 2 ‖c‖}.eq_empty_or_nonempty with hbe | hbne
    · exact ⟨0, fun w hw => absurd (show w ∈ {w : ℂ | ‖w‖ ≤ max 2 ‖c‖} from hw)
        (by rw [hbe]; exact Set.notMem_empty w)⟩
    obtain ⟨w₀, _, hw₀max⟩ := hcpt.exists_isMaxOn hbne
      (continuous_greenFunctionDyn c).continuousOn
    exact ⟨greenFunctionDyn c w₀, fun w hw => hw₀max hw⟩
  -- choose N beyond both the ball bound and the norm target
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max Cb (Real.log (max M 1) + 1) < 2 ^ N * ε := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
      ((max Cb (Real.log (max M 1) + 1) + 1) / ε) (by norm_num : (1:ℝ) < 2)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ hε] at hN
    nlinarith
  refine ⟨N, ?_⟩
  intro n hn z hzL
  have hG : (2:ℝ) ^ n * ε ≤ greenFunctionDyn c ((quadratic c)^[n] z) := by
    rw [greenFunctionDyn_iterate]
    have h1 : ε ≤ greenFunctionDyn c z := hz₀min hzL
    have h2 : (0:ℝ) < 2 ^ n := by positivity
    nlinarith
  have hNn : (2:ℝ) ^ N * ε ≤ 2 ^ n * ε := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hε)
    apply pow_le_pow_right₀ (by norm_num) hn
  -- the iterate has left the crude ball
  have hfar : max 2 ‖c‖ < ‖(quadratic c)^[n] z‖ := by
    by_contra hcon
    push Not at hcon
    have h1 := hCb _ hcon
    have h2 : max Cb (Real.log (max M 1) + 1) < greenFunctionDyn c ((quadratic c)^[n] z) := by
      linarith
    have h3 : Cb ≤ max Cb (Real.log (max M 1) + 1) := le_max_left _ _
    linarith
  -- crude bound: the norm exceeds the target
  have hcrude := greenFunctionDyn_le_crude
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hfar))
    (lt_of_le_of_lt (le_max_left _ _) hfar)
  have h4 : Real.log (max M 1) < Real.log ‖(quadratic c)^[n] z‖ := by
    have h5 : Real.log (max M 1) + 1 ≤ max Cb (Real.log (max M 1) + 1) := le_max_right _ _
    linarith
  have h6 : max M 1 < ‖(quadratic c)^[n] z‖ := by
    have h7 : (0:ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h8 : (0:ℝ) < ‖(quadratic c)^[n] z‖ :=
      lt_trans (by norm_num) (lt_of_le_of_lt (le_max_left _ _) hfar)
    calc max M 1 = Real.exp (Real.log (max M 1)) := (Real.exp_log h7).symm
      _ < Real.exp (Real.log ‖(quadratic c)^[n] z‖) := Real.exp_lt_exp.mpr h4
      _ = ‖(quadratic c)^[n] z‖ := Real.exp_log h8
  exact lt_of_le_of_lt (le_max_left _ _) h6

end Bottcher

