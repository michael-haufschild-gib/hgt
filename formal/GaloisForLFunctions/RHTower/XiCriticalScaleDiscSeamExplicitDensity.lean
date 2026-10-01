import GaloisForLFunctions.RHTower.XiCriticalScaleDiscSeamProportion
import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity

/-!
# Contracting seams on a fixed proportion of the right discs, at every scale

For `0 < r ≤ 1/8` the right discs `D_k` of radius `r` centred at `½ + 2r + 3rk·i` (`k = 1, …, K`)
lie in `½ + r ≤ Re s ≤ ½ + 3r`.  A disc containing a zero of `ξ` receives a zero `ρ` with
`Re ρ − ½ ≥ r`, different discs receive different zeros, and all these zeros lie in the box
`½ < Re ρ < 1`, `0 ≤ Im ρ ≤ 3rK + r`.  Hence

  `r · #{exceptional discs} ≤ Σ_{0 ≤ Im ρ ≤ 3rK + r} m(ρ)(Re ρ − ½)`
  (`mul_card_badCriticalScaleDiscs_le_offLineMoment`),

and an off-line moment bound `≤ μ·height` gives, uniformly in the radius,

  `#{k ≤ K : D_k zero-free} ≥ (1 − 3μ) K − μ`   once `3rK + r` is large

(`exists_card_goodCriticalScaleDiscs_ge_of_moment`); `μ = 21/100` gives `(37/100) K − 21/100`
(`exists_card_goodCriticalScaleDiscs_ge`).  On every zero-free disc the adjoint Hankel seam of the
`ξ` phase is a strict contraction (`criticalScaleDisc_adjointSeam_lt_one`), so the TG seam
criterion holds on at least `37%` of the right discs at every scale, including the zero-spacing
scale `r ≍ 1/log T`.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- **Exceptional discs against the off-line first moment.** -/
theorem mul_card_badCriticalScaleDiscs_le_offLineMoment {r : ℝ} (hr : 0 < r) (K : ℕ) :
    r * ((badCriticalScaleDiscs r K).card : ℝ) ≤ offLineMoment (3 * r * K + r) := by
  classical
  set T := 3 * r * K + r
  have hchoose : ∀ k ∈ badCriticalScaleDiscs r K,
      ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0 := by
    intro k hk
    unfold badCriticalScaleDiscs at hk
    exact (Finset.mem_filter.mp hk).2
  choose! w hwball hwzero using hchoose
  have hIcc : ∀ k ∈ badCriticalScaleDiscs r K, 1 ≤ k ∧ k ≤ K := by
    intro k hk
    unfold badCriticalScaleDiscs at hk
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
  have hbox : ∀ k ∈ badCriticalScaleDiscs r K, w k ∈ boxFinsetLe T := by
    intro k hk
    obtain ⟨h1, -, h3, h4⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hIcc k hk).1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (hIcc k hk).2
    rw [mem_boxFinsetLe]
    exact ⟨by linarith, xi_zero_re_lt_one (hwzero k hk), by nlinarith, by nlinarith, hwzero k hk⟩
  have hinj : Set.InjOn w (badCriticalScaleDiscs r K : Set ℕ) := by
    intro k hk l hl hkl
    obtain ⟨-, -, hk1, hk2⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    obtain ⟨-, -, hl1, hl2⟩ := re_im_of_mem_criticalScaleDisc (hwball l hl)
    rw [hkl] at hk1 hk2
    have f1 : (k : ℝ) - l < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have f2 : (l : ℝ) - k < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have g1 : (k : ℤ) - l < 1 := by exact_mod_cast f1
    have g2 : (l : ℤ) - k < 1 := by exact_mod_cast f2
    omega
  have hsub : (badCriticalScaleDiscs r K).image w ⊆ boxFinsetLe T := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hbox k hk
  have hre : ∀ z ∈ boxFinsetLe T, 0 ≤ ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) :=
    fun z hz => offLineMoment_term_nonneg hz
  calc r * ((badCriticalScaleDiscs r K).card : ℝ)
      = ∑ k ∈ badCriticalScaleDiscs r K, r := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ badCriticalScaleDiscs r K, ((w k).re - 1 / 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have := (re_im_of_mem_criticalScaleDisc (hwball k hk)).1
        linarith
    _ = ∑ z ∈ (badCriticalScaleDiscs r K).image w, (z.re - 1 / 2) :=
        (Finset.sum_image (f := fun z : ℂ => z.re - 1 / 2) (g := w)
          (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ z ∈ (badCriticalScaleDiscs r K).image w,
          ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hzb := hsub hz
        rw [mem_boxFinsetLe] at hzb
        have h1 := DeBruijn.one_le_toNat_analyticOrderAt_xi hzb.2.2.2.2
        have h1' : (1 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := by exact_mod_cast h1
        have hpos : 0 ≤ z.re - 1 / 2 := by linarith [hzb.1]
        nlinarith
    _ ≤ offLineMoment T :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => hre z hz

/-- **Exceptional discs from an off-line moment bound.**  If `Σ m(ρ)(Re ρ − ½) ≤ μ T` for all large
`T`, then at every scale at most `3μK + μ` of the discs `D_1, …, D_K` are exceptional. -/
theorem exists_card_badCriticalScaleDiscs_le_of_moment {μ : ℝ}
    (hmom : ∀ᶠ T in Filter.atTop, offLineMoment T ≤ μ * T) :
    ∃ T₀ : ℝ, ∀ r : ℝ, 0 < r → ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      ((badCriticalScaleDiscs r K).card : ℝ) ≤ 3 * μ * K + μ := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hmom
  refine ⟨T₀, fun r hr K hK => ?_⟩
  have h1 := mul_card_badCriticalScaleDiscs_le_offLineMoment hr K
  have h2 := hT₀ _ hK
  have h3 : r * ((badCriticalScaleDiscs r K).card : ℝ) ≤ r * (3 * μ * K + μ) := by
    have : μ * (3 * r * K + r) = r * (3 * μ * K + μ) := by ring
    linarith
  exact le_of_mul_le_mul_left h3 hr

/-- **At most `63%` exceptional discs, at every scale.** -/
theorem exists_card_badCriticalScaleDiscs_le :
    ∃ T₀ : ℝ, ∀ r : ℝ, 0 < r → ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      ((badCriticalScaleDiscs r K).card : ℝ) ≤ 63 / 100 * K + 21 / 100 := by
  obtain ⟨T₀, hT₀⟩ :=
    exists_card_badCriticalScaleDiscs_le_of_moment ZetaGateProductAFE.eventually_offLineMoment_le
  exact ⟨T₀, fun r hr K hK => (hT₀ r hr K hK).trans_eq (by ring)⟩

/-- **Contracting seams from an off-line moment bound.**  If `Σ m(ρ)(Re ρ − ½) ≤ μ T` for all large
`T`, then once `3rK + r` is large at least `(1 − 3μ) K − μ` of the discs `D_1, …, D_K` of radius
`r ≤ 1/8` are zero-free, and on each of them the adjoint Hankel seam of the `ξ` phase has norm
`< 1`. -/
theorem exists_card_goodCriticalScaleDiscs_ge_of_moment {μ : ℝ}
    (hmom : ∀ᶠ T in Filter.atTop, offLineMoment T ≤ μ * T) :
    ∃ T₀ : ℝ, ∀ r : ℝ, ∀ hr : 0 < r, ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      (1 - 3 * μ) * (K : ℝ) - μ ≤
        ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ) ∧
      ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs r K,
        ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
          ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
            < 1 := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_card_badCriticalScaleDiscs_le_of_moment hmom
  refine ⟨T₀, fun r hr K hK => ⟨?_, fun k hk => ?_⟩⟩
  · have hbad := hT₀ r hr K hK
    have hsub : badCriticalScaleDiscs r K ⊆ Finset.Icc 1 K := by
      intro k hk
      unfold badCriticalScaleDiscs at hk
      exact (Finset.mem_filter.mp hk).1
    have hcard := Finset.card_sdiff_of_subset hsub
    have hK : ((Finset.Icc 1 K).card : ℝ) = K := by simp
    have e : ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ)
        = ((Finset.Icc 1 K).card : ℝ) - (badCriticalScaleDiscs r K).card := by
      rw [hcard, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [e, hK]
    linarith
  · obtain ⟨hkI, hkb⟩ := Finset.mem_sdiff.mp hk
    apply criticalScaleDisc_adjointSeam_lt_one hr
    intro z hz hz0
    apply hkb
    unfold badCriticalScaleDiscs
    exact Finset.mem_filter.mpr ⟨hkI, z, hz, hz0⟩

/-- **Contracting seams on `37%` of the right discs, at every scale.** Once `3rK + r` is large,
at least `(37/100) K − 21/100` of the discs `D_1, …, D_K` of radius `r ≤ 1/8` are zero-free, and on
each of them the adjoint Hankel seam of the `ξ` phase has norm `< 1`. -/
theorem exists_card_goodCriticalScaleDiscs_ge :
    ∃ T₀ : ℝ, ∀ r : ℝ, ∀ hr : 0 < r, ∀ K : ℕ, T₀ ≤ 3 * r * K + r →
      37 / 100 * (K : ℝ) - 21 / 100 ≤
        ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ) ∧
      ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs r K,
        ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
          ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
            < 1 := by
  obtain ⟨T₀, hT₀⟩ :=
    exists_card_goodCriticalScaleDiscs_ge_of_moment ZetaGateProductAFE.eventually_offLineMoment_le
  refine ⟨T₀, fun r hr K hK => ⟨le_trans (le_of_eq (by ring)) (hT₀ r hr K hK).1, (hT₀ r hr K hK).2⟩⟩

end

end RHTower
