/-
# Distinct connected parameters have mutually non-nested filled Julia sets

For `c₁ ≠ c₂` in the Mandelbrot set, `K_{c₁} ⊄ K_{c₂}`; equivalently the Julia set `J_{c₁}` meets
the basin `Ω_{c₂}`.

Suppose `K_{c₁} ⊆ K_{c₂}`, so `Ω_{c₂} ⊆ Ω_{c₁}`.  With `ψ₂` the inverse Böttcher map of `c₂`, the
function `f(t) = 1/(t·β₁(ψ₂(1/t)))` on the punctured unit disk has modulus `|t|⁻¹·e^{−G₁}` at
`ψ₂(1/t)`, which is also `e^{G₂ − G₁}`.  Both Green functions are `log|z| + O(|z|⁻²)`, so `|f| → 1`
at `0` and the singularity is removable with `|f(0)| = 1`.  On `|t| = r` the modulus is at most
`1/r`, so the maximum principle gives `|f| ≤ 1` on the disk with the maximum attained at `0`; hence
`|f| ≡ 1` and `G₁ = G₂` on `Ω_{c₂}`.  No point of `Ω_{c₁}` can then lie on `∂Ω_{c₂}`, where `G₁`
would vanish, so the connected `Ω_{c₁}` lies in `Ω_{c₂}`: the filled Julia sets coincide and
`c₁ = c₂`.
-/
import GaloisForLFunctions.Bottcher.Q62BothConnectedIndependence
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex Filter Topology Set Metric

namespace Bottcher

/-- In the escape region the dynamical Green function is the Green limit. -/
theorem greenFunctionDyn_eq_greenLimit_of_escape {c z : ℂ} (hz : z ∈ escapeOpen c) :
    greenFunctionDyn c z = greenLimit c z := by
  unfold greenFunctionDyn
  rw [if_neg (escapeOpen_subset_compl_filledJulia c hz)]

/-- **Two Green functions agree at infinity** to order `|z|⁻²`. -/
theorem abs_greenFunctionDyn_sub_le {c₁ c₂ z : ℂ} (h1 : max 2 ‖c₁‖ < ‖z‖)
    (h2 : max 2 ‖c₂‖ < ‖z‖) :
    |greenFunctionDyn c₂ z - greenFunctionDyn c₁ z|
      ≤ 2 * ‖c₁‖ / ‖z‖ ^ (2 : ℕ) + 2 * ‖c₂‖ / ‖z‖ ^ (2 : ℕ) := by
  rw [greenFunctionDyn_eq_greenLimit_of_escape (c := c₁) h1,
    greenFunctionDyn_eq_greenLimit_of_escape (c := c₂) h2]
  have e1 := greenLimit_abs_sub_log (c := c₁) (z := z)
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) h1)) (lt_of_le_of_lt (le_max_left _ _) h1)
  have e2 := greenLimit_abs_sub_log (c := c₂) (z := z)
    (le_of_lt (lt_of_le_of_lt (le_max_right _ _) h2)) (lt_of_le_of_lt (le_max_left _ _) h2)
  calc |greenLimit c₂ z - greenLimit c₁ z|
      = |(greenLimit c₂ z - Real.log ‖z‖) - (greenLimit c₁ z - Real.log ‖z‖)| := by ring_nf
    _ ≤ |greenLimit c₂ z - Real.log ‖z‖| + |greenLimit c₁ z - Real.log ‖z‖| := abs_sub _ _
    _ ≤ 2 * ‖c₂‖ / ‖z‖ ^ (2 : ℕ) + 2 * ‖c₁‖ / ‖z‖ ^ (2 : ℕ) := add_le_add e2 e1
    _ = _ := by ring

/-- **Nested connected filled Julia sets have equal Green functions on the smaller basin.** -/
theorem greenFunctionDyn_eq_of_filledJulia_subset {c₁ c₂ : ℂ} (hc₁M : c₁ ∈ mandelbrot)
    (hc₂M : c₂ ∈ mandelbrot) (hsub : filledJulia c₁ ⊆ filledJulia c₂) :
    ∀ z ∈ (filledJulia c₂)ᶜ, greenFunctionDyn c₁ z = greenFunctionDyn c₂ z := by
  obtain ⟨β₁, -, hβ₁an, -, hβ₁mod, -⟩ := exists_global_branch_with_inverse_of_mem_mandelbrot c₁ hc₁M
  obtain ⟨h₂, β₂, ψ₂, hhd, -, -, hh0, hbridge, -, -, hβ₂mod, hψ₂an, hψβ₂, hψmem₂, hβψ₂⟩ :=
    exists_connected_bottcher_package c₂ hc₂M
  have hΩ : (filledJulia c₂)ᶜ ⊆ (filledJulia c₁)ᶜ := compl_subset_compl.mpr hsub
  set G₁ := greenFunctionDyn c₁
  set G₂ := greenFunctionDyn c₂
  set P : Set ℂ := ball (0 : ℂ) 1 \ {0} with hPdef
  have hPt : ∀ t ∈ P, t ≠ 0 ∧ 1 < ‖1 / t‖ := by
    intro t ht
    have ht0 : t ≠ 0 := ht.2
    have htn : ‖t‖ < 1 := mem_ball_zero_iff.mp ht.1
    refine ⟨ht0, ?_⟩
    rw [norm_div, norm_one]
    exact (one_lt_div (norm_pos_iff.mpr ht0)).mpr htn
  set z : ℂ → ℂ := fun t => ψ₂ (1 / t) with hzdef
  have hzΩ₂ : ∀ t ∈ P, z t ∈ (filledJulia c₂)ᶜ := fun t ht => hψmem₂ _ (hPt t ht).2
  set f : ℂ → ℂ := fun t => 1 / (t * β₁ (z t)) with hfdef
  -- the modulus of `f`
  have hG₂z : ∀ t ∈ P, Real.exp (G₂ (z t)) = 1 / ‖t‖ := by
    intro t ht
    rw [← hβ₂mod _ (hzΩ₂ t ht), hzdef, hβψ₂ _ (hPt t ht).2, norm_div, norm_one]
  have hnorm : ∀ t ∈ P, ‖f t‖ = (1 / ‖t‖) / Real.exp (G₁ (z t)) := by
    intro t ht
    rw [hfdef, norm_div, norm_one, norm_mul, hβ₁mod _ (hΩ (hzΩ₂ t ht))]
    field_simp
  have hnormD : ∀ t ∈ P, ‖f t‖ = Real.exp (G₂ (z t) - G₁ (z t)) := by
    intro t ht
    rw [hnorm t ht, ← hG₂z t ht, Real.exp_sub]
  -- `f` is holomorphic on the punctured disk
  have hdiff : DifferentiableOn ℂ f P := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := hPt t ht
    have hinv : DifferentiableAt ℂ (fun t : ℂ => 1 / t) t := by
      simpa only [one_div] using differentiableAt_inv ht0
    have hψ : DifferentiableAt ℂ ψ₂ (1 / t) := (hψ₂an _ ht1).differentiableAt
    have hβ : DifferentiableAt ℂ β₁ (z t) := (hβ₁an _ (hΩ (hzΩ₂ t ht))).differentiableAt
    have hden : t * β₁ (z t) ≠ 0 := by
      refine mul_ne_zero ht0 fun h0 => ?_
      have := hβ₁mod _ (hΩ (hzΩ₂ t ht))
      rw [h0, norm_zero] at this
      exact (Real.exp_pos _).ne' this.symm
    have hcomp : DifferentiableAt ℂ (fun t => t * β₁ (z t)) t :=
      differentiableAt_id.mul (hβ.comp t (hψ.comp t hinv))
    exact (hcomp.inv hden).differentiableWithinAt.congr (fun y _ => by simp [hfdef, one_div])
      (by simp [hfdef, one_div])
  -- the modulus exponent is bounded above on the `c₂`-basin
  set R : ℝ := max (max 2 ‖c₁‖) (max 2 ‖c₂‖) + 1 with hRdef
  have hR1 : max 2 ‖c₁‖ < R := by
    have := le_max_left (max 2 ‖c₁‖) (max 2 ‖c₂‖); rw [hRdef]; linarith
  have hR2 : max 2 ‖c₂‖ < R := by
    have := le_max_right (max 2 ‖c₁‖) (max 2 ‖c₂‖); rw [hRdef]; linarith
  have hR0 : (1 : ℝ) ≤ R := by
    have := le_max_left 2 ‖c₁‖; linarith
  set Kc : ℝ := 2 * ‖c₁‖ + 2 * ‖c₂‖ with hKcdef
  have hfar : ∀ w : ℂ, R ≤ ‖w‖ → |G₂ w - G₁ w| ≤ Kc / ‖w‖ ^ (2 : ℕ) := by
    intro w hw
    have h := abs_greenFunctionDyn_sub_le (lt_of_lt_of_le hR1 hw) (lt_of_lt_of_le hR2 hw)
    rw [hKcdef, add_div]
    exact h
  obtain ⟨M, hM⟩ : BddAbove (G₂ '' closedBall 0 R) :=
    (isCompact_closedBall 0 R).bddAbove_image (continuous_greenFunctionDyn c₂).continuousOn
  have hDup : ∀ w ∈ (filledJulia c₂)ᶜ, G₂ w - G₁ w ≤ max M Kc := by
    intro w _hw
    rcases le_or_gt R ‖w‖ with hw | hw
    · have h1 := hfar w hw
      have hpos : (1 : ℝ) ≤ ‖w‖ ^ (2 : ℕ) := one_le_pow₀ (le_trans hR0 hw)
      have hKc : 0 ≤ Kc := by positivity
      have h2 : Kc / ‖w‖ ^ (2 : ℕ) ≤ Kc := div_le_self hKc hpos
      exact le_trans (le_trans (le_abs_self _) (le_trans h1 h2)) (le_max_right _ _)
    · have h1 : G₂ w ≤ M := hM ⟨w, mem_closedBall_zero_iff.mpr hw.le, rfl⟩
      have h2 : 0 ≤ G₁ w := greenFunctionDyn_nonneg c₁ w
      exact le_trans (by linarith) (le_max_left _ _)
  have hbdd : BddAbove (norm ∘ f '' P) := by
    refine ⟨Real.exp (max M Kc), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only [Function.comp_apply]
    rw [hnormD t ht]
    exact Real.exp_le_exp.mpr (hDup _ (hzΩ₂ t ht))
  -- removable singularity at `0`
  set F : ℂ → ℂ := Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f) with hFdef
  have hFd : DifferentiableOn ℂ F (ball 0 1) :=
    differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds 0 one_pos) hdiff hbdd
  have hFf : ∀ t ∈ P, F t = f t := fun t ht => Function.update_of_ne ht.2 _ _
  -- `‖f‖ → 1` at `0`
  have hzbig : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ P ∧ 1 / (2 * ‖t‖) ≤ ‖z t‖ := by
    have hh₂c : ContinuousAt h₂ 0 := (hhd.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
    have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), (1 / 2 : ℝ) ≤ ‖h₂ t‖ := by
      have h := hh₂c.norm.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < ‖h₂ 0‖ by
        rw [hh0, norm_one]; norm_num))
      exact h.mono fun t ht => ht.le
    filter_upwards [nhdsWithin_le_nhds hnear, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos),
      self_mem_nhdsWithin] with t hnt hball ht0
    have htP : t ∈ P := ⟨hball, ht0⟩
    refine ⟨htP, ?_⟩
    have ht0' : t ≠ 0 := ht0
    have htn : ‖t‖ < 1 := mem_ball_zero_iff.mp hball
    have hbr := hbridge t ht0' htn
    have hzt : z t = h₂ t / t := by
      rw [hzdef, hbr]; field_simp
    rw [hzt, norm_div]
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0'
    rw [div_le_div_iff₀ (by positivity) htpos]
    nlinarith
  have hDlim : Tendsto (fun t => G₂ (z t) - G₁ (z t)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have hsq : Tendsto (fun t : ℂ => 4 * Kc * ‖t‖ ^ (2 : ℕ)) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      have : Tendsto (fun t : ℂ => 4 * Kc * ‖t‖ ^ (2 : ℕ)) (𝓝 (0 : ℂ)) (𝓝 (4 * Kc * ‖(0:ℂ)‖ ^ 2)) :=
        ((continuous_const.mul (continuous_norm.pow 2)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ < 1 / (2 * R) := by
      have hR2pos : (0 : ℝ) < 1 / (2 * R) := by positivity
      have : ∀ᶠ t in 𝓝 (0 : ℂ), ‖t‖ < 1 / (2 * R) :=
        continuous_norm.continuousAt.eventually
          (gt_mem_nhds (show ‖(0 : ℂ)‖ < 1 / (2 * R) by rw [norm_zero]; exact hR2pos))
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds this
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [hzbig, hsmall] with t ⟨htP, hzt⟩ hts
    have ht0 : t ≠ 0 := htP.2
    have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have hzR : R ≤ ‖z t‖ := by
      refine le_trans ?_ hzt
      rw [le_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ (by positivity)] at hts
      linarith
    have hzpos : 0 < ‖z t‖ := lt_of_lt_of_le (by linarith) hzR
    rw [Real.norm_eq_abs]
    refine le_trans (hfar _ hzR) ?_
    have hKc : 0 ≤ Kc := by positivity
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ 2 * ‖t‖ * ‖z t‖ := by
      have := hzt
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h2 : 1 ≤ (2 * ‖t‖ * ‖z t‖) ^ (2 : ℕ) := one_le_pow₀ h1
    nlinarith
  have hfnorm_lim : Tendsto (fun t => ‖f t‖) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hDlim
    rw [Real.exp_zero] at h
    refine h.congr' ?_
    filter_upwards [hzbig] with t ⟨htP, _⟩
    exact (hnormD t htP).symm
  have hF0 : ‖F 0‖ = 1 := by
    have hFc : ContinuousAt F 0 := (hFd.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt
    have h1 : Tendsto (fun t => ‖F t‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖F 0‖) :=
      (hFc.norm.tendsto).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t => ‖F t‖) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
      refine hfnorm_lim.congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos)]
        with t ht hball
      rw [hFf t ⟨hball, ht⟩]
    exact tendsto_nhds_unique h1 h2
  -- the maximum principle: `‖F‖ ≤ 1` on the disk
  have hFle : ∀ t ∈ ball (0 : ℂ) 1, ‖F t‖ ≤ 1 := by
    intro t₀ ht₀
    have ht₀n : ‖t₀‖ < 1 := mem_ball_zero_iff.mp ht₀
    have hbound : ∀ r : ℝ, ‖t₀‖ < r → r < 1 → ‖F t₀‖ ≤ 1 / r := by
      intro r hr hr1
      have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr
      have hsubB : closedBall (0 : ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hr1
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (hFd.diffContOnCl_ball hsubB) ?_ (subset_closure (mem_ball_zero_iff.mpr hr))
      intro t ht
      rw [frontier_ball 0 hrpos.ne', mem_sphere_zero_iff_norm] at ht
      have ht0 : t ≠ 0 := by
        intro h0; rw [h0, norm_zero] at ht; linarith
      have htP : t ∈ P := ⟨mem_ball_zero_iff.mpr (by rw [ht]; exact hr1), ht0⟩
      rw [hFf t htP, hnorm t htP, ht]
      exact div_le_self (by positivity) (Real.one_le_exp (greenFunctionDyn_nonneg c₁ _))
    by_contra hgt
    push Not at hgt
    set r : ℝ := max ((1 + ‖t₀‖) / 2) ((1 + 1 / ‖F t₀‖) / 2)
    have hFpos : 0 < ‖F t₀‖ := lt_trans one_pos hgt
    have hinvlt : 1 / ‖F t₀‖ < 1 := (div_lt_one hFpos).mpr hgt
    have hr1 : r < 1 := max_lt (by linarith) (by linarith)
    have hr0 : ‖t₀‖ < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hrF : 1 / ‖F t₀‖ < r := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr0
    have := hbound r hr0 hr1
    rw [div_lt_iff₀ hFpos] at hrF
    rw [le_div_iff₀ hrpos] at this
    linarith
  -- the maximum is attained at `0`, so `‖F‖ ≡ 1`
  have hmax : IsMaxOn (norm ∘ F) (ball 0 1) 0 := fun t ht => by
    simp only [mem_setOf_eq, Function.comp_apply, hF0]
    exact hFle t ht
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0:ℂ) 1).isPreconnected
    isOpen_ball hFd (mem_ball_self one_pos) hmax
  intro w hw
  have hβw : 1 < ‖β₂ w‖ := by
    rw [hβ₂mod w hw]
    have hpos : 0 < G₂ w := by
      rcases (greenFunctionDyn_nonneg c₂ w).lt_or_eq with h | h
      · exact h
      · exact absurd ((greenFunctionDyn_eq_zero_iff c₂ w).mp h.symm) hw
    exact Real.one_lt_exp_iff.mpr hpos
  set t : ℂ := 1 / β₂ w with htdef
  have hβ0 : β₂ w ≠ 0 := by intro h0; rw [h0, norm_zero] at hβw; linarith
  have htP : t ∈ P := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, htdef, norm_div, norm_one]
      exact (div_lt_one (by linarith)).mpr hβw
    · rw [htdef]; exact one_div_ne_zero hβ0
  have hzt : z t = w := by
    show ψ₂ (1 / (1 / β₂ w)) = w
    rw [one_div_one_div, hψβ₂ w hw]
  have hFt : ‖F t‖ = 1 := by
    rw [hconst (mem_ball_zero_iff.mpr (mem_ball_zero_iff.mp htP.1))]
    exact hF0
  rw [hFf t htP, hnorm t htP, hzt] at hFt
  have ht1 : 1 / ‖t‖ = Real.exp (G₂ w) := by rw [← hG₂z t htP, hzt]
  rw [ht1, div_eq_one_iff_eq (Real.exp_pos _).ne'] at hFt
  exact (Real.exp_injective hFt).symm

/-- **Distinct connected parameters: `K_{c₁} ⊄ K_{c₂}`.** -/
theorem not_filledJulia_subset_of_mem_mandelbrot {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot) :
    ¬ filledJulia c₁ ⊆ filledJulia c₂ := by
  intro hsub
  have hG := greenFunctionDyn_eq_of_filledJulia_subset hc₁M hc₂M hsub
  -- the basin of `c₁` avoids the frontier of the basin of `c₂`
  have hfr : (filledJulia c₁)ᶜ ∩ frontier (filledJulia c₂)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hy₁, hyfr⟩
    have hyK₂ : y ∈ filledJulia c₂ := by
      have hopen := (isClosed_filledJulia c₂).isOpen_compl
      rw [hopen.frontier_eq] at hyfr
      simpa using hyfr.2
    have hlim : Tendsto (greenFunctionDyn c₁) (𝓝[(filledJulia c₂)ᶜ] y)
        (𝓝 (greenFunctionDyn c₂ y)) := by
      have h := ((continuous_greenFunctionDyn c₂).tendsto y).mono_left
        (nhdsWithin_le_nhds (s := (filledJulia c₂)ᶜ))
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw using (hG w hw).symm
    haveI : (𝓝[(filledJulia c₂)ᶜ] y).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (frontier_subset_closure hyfr)
    have h1 : Tendsto (greenFunctionDyn c₁) (𝓝[(filledJulia c₂)ᶜ] y)
        (𝓝 (greenFunctionDyn c₁ y)) :=
      ((continuous_greenFunctionDyn c₁).tendsto y).mono_left nhdsWithin_le_nhds
    have heq := tendsto_nhds_unique h1 hlim
    rw [(greenFunctionDyn_eq_zero_iff c₂ y).mpr hyK₂] at heq
    exact hy₁ ((greenFunctionDyn_eq_zero_iff c₁ y).mp heq)
  obtain ⟨u, hu⟩ : (escapeOpen c₁ ∩ escapeOpen c₂).Nonempty :=
    (isConnected_escapeOpen_inter c₁ c₂).nonempty
  have hsub₂ : (filledJulia c₁)ᶜ ⊆ (filledJulia c₂)ᶜ :=
    subset_of_isPreconnected_of_inter_frontier_empty_of_inter_nonempty
      (isPreconnected_compl_filledJulia c₁) (isClosed_filledJulia c₂).isOpen_compl
      ⟨u, escapeOpen_subset_compl_filledJulia c₁ hu.1, escapeOpen_subset_compl_filledJulia c₂ hu.2⟩
      hfr
  have heqK : filledJulia c₁ = filledJulia c₂ :=
    Subset.antisymm hsub (compl_subset_compl.mp hsub₂)
  exact hne (c_eq_of_filledJulia_eq' heqK)

/-- **The Julia set of `c₁` meets the basin of `c₂`** for distinct connected parameters. -/
theorem exists_frontier_filledJulia_not_mem_of_mem_mandelbrot {c₁ c₂ : ℂ} (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₂M : c₂ ∈ mandelbrot) :
    ∃ p, p ∈ frontier (filledJulia c₁) ∧ p ∉ filledJulia c₂ := by
  obtain ⟨x, hx₁, hx₂⟩ := not_subset.mp (not_filledJulia_subset_of_mem_mandelbrot hne hc₁M hc₂M)
  exact exists_frontier_off hx₁ hx₂

end Bottcher
