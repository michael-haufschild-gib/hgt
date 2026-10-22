import GaloisForLFunctions.RHTower.Suzuki.SuzukiCharacteristicMeromorphicLimit
import GaloisForLFunctions.HTGeometry.LaguerrePolyaImaginaryAxisBounds
import GaloisForLFunctions.RHTower.LaguerrePolyaFirstOrderInterlacing

/-!
# Dividing a Laguerre–Pólya function by a real zero

If `F` is Laguerre–Pólya, not identically zero, and `F(a) = 0` for a real `a`, then the quotient
`G = dslope F a` (so `F(z) = (z − a)G(z)`) is Laguerre–Pólya (`laguerrePolya_dslope`).

**Proof.** Let `p_m → F` be real-rooted approximants.
* The zero `a` is isolated, so small spheres around `a` are zero-free. By Hurwitz
  (`eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn`), `p_m` eventually has a
  zero in every small closed ball around `a`. That zero is real, so the root `a_m` of `p_m`
  nearest to `a` converges to `a` (`tendsto_nearestRoot`).
* `q_m = p_m/(X − a_m)` is real-rooted. On a large sphere around `a`,
  `q_m = p_m/(z − a_m) → F/(z − a) = G` uniformly. By the maximum principle the convergence
  holds on the whole ball (`tendstoLocallyUniformly_divByMonic`).
-/

open Complex Polynomial Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The root of `p` nearest to `a` (or `a` itself if `p` has no real root). -/
def nearestRoot (p : ℝ[X]) (a : ℝ) : ℝ :=
  if h : p.roots.toFinset.Nonempty then
    (p.roots.toFinset.exists_min_image (fun r => |r - a|) h).choose
  else a

theorem nearestRoot_mem {p : ℝ[X]} {a : ℝ} (h : p.roots.toFinset.Nonempty) :
    nearestRoot p a ∈ p.roots.toFinset := by
  rw [nearestRoot, dif_pos h]
  exact (p.roots.toFinset.exists_min_image (fun r => |r - a|) h).choose_spec.1

theorem abs_nearestRoot_sub_le {p : ℝ[X]} {a r : ℝ} (hr : r ∈ p.roots.toFinset) :
    |nearestRoot p a - a| ≤ |r - a| := by
  have h : p.roots.toFinset.Nonempty := ⟨r, hr⟩
  rw [nearestRoot, dif_pos h]
  exact (p.roots.toFinset.exists_min_image (fun r => |r - a|) h).choose_spec.2 r hr

/-- **The nearest roots converge.** -/
theorem tendsto_nearestRoot {F : ℂ → ℂ} {p : ℕ → ℝ[X]} (hsplit : ∀ m, (p m).Splits)
    (hconv : TendstoLocallyUniformly (fun m => polyEvalC (p m)) F atTop)
    (hdiff : Differentiable ℂ F) {z₀ : ℂ} (hz₀ : F z₀ ≠ 0) {a : ℝ} (ha : F a = 0) :
    (∀ᶠ m in atTop, (p m).roots.toFinset.Nonempty) ∧
      Tendsto (fun m => nearestRoot (p m) a) atTop (𝓝 a) := by
  -- the zero `a` is isolated
  have hanalytic : AnalyticAt ℂ F (a : ℂ) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff) _ (Set.mem_univ _)
  have hiso : ∀ᶠ z in 𝓝[≠] (a : ℂ), F z ≠ 0 := by
    rcases hanalytic.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have heq : Set.EqOn F 0 Set.univ :=
        (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff).eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (Set.mem_univ _) h
      exact hz₀ (heq (Set.mem_univ z₀))
    · exact h
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso)
  -- roots in every small ball
  have hroot : ∀ δ > 0, ∀ᶠ m in atTop, ∃ r ∈ (p m).roots.toFinset, |r - a| ≤ δ := by
    intro δ hδ
    set ρ := min δ (ε / 2) with hρ
    have hρ0 : 0 < ρ := lt_min hδ (by positivity)
    have hsphere : ∀ w ∈ sphere (a : ℂ) ρ, F w ≠ 0 := by
      intro w hw
      refine hεball ?_ ?_
      · rw [mem_sphere.mp hw]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · rw [Set.mem_compl_singleton_iff]
        intro h
        rw [mem_sphere, h, dist_self] at hw
        exact hρ0.ne' hw.symm
    have hH := eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn
      (tendstoLocallyUniformlyOn_univ.mpr hconv)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff)
      (Eventually.of_forall fun m => differentiable_polyEvalC (p m)) hρ0
      (Set.subset_univ _) ha hsphere
    have hne : ∀ᶠ m in atTop, p m ≠ 0 := by
      have hpt := (TendstoLocallyUniformlyOn.tendsto_at
        (tendstoLocallyUniformlyOn_univ.2 hconv) (Set.mem_univ z₀)).eventually_ne hz₀
      filter_upwards [hpt] with m hm h0
      exact hm (by simp [h0, polyEvalC])
    filter_upwards [hH, hne] with m ⟨w, hw, hw0⟩ hm
    have him : w.im = 0 := im_eq_zero_of_splits (hsplit m) hm hw0
    have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
    refine ⟨w.re, ?_, ?_⟩
    · rw [Multiset.mem_toFinset, mem_roots hm, IsRoot.def]
      have h1 : polyEvalC (p m) (w.re : ℂ) = 0 := by rw [← hw']; exact hw0
      rw [polyEvalC_ofReal] at h1
      exact_mod_cast h1
    · have : dist (w.re : ℂ) (a : ℂ) ≤ ρ := by rw [← hw']; exact mem_closedBall.mp hw
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
      exact this.trans (min_le_left _ _)
  refine ⟨?_, ?_⟩
  · filter_upwards [hroot 1 one_pos] with m ⟨r, hr, _⟩
    exact ⟨r, hr⟩
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hroot (δ / 2) (by positivity))
    refine ⟨N, fun m hm => ?_⟩
    obtain ⟨r, hr, hra⟩ := hN m hm
    rw [Real.dist_eq]
    exact lt_of_le_of_lt ((abs_nearestRoot_sub_le hr).trans hra) (by linarith)

/-- `p/(X − r)` when `r` is a root of `p ≠ 0`, and `0` otherwise. -/
def divRoot (p : ℝ[X]) (r : ℝ) : ℝ[X] := if p ≠ 0 ∧ p.IsRoot r then p /ₘ (X - C r) else 0

theorem divRoot_mul {p : ℝ[X]} {r : ℝ} (h : p ≠ 0 ∧ p.IsRoot r) :
    (X - C r) * divRoot p r = p := by
  rw [divRoot, if_pos h]
  exact mul_divByMonic_eq_iff_isRoot.mpr h.2

theorem splits_divRoot {p : ℝ[X]} (hp : p.Splits) (r : ℝ) : (divRoot p r).Splits := by
  by_cases h : p ≠ 0 ∧ p.IsRoot r
  · exact hp.of_dvd h.1 ⟨X - C r, by rw [mul_comm, divRoot_mul h]⟩
  · rw [divRoot, if_neg h]; exact Splits.zero

theorem differentiable_dslope_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ) :
    Differentiable ℂ (dslope F a) := by
  have h := (Complex.differentiableOn_dslope (s := Set.univ) (c := a) Filter.univ_mem).mpr
    hF.differentiableOn
  exact differentiableOn_univ.mp h

/-- **Dividing out a real zero preserves the Laguerre–Pólya class.** -/
theorem laguerrePolya_dslope {F : ℂ → ℂ} (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F)
    {z₀ : ℂ} (hz₀ : F z₀ ≠ 0) {a : ℝ} (ha : F a = 0) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (dslope F (a : ℂ)) := by
  have hdiff := hF.differentiable
  obtain ⟨p, hsplit, hconv⟩ := hF
  obtain ⟨hnon, hlim⟩ := tendsto_nearestRoot hsplit hconv hdiff hz₀ ha
  set am : ℕ → ℝ := fun m => nearestRoot (p m) a with ham
  have hroot : ∀ᶠ m in atTop, p m ≠ 0 ∧ (p m).IsRoot (am m) := by
    filter_upwards [hnon] with m hm
    have hmem := Multiset.mem_toFinset.mp (nearestRoot_mem (a := a) hm)
    have hp0 := ne_zero_of_mem_roots hmem
    exact ⟨hp0, (mem_roots hp0).mp hmem⟩
  refine ⟨fun m => divRoot (p m) (am m), fun m => splits_divRoot (hsplit m) _, ?_⟩
  set G := dslope F (a : ℂ) with hG
  have hGd : Differentiable ℂ G := differentiable_dslope_of_entire hdiff a
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (a : ℂ)
  set R' : ℝ := |R| + 1 with hR'
  have hR'1 : 1 ≤ R' := by rw [hR']; linarith [abs_nonneg R]
  have hR'0 : 0 < R' := by linarith
  refine TendstoUniformlyOn.mono (s := closedBall (a : ℂ) R') ?_
    (hR.trans (closedBall_subset_closedBall (by linarith [le_abs_self R, hR'])))
  -- uniform data on the sphere
  have hS := isCompact_sphere (a : ℂ) R'
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hdiff.continuous.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (NormedSpace.sphere_nonempty.mpr
    hR'0.le).some_mem)
  have hconvS : TendstoUniformlyOn (fun m => polyEvalC (p m)) F atTop (sphere (a : ℂ) R') :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) _ hS
  rw [Metric.tendstoUniformlyOn_iff] at hconvS ⊢
  intro ε hε
  have h1 := hconvS (ε / 8) (by positivity)
  have h2 : ∀ᶠ m in atTop, |am m - a| < min (1 / 2) (ε / (8 * (M + 1))) := by
    have := (Metric.tendsto_atTop.mp hlim) (min (1 / 2) (ε / (8 * (M + 1)))) (by positivity)
    obtain ⟨N, hN⟩ := this
    exact eventually_atTop.mpr ⟨N, fun m hm => by simpa [Real.dist_eq] using hN m hm⟩
  filter_upwards [h1, h2, hroot] with m hm1 hm2 hm3 z hz
  -- the bound on the sphere
  have hsph : ∀ w ∈ sphere (a : ℂ) R', ‖G w - polyEvalC (divRoot (p m) (am m)) w‖ ≤ ε / 2 := by
    intro w hw
    have hwa : ‖w - a‖ = R' := by rw [← dist_eq_norm]; exact mem_sphere.mp hw
    have hamh : |am m - a| < 1 / 2 := lt_of_lt_of_le hm2 (min_le_left _ _)
    have hwam : 1 / 2 ≤ ‖w - (am m : ℂ)‖ := by
      have h3 : ‖w - (a : ℂ)‖ ≤ ‖w - (am m : ℂ)‖ + ‖((am m : ℂ) - a)‖ := by
        have := norm_add_le (w - (am m : ℂ)) ((am m : ℂ) - a)
        rwa [show w - (am m : ℂ) + ((am m : ℂ) - a) = w - a by ring] at this
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hwa] at h3
      linarith
    have hwne : w ≠ (a : ℂ) := by
      intro h; rw [h, sub_self, norm_zero] at hwa; linarith
    have hwne' : w - (am m : ℂ) ≠ 0 := by
      intro h; rw [h, norm_zero] at hwam; linarith
    have hwne2 : w - (a : ℂ) ≠ 0 := sub_ne_zero.mpr hwne
    -- the two quotients
    have hq : polyEvalC (divRoot (p m) (am m)) w = polyEvalC (p m) w / (w - am m) := by
      have e := congrArg (fun q => polyEvalC q w) (divRoot_mul hm3)
      simp only [polyEvalC_mul, polyEvalC_X_sub_C] at e
      field_simp
      rw [mul_comm]; exact e
    have hGw : G w = F w / (w - a) := by
      rw [hG, dslope_of_ne _ hwne, slope_def_field, ha, sub_zero]
    rw [hq, hGw]
    have e : F w / (w - a) - polyEvalC (p m) w / (w - am m) =
        (F w - polyEvalC (p m) w) / (w - am m) +
          F w * (((a : ℂ) - am m) / ((w - a) * (w - am m))) := by
      field_simp; ring
    rw [e]
    have hFw := hM w hw
    have hd := hm1 w hw
    rw [dist_eq_norm] at hd
    have hb1 : ‖(F w - polyEvalC (p m) w) / (w - am m)‖ ≤ 2 * (ε / 8) := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hwne')]
      nlinarith [norm_nonneg (F w - polyEvalC (p m) w)]
    have hb2 : ‖F w * (((a : ℂ) - am m) / ((w - a) * (w - am m)))‖ ≤
        M * (2 * (ε / (8 * (M + 1)))) := by
      rw [norm_mul, norm_div, norm_mul]
      have hnum : ‖((a : ℂ) - am m)‖ ≤ ε / (8 * (M + 1)) := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        exact (lt_of_lt_of_le hm2 (min_le_right _ _)).le
      have hden : 1 / 2 ≤ ‖w - (a : ℂ)‖ * ‖w - (am m : ℂ)‖ := by
        rw [hwa]; nlinarith
      have hfrac : ‖((a : ℂ) - am m)‖ / (‖w - (a : ℂ)‖ * ‖w - (am m : ℂ)‖) ≤
          2 * (ε / (8 * (M + 1))) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg ((a : ℂ) - am m)]
      exact mul_le_mul hFw hfrac (by positivity) hM0
    have hb3 : M * (2 * (ε / (8 * (M + 1)))) ≤ ε / 4 := by
      rw [show M * (2 * (ε / (8 * (M + 1)))) = (ε / 4) * (M / (M + 1)) by field_simp; ring]
      have : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    calc _ ≤ ‖(F w - polyEvalC (p m) w) / (w - am m)‖ +
          ‖F w * (((a : ℂ) - am m) / ((w - a) * (w - am m)))‖ := norm_add_le _ _
      _ ≤ 2 * (ε / 8) + ε / 4 := add_le_add hb1 (hb2.trans hb3)
      _ = ε / 2 := by ring
  -- the maximum principle
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (a : ℂ) R')
    isBounded_ball ((hGd.sub (differentiable_polyEvalC _)).diffContOnCl)
    (fun w hw => by rw [frontier_ball _ hR'0.ne'] at hw; exact hsph w hw)
    (z := z) (by rw [closure_ball _ hR'0.ne']; exact hz)
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hmax (by linarith)

end

end RHTower
