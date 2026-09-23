import GaloisForLFunctions.HTGeometry.MultiPairPhaseBlind

/-!
# Separation on an arbitrary interval

`LogConcaveSeparation` proved that a single exponential separates a positive exponential sum from a
log-concave comparison function on a *hump* — an interval whose endpoints carry `C ≤ 0`.  That
hypothesis was an artefact: it was used only to place the maximiser of `C/R` in the interior.

The first-order optimality condition on a convex set replaces it.  At a maximiser of `C/R` over any
interval, interior or endpoint, one has `(C'/C − R'/R)(t^*)·(t − t^*) ≤ 0` for every `t` in the
interval, and that is exactly what the tangency argument needs.  So separation holds on **any**
interval on which `C` is log-tangent-dominated.

The consequence is that a hump may be subdivided — at the inflection points of `log C`, say — without
losing the criterion.  The piecewise profile criterion therefore applies to an arbitrary finite cover
of the positivity set by intervals of log-concavity.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-! ## The first-order condition -/

/-- **First-order optimality on an interval.**  At a maximiser over `[u,v]`, the derivative points
away from the interval. -/
theorem deriv_mul_sub_nonpos_of_isMaxOn {f : ℝ → ℝ} {u v ts : ℝ}
    (hf : ∀ x, DifferentiableAt ℝ f x) (hts : ts ∈ Icc u v)
    (hmax : ∀ s ∈ Icc u v, f s ≤ f ts) {t : ℝ} (ht : t ∈ Icc u v) :
    deriv f ts * (t - ts) ≤ 0 := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hf ts).hasDerivAt
  rcases lt_trichotomy t ts with hlt | heq | hgt
  · have hd : 0 ≤ deriv f ts := by
      by_contra hcon
      push Not at hcon
      have hev : ∀ᶠ s in nhdsWithin ts (Set.Iio ts), slope f ts s < 0 := by
        refine (hslope.mono_left ?_).eventually (eventually_lt_nhds hcon)
        exact nhdsWithin_mono ts (fun x hx => ne_of_lt hx)
      have hev2 : ∀ᶠ s in nhdsWithin ts (Set.Iio ts), t < s :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hlt)
      obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
      have hslt : s < ts := hs3
      have hfs : f ts < f s := by
        rw [slope_def_field] at hs1
        rcases div_neg_iff.mp hs1 with ⟨h1, _⟩ | ⟨_, h2⟩
        · linarith
        · linarith
      exact absurd (hmax s ⟨le_trans ht.1 (le_of_lt hs2), le_trans (le_of_lt hslt) hts.2⟩)
        (not_le.mpr hfs)
    nlinarith
  · rw [heq]; simp
  · have hd : deriv f ts ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have hev : ∀ᶠ s in nhdsWithin ts (Set.Ioi ts), 0 < slope f ts s := by
        refine (hslope.mono_left ?_).eventually (eventually_gt_nhds hcon)
        exact nhdsWithin_mono ts (fun x hx => ne_of_gt hx)
      have hev2 : ∀ᶠ s in nhdsWithin ts (Set.Ioi ts), s < t :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hgt)
      obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
      have hsgt : ts < s := hs3
      have hfs : f ts < f s := by
        rw [slope_def_field] at hs1
        rcases div_pos_iff.mp hs1 with ⟨h1, _⟩ | ⟨_, h2⟩
        · linarith
        · linarith
      exact absurd (hmax s ⟨le_trans hts.1 (le_of_lt hsgt), le_trans (le_of_lt hs2) ht.2⟩)
        (not_le.mpr hfs)
    nlinarith

/-! ## Separation without endpoint conditions -/

/-- **Separation on an arbitrary interval.**  If `C` is log-tangent-dominated on `[u,v]` and is
dominated there by a positive exponential sum, then a single exponential separates them — with no
condition on the values at the endpoints. -/
theorem exists_separating_of_le_on_interval {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m)
    (hc : ∀ i, 0 < c i) {C : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (hCcont : Continuous C) (hCdiff : ∀ t, DifferentiableAt ℝ C t)
    (hlt : LogTangentDominated C (Icc u v))
    (hdom : ∀ t ∈ Icc u v, C t ≤ expSum c a t) :
    ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + ν * t) ≤ expSum c a t)
      ∧ ∀ t ∈ Icc u v, C t ≤ Real.exp (L + ν * t) := by
  have hRpos : ∀ t : ℝ, 0 < expSum c a t := fun t => expSum_pos c a hm hc t
  set P : ℝ → ℝ := fun t => C t / expSum c a t with hP
  have hPcont : Continuous P :=
    hCcont.div ((contDiff_expSum c a).continuous) (fun t => ne_of_gt (hRpos t))
  have hPdiff : ∀ x, DifferentiableAt ℝ P x := fun x =>
    (hCdiff x).div ((contDiff_expSum c a).differentiable (by simp) x) (ne_of_gt (hRpos x))
  obtain ⟨ts, htsK, htsmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨u, left_mem_Icc.mpr huv⟩ hPcont.continuousOn
  by_cases hCpos : 0 < C ts
  case neg =>
    push Not at hCpos
    -- the comparison is nonpositive on the whole interval; any supporting exponential works
    refine ⟨expSum (fun i => c i * a i) a 0 / expSum c a 0,
      Real.log (expSum c a 0) - expSum (fun i => c i * a i) a 0 / expSum c a 0 * 0, ?_, ?_⟩
    · intro t
      have hsup := exp_supporting_le_expSum c a hm hc 0 t
      have hrw : Real.log (expSum c a 0)
            - expSum (fun i => c i * a i) a 0 / expSum c a 0 * 0
            + expSum (fun i => c i * a i) a 0 / expSum c a 0 * t
          = Real.log (expSum c a 0)
            + expSum (fun i => c i * a i) a 0 / expSum c a 0 * (t - 0) := by ring
      rw [hrw]
      exact hsup
    · intro t ht
      have hPt : P t ≤ P ts := htsmax ht
      have hCt : C t ≤ 0 := by
        simp only [hP] at hPt
        have h1 : C ts / expSum c a ts ≤ 0 := div_nonpos_of_nonpos_of_nonneg hCpos (hRpos ts).le
        have h2 : C t / expSum c a t ≤ 0 := le_trans hPt h1
        rcases div_nonpos_iff.mp h2 with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact absurd hb (not_le.mpr (hRpos t))
        · exact ha
      exact le_trans hCt (Real.exp_pos _).le
  -- the tangency argument, driven by the first-order condition
  set nu : ℝ := expSum (fun i => c i * a i) a ts / expSum c a ts with hnu
  have hfirst : ∀ t ∈ Icc u v, deriv P ts * (t - ts) ≤ 0 := fun t ht =>
    deriv_mul_sub_nonpos_of_isMaxOn hPdiff htsK (fun s hs => htsmax hs) ht
  have hPderiv : HasDerivAt P
      ((deriv C ts * expSum c a ts - C ts * expSum (fun i => c i * a i) a ts)
        / (expSum c a ts) ^ (2 : ℕ)) ts :=
    ((hCdiff ts).hasDerivAt).div (hasDerivAt_expSum c a ts) (ne_of_gt (hRpos ts))
  have hderivP : deriv P ts
      = (deriv C ts * expSum c a ts - C ts * expSum (fun i => c i * a i) a ts)
          / (expSum c a ts) ^ (2 : ℕ) := hPderiv.deriv
  have hslope : ∀ t ∈ Icc u v, (deriv C ts / C ts - nu) * (t - ts) ≤ 0 := by
    intro t ht
    have h1 := hfirst t ht
    rw [hderivP, div_mul_eq_mul_div] at h1
    have hR2 : (0 : ℝ) < (expSum c a ts) ^ (2 : ℕ) := pow_pos (hRpos ts) 2
    have h2 : (deriv C ts * expSum c a ts - C ts * expSum (fun i => c i * a i) a ts)
        * (t - ts) ≤ 0 := by
      rcases div_nonpos_iff.mp h1 with ⟨_, hb⟩ | ⟨ha, _⟩
      · exact absurd hb (not_le.mpr hR2)
      · exact ha
    have hCR : (0 : ℝ) < C ts * expSum c a ts := mul_pos hCpos (hRpos ts)
    have hEq : (deriv C ts / C ts - nu) * (t - ts)
        = ((deriv C ts * expSum c a ts - C ts * expSum (fun i => c i * a i) a ts) * (t - ts))
          / (C ts * expSum c a ts) := by
      rw [hnu, div_sub_div _ _ (ne_of_gt hCpos) (ne_of_gt (hRpos ts)), div_mul_eq_mul_div]
    rw [hEq]
    exact div_nonpos_of_nonpos_of_nonneg h2 hCR.le
  refine ⟨nu, Real.log (expSum c a ts) - nu * ts, ?_, ?_⟩
  · intro t
    have hsup := exp_supporting_le_expSum c a hm hc ts t
    rw [← hnu] at hsup
    have hrw : Real.log (expSum c a ts) - nu * ts + nu * t
        = Real.log (expSum c a ts) + nu * (t - ts) := by ring
    rw [hrw]
    exact hsup
  · intro t ht
    have htan := hlt ts htsK hCpos t ht
    have hstep : C ts * Real.exp (deriv C ts / C ts * (t - ts))
        ≤ C ts * Real.exp (nu * (t - ts)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCpos.le
      have := hslope t ht
      nlinarith
    have hCle : C ts ≤ expSum c a ts := hdom ts htsK
    have hstep2 : C ts * Real.exp (nu * (t - ts))
        ≤ expSum c a ts * Real.exp (nu * (t - ts)) :=
      mul_le_mul_of_nonneg_right hCle (Real.exp_pos _).le
    have hrw : Real.exp (Real.log (expSum c a ts) - nu * ts + nu * t)
        = expSum c a ts * Real.exp (nu * (t - ts)) := by
      rw [show Real.log (expSum c a ts) - nu * ts + nu * t
          = Real.log (expSum c a ts) + nu * (t - ts) from by ring, Real.exp_add,
        Real.exp_log (hRpos ts)]
    rw [hrw]
    linarith

/-- **The piecewise profile criterion, without endpoint conditions.**  Any finite cover of the
positivity set of `C` by intervals of log-tangent-domination gives an exact criterion: one
separating exponential per interval. -/
theorem le_iff_forall_separating_interval {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m)
    (hc : ∀ i, 0 < c i) {C : ℝ → ℝ} (hCcont : Continuous C)
    (hCdiff : ∀ t, DifferentiableAt ℝ C t) {n : ℕ} (u v : Fin n → ℝ) (huv : ∀ k, u k ≤ v k)
    (hlt : ∀ k, LogTangentDominated C (Icc (u k) (v k)))
    (hcover : ∀ t : ℝ, 0 < C t → ∃ k, t ∈ Icc (u k) (v k)) :
    (∀ t : ℝ, C t ≤ expSum c a t)
      ↔ ∀ k, ∃ ν L : ℝ, (∀ t : ℝ, Real.exp (L + ν * t) ≤ expSum c a t)
          ∧ ∀ t ∈ Icc (u k) (v k), C t ≤ Real.exp (L + ν * t) := by
  constructor
  · intro h k
    exact exists_separating_of_le_on_interval c a hm hc (huv k) hCcont hCdiff (hlt k)
      (fun t _ => h t)
  · intro h t
    by_cases hCt : 0 < C t
    · obtain ⟨k, hk⟩ := hcover t hCt
      obtain ⟨ν, L, hsep, hcap⟩ := h k
      exact le_trans (hcap t hk) (hsep t)
    · push Not at hCt
      exact le_trans hCt (expSum_pos c a hm hc t).le

end GaloisForLFunctions.HTGeometry
