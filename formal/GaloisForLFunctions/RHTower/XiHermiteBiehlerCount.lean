import GaloisForLFunctions.RHTower.XiDerivOffLineCount

/-!
# Hermite–Biehler count: `ξ + λξ'` and `ξ` have the same zeros to the right of the line

For `λ > 0`, `ξ + λξ' = ξ · (1 + λ ξ'/ξ)`. To the right of the critical line and outside the Speiser
disks, `Re ξ'/ξ > 0`, so the ratio `1 + λξ'/ξ` has real part `> 1` there. On the critical line
`Re ξ'/ξ = 0`, so near the line the ratio has real part close to `1`.

**Theorem** (`exists_hermiteBiehler_count_right`). For `λ > 0` and unshadowed heights `T₁ < T₂`,
`ξ + λξ'` and `ξ` have the same number of zeros, with multiplicity, in `1/2 < Re s < 2`,
`T₁ < Im s < T₂`.

**Proof.**
- On the boundary of `[1/2 + δ, 2] × [T₁, T₂]`:
  - the ratio has positive real part on the horizontal edges (strict disk criterion) and on
    `Re s = 2`;
  - on `Re s = 1/2 + δ`, for small `δ`, it has positive real part by `exists_xi_right_edge`. After
    peeling the on-line zeros of `ξ`, the remaining logarithmic derivative has zero real part on the
    line, so it is small nearby by compactness, and each on-line pole contributes
    `mδ/(δ² + (t − γ)²) ≥ 0`.
- The winding lemma (`sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg`, applied to minus the ratio)
  equates the counts.
- Under RH the count of `ξ` is zero, so `ξ + λξ'` has no zeros to the right of the line: the
  Hermite–Biehler picture.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The Hermite–Biehler combination `ξ + λξ'`. -/
def xiHermiteBiehler (lam : ℝ) (s : ℂ) : ℂ := xi s + (lam : ℂ) * deriv xi s

theorem analyticOnNhd_xiHermiteBiehler (lam : ℝ) :
    AnalyticOnNhd ℂ (xiHermiteBiehler lam) Set.univ := fun z _ =>
  (xi_analyticOnNhd_univ z trivial).add (analyticAt_const.mul (analyticOnNhd_deriv_xi z trivial))

theorem xiHermiteBiehler_eq_mul {lam : ℝ} {z : ℂ} (hz : xi z ≠ 0) :
    xiHermiteBiehler lam z = xi z * (1 + (lam : ℂ) * logDeriv xi z) := by
  rw [xiHermiteBiehler, logDeriv_apply]; field_simp

/-- **The right edge for `ξ`.** For `ε > 0` and `T₁ ≤ T₂`, there is `δ₀ > 0` such that for
`0 < δ < δ₀`, `ξ ≠ 0` and `Re ξ'/ξ > −ε` on `Re s = 1/2 + δ`, `T₁ ≤ Im s ≤ T₂`. -/
theorem exists_xi_right_edge_re_logDeriv_gt {ε T₁ T₂ : ℝ} (hε : 0 < ε) (hT : T₁ ≤ T₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ t ∈ Icc T₁ T₂,
      xi (((1 / 2 + δ : ℝ) : ℂ) + t * I) ≠ 0 ∧
        -ε < (logDeriv xi (((1 / 2 + δ : ℝ) : ℂ) + t * I)).re := by
  classical
  have hxi0 : ∃ z : ℂ, xi z ≠ 0 := ⟨0, by simpa using xi_ne_zero_of_real 0⟩
  set z₁ : ℂ := ((1 / 4 : ℝ) : ℂ) + ((T₁ - 1 : ℝ) : ℂ) * I with hz₁
  set z₂ : ℂ := ((3 / 4 : ℝ) : ℂ) + ((T₂ + 1 : ℝ) : ℂ) * I with hz₂
  have hfin := entire_zeros_closedRectangle_finite xi_analyticOnNhd_univ hxi0 z₁ z₂
  set Zf := hfin.toFinset with hZf
  have hbox : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 / 4 → T₁ - 1 ≤ z.im → z.im ≤ T₂ + 1 →
      xi z = 0 → z ∈ Zf := by
    intro z h1 h2 h3 h4 hz
    rw [hZf, Set.Finite.mem_toFinset, Set.mem_sep_iff]
    refine ⟨?_, hz⟩
    rw [Complex.mem_reProdIm]
    have e1 : z₁.re = 1 / 4 := by simp [hz₁]
    have e2 : z₂.re = 3 / 4 := by simp [hz₂]
    have e3 : z₁.im = T₁ - 1 := by simp [hz₁]
    have e4 : z₂.im = T₂ + 1 := by simp [hz₂]
    rw [e1, e2, e3, e4, uIcc_of_le (by norm_num), uIcc_of_le (by linarith)]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  obtain ⟨η₁, hη₁, hη₁le⟩ := exists_pos_le_of_finset (Zf.filter fun w => w.re ≠ 1 / 2)
    (fun w => |w.re - 1 / 2|) (fun w hw => abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hw).2))
  set η : ℝ := min η₁ (1 / 4) with hη
  have hη0 : 0 < η := lt_min hη₁ (by norm_num)
  have hηle : η ≤ 1 / 4 := min_le_right _ _
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  set U : Set ℂ := {z : ℂ | |z.re - 1 / 2| < η / 2 ∧ T₁ - 1 / 2 < z.im ∧ z.im < T₂ + 1 / 2}
    with hUdef
  have hUopen : IsOpen U := by
    refine (isOpen_lt (f := fun z : ℂ => |z.re - 1 / 2|) (g := fun _ => η / 2) (by fun_prop)
      continuous_const).inter ((isOpen_lt (f := fun _ : ℂ => T₁ - 1 / 2) (g := fun z : ℂ => z.im)
        continuous_const (by fun_prop)).inter (isOpen_lt (f := fun z : ℂ => z.im)
          (g := fun _ => T₂ + 1 / 2) (by fun_prop) continuous_const))
  set ton : Finset ℂ := Zf.filter (· ∈ U) with hton
  have hzeroU : ∀ z ∈ U, xi z = 0 → z ∈ ton := by
    intro z hz hx
    have hr := abs_lt.mp hz.1
    refine Finset.mem_filter.mpr ⟨hbox z (by linarith) (by linarith) (by linarith [hz.2.1])
      (by linarith [hz.2.2]) hx, hz⟩
  have hon : ∀ w ∈ ton, w.re = 1 / 2 := by
    intro w hw
    obtain ⟨hwZ, hwU⟩ := Finset.mem_filter.mp hw
    by_contra hne
    have := hη₁le w (Finset.mem_filter.mpr ⟨hwZ, hne⟩)
    have := hwU.1
    linarith
  have hord : ∀ w ∈ ton, analyticOrderAt xi w ≠ ⊤ := fun w _ =>
    DeBruijn.analyticOrderAt_ne_top_of_ne_zero xi_analyticOnNhd_univ
      (by simpa using xi_ne_zero_of_real 0) w
  obtain ⟨m, h, hh, -, hh0, hfact⟩ := exists_finite_peel hUopen
    (fun z _ => xi_analyticOnNhd_univ z trivial) ton (fun w hw => (Finset.mem_filter.mp hw).2) hord
  have hhne : ∀ z ∈ U, h z ≠ 0 := by
    intro z hz
    by_cases hzt : z ∈ ton
    · exact hh0 z hzt
    · intro h0
      have : xi z = 0 := by rw [hfact z hz, h0, mul_zero]
      exact hzt (hzeroU z hz this)
  have hdecomp : ∀ z ∈ U, z ∉ ton →
      logDeriv xi z = (∑ w ∈ ton, (m w : ℂ) / (z - w)) + logDeriv h z := by
    intro z hz hzt
    have hev : xi =ᶠ[𝓝 z] fun y => (∏ w ∈ ton, (y - w) ^ m w) * h y := by
      filter_upwards [hUopen.mem_nhds hz] with y hy
      exact hfact y hy
    have hzw : ∀ w ∈ ton, z - w ≠ 0 := fun w hw h0 => hzt (by rwa [sub_eq_zero.mp h0])
    have hP : (∏ w ∈ ton, (z - w) ^ m w) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (hzw w hw)
    rw [logDeriv_eq_of_germ_eq hev,
      logDeriv_mul z hP (hhne z hz) (by fun_prop) (hh z hz).differentiableAt,
      logDeriv_prod (f := fun w y => (y - w) ^ m w) (fun w hw => pow_ne_zero _ (hzw w hw))
        (fun w _ => by fun_prop)]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply, deriv_sub_const, deriv_id'', mul_one_div]
  have hcont : ContinuousOn (fun z => (logDeriv h z).re) U := fun z hz =>
    (Complex.continuous_re.continuousAt.comp
      (continuousAt_logDeriv_of_analyticAt (hh z hz) (hhne z hz))).continuousWithinAt
  set p : ℝ → ℂ := fun t => ((1 / 2 : ℝ) : ℂ) + t * I with hp
  have hpcont : Continuous p := by rw [hp]; fun_prop
  have hpre : ∀ t, (p t).re = 1 / 2 := fun t => by simp [hp]
  have hpim : ∀ t, (p t).im = t := fun t => by simp [hp]
  have hpU : ∀ t, T₁ - 1 / 2 < t → t < T₂ + 1 / 2 → p t ∈ U := fun t h1 h2 => by
    refine ⟨?_, by rw [hpim]; exact h1, by rw [hpim]; exact h2⟩
    rw [hpre, sub_self, abs_zero]; linarith
  -- on the line away from the zeros, `Re h'/h = 0`
  have hgood : ∀ t, T₁ - 1 / 2 < t → t < T₂ + 1 / 2 → p t ∉ ton → (logDeriv h (p t)).re = 0 := by
    intro t h1 h2 hpt
    have hsplit := hdecomp (p t) (hpU t h1 h2) hpt
    have hpole : (∑ w ∈ ton, (m w : ℂ) / (p t - w)).re = 0 := by
      rw [Complex.re_sum]
      refine Finset.sum_eq_zero fun w hw => ?_
      have hd : p t - w = ((t - w.im : ℝ) : ℂ) * I := by
        apply Complex.ext
        · simp [hp, hon w hw]
        · simp [hp]
      rw [hd]
      simp [Complex.div_re]
    have hline := re_logDeriv_xi_eq_zero_of_re_eq_half (s := p t) (hpre t)
    rw [hsplit, Complex.add_re, hpole, zero_add] at hline
    exact hline
  have hseg : ∀ t ∈ Icc T₁ T₂, (logDeriv h (p t)).re = 0 := by
    intro t ht
    have hU' : p t ∈ U := hpU t (by linarith [ht.1]) (by linarith [ht.2])
    have hca : ContinuousAt (fun u => (logDeriv h (p u)).re) t :=
      ((hcont (p t) hU').continuousAt (hUopen.mem_nhds hU')).comp (f := p) hpcont.continuousAt
    have hfinpre : {u : ℝ | p u ∈ ton}.Finite := by
      refine (ton.finite_toSet.preimage ?_)
      intro u _ v _ huv
      have := congrArg Complex.im huv
      rwa [hpim, hpim] at this
    have hev : ∀ᶠ u in 𝓝[≠] t, (logDeriv h (p u)).re = 0 := by
      have hc : ({u : ℝ | p u ∈ ton} \ {t})ᶜ ∈ 𝓝 t :=
        ((hfinpre.subset Set.sdiff_subset).isClosed).compl_mem_nhds (fun h => h.2 rfl)
      have hball : Ioo (t - 1 / 2) (t + 1 / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [nhdsWithin_le_nhds hc, nhdsWithin_le_nhds hball, self_mem_nhdsWithin]
        with u hu hub hne
      exact hgood u (by linarith [hub.1, ht.1]) (by linarith [hub.2, ht.2])
        fun hmem => hu ⟨hmem, hne⟩
    exact tendsto_nhds_unique (hca.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun u hu => hu.symm))
  -- compactness: `|Re h'/h| < ε` on a thickening
  set S : Set ℂ := p '' Icc T₁ T₂ with hS
  have hScpt : IsCompact S := isCompact_Icc.image hpcont
  set O : Set ℂ := U ∩ (fun z => (logDeriv h z).re) ⁻¹' Ioo (-ε) ε with hO
  have hOopen : IsOpen O := hcont.isOpen_inter_preimage hUopen isOpen_Ioo
  have hSO : S ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨hpU t (by linarith [ht.1]) (by linarith [ht.2]), ?_⟩
    show (logDeriv h (p t)).re ∈ Ioo _ _
    rw [hseg t ht]
    exact ⟨by linarith, hε⟩
  obtain ⟨κ, hκ, hsub⟩ := hScpt.exists_cthickening_subset_open hOopen hSO
  refine ⟨min κ (η / 2), lt_min hκ (by linarith), fun δ hδ hδ₀ t ht => ?_⟩
  set z : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + t * I with hzdef
  have hzre : z.re = 1 / 2 + δ := by simp [hzdef]
  have hzO : z ∈ O := by
    apply hsub
    refine Metric.mem_cthickening_of_dist_le z (p t) κ S ⟨t, ht, rfl⟩ ?_
    have : z - p t = ((δ : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hzdef, hp]
      · simp [hzdef, hp]
    rw [dist_eq_norm, this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    linarith [min_le_left κ (η / 2)]
  have hzt : z ∉ ton := fun hmem => by
    have := hon z hmem; rw [hzre] at this; linarith
  have hxz : xi z ≠ 0 := fun h0 => hzt (hzeroU z hzO.1 h0)
  refine ⟨hxz, ?_⟩
  have hpole : 0 ≤ ∑ w ∈ ton, ((m w : ℂ) / (z - w)).re := by
    refine Finset.sum_nonneg fun w hw => ?_
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [Complex.sub_re, hzre, hon w hw]; linarith
  have hre : (logDeriv xi z).re ≥ (logDeriv h z).re := by
    rw [hdecomp z hzO.1 hzt, Complex.add_re, Complex.re_sum]; linarith
  have hlow : -ε < (logDeriv h z).re := hzO.2.1
  linarith

/-- For `λ > 0` and small `δ`, `Re(1 + λξ'/ξ) > 0` on the segment `Re s = 1/2 + δ`,
`T₁ ≤ Im s ≤ T₂`. -/
theorem exists_xi_right_edge {lam T₁ T₂ : ℝ} (hlam : 0 < lam) (hT : T₁ ≤ T₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ t ∈ Icc T₁ T₂,
      xi (((1 / 2 + δ : ℝ) : ℂ) + t * I) ≠ 0 ∧
        0 < (1 + (lam : ℂ) * logDeriv xi (((1 / 2 + δ : ℝ) : ℂ) + t * I)).re := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_xi_right_edge_re_logDeriv_gt (ε := 1 / (2 * lam)) (by positivity) hT
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ t ht => ⟨(h δ hδ hδδ t ht).1, ?_⟩⟩
  have hlow := (h δ hδ hδδ t ht).2
  have hre1 : (1 + (lam : ℂ) * logDeriv xi (((1 / 2 + δ : ℝ) : ℂ) + t * I)).re =
      1 + lam * (logDeriv xi (((1 / 2 + δ : ℝ) : ℂ) + t * I)).re := by simp
  rw [hre1]
  have : lam * (-(1 / (2 * lam))) = -(1 / 2) := by field_simp
  nlinarith

/-- The boundary relation for `ξ + λξ'` against `ξ`, with `g = −(1 + λξ'/ξ)`. -/
theorem ratioLeftBoundary_xiHermiteBiehler {lam : ℝ} {z : ℂ} (hz : xi z ≠ 0)
    (hpos : 0 < (1 + (lam : ℂ) * logDeriv xi z).re) :
    RatioLeftBoundary (xiHermiteBiehler lam) xi (fun w => -(1 + (lam : ℂ) * logDeriv xi w)) z := by
  have hq0 : (1 + (lam : ℂ) * logDeriv xi z) ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hpos; exact lt_irrefl 0 hpos
  have hA := xi_analyticOnNhd_univ z trivial
  have hqA : AnalyticAt ℂ (fun w => 1 + (lam : ℂ) * logDeriv xi w) z :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_logDeriv_xi hz))
  refine ⟨by rw [xiHermiteBiehler_eq_mul hz]; exact mul_ne_zero hz hq0, hz, hqA.neg,
    by simp only [Complex.neg_re]; linarith, ?_⟩
  have hev : xiHermiteBiehler lam =ᶠ[𝓝 z] fun w => xi w * (1 + (lam : ℂ) * logDeriv xi w) := by
    filter_upwards [hA.continuousAt.eventually_ne hz] with w hw
    exact xiHermiteBiehler_eq_mul hw
  rw [logDeriv_eq_of_germ_eq hev, logDeriv_mul z hz hq0 hA.differentiableAt hqA.differentiableAt,
    logDeriv_neg_fun (fun w => 1 + (lam : ℂ) * logDeriv xi w)]
  ring

/-- The window `1/2 < Re s < 2`, `T₁ < Im s < T₂`. -/
def rightHalfWindow (T₁ T₂ : ℝ) (w : ℂ) : Prop :=
  1 / 2 < w.re ∧ w.re < 2 ∧ T₁ < w.im ∧ w.im < T₂

/-- **Hermite–Biehler count.** For `λ > 0` and unshadowed heights `T₁ < T₂`, `ξ + λξ'` and `ξ`
have the same number of zeros, with multiplicity, in `1/2 < Re s < 2`, `T₁ < Im s < T₂`. -/
theorem exists_hermiteBiehler_count_right {lam T₁ T₂ : ℝ} (hlam : 0 < lam) (hT : T₁ < T₂)
    (hu₁ : SpeiserUnshadowed T₁) (hu₂ : SpeiserUnshadowed T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ w : ℂ, w ∈ Z₁ ↔ rightHalfWindow T₁ T₂ w ∧ xiHermiteBiehler lam w = 0) ∧
      (∀ w : ℂ, w ∈ Z₀ ↔ rightHalfWindow T₁ T₂ w ∧ xi w = 0) ∧
      ∑ w ∈ Z₁, (analyticOrderAt (xiHermiteBiehler lam) w).toNat =
        ∑ w ∈ Z₀, (analyticOrderAt xi w).toNat := by
  classical
  -- positivity of the ratio right of the line at an unshadowed height, and on `Re s = 2`
  have hhor : ∀ T : ℝ, SpeiserUnshadowed T → ∀ x : ℝ, 1 / 2 < x →
      xi ((x : ℂ) + T * I) ≠ 0 ∧ 0 < (1 + (lam : ℂ) * logDeriv xi ((x : ℂ) + T * I)).re := by
    intro T hu x hx
    have hre : ((x : ℂ) + T * I).re = x := by simp
    have him : ((x : ℂ) + T * I).im = T := by simp
    have hxi := xi_ne_zero_of_speiserUnshadowed (x := x) hu (ne_of_gt hx)
    have hpos : 0 < (logDeriv xi ((x : ℂ) + T * I)).re :=
      re_logDeriv_xi_pos_of_disk_bound (by rw [hre]; exact hx) hxi fun q => by
        have h1 := hu (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)
        rw [hre, him]
        have h2 : 0 < (x - 1 / 2) ^ 2 := by
          have : x - 1 / 2 ≠ 0 := by linarith
          positivity
        linarith
    refine ⟨hxi, ?_⟩
    have : (1 + (lam : ℂ) * logDeriv xi ((x : ℂ) + T * I)).re =
        1 + lam * (logDeriv xi ((x : ℂ) + T * I)).re := by simp
    rw [this]; nlinarith
  have hright : ∀ t : ℝ, xi (((2 : ℝ) : ℂ) + t * I) ≠ 0 ∧
      0 < (1 + (lam : ℂ) * logDeriv xi (((2 : ℝ) : ℂ) + t * I)).re := by
    intro t
    have h1 : (1 : ℝ) ≤ (((2 : ℝ) : ℂ) + t * I).re := by norm_num
    have hpos := re_logDeriv_xi_pos_of_one_le_re h1
    refine ⟨xi_ne_zero_of_one_le_re h1, ?_⟩
    have : (1 + (lam : ℂ) * logDeriv xi (((2 : ℝ) : ℂ) + t * I)).re =
        1 + lam * (logDeriv xi (((2 : ℝ) : ℂ) + t * I)).re := by simp
    rw [this]; nlinarith
  obtain ⟨δ₀, hδ₀, hedge⟩ := exists_xi_right_edge hlam hT.le
  -- finitely many zeros of both functions in `[1/2, 2] × [T₁, T₂]`
  set V := xiHermiteBiehler lam with hV
  have hnV : ∃ z : ℂ, V z ≠ 0 := by
    refine ⟨((2 : ℝ) : ℂ) + (0 : ℝ) * I, ?_⟩
    obtain ⟨hx, hp⟩ := hright 0
    rw [hV, xiHermiteBiehler_eq_mul hx]
    refine mul_ne_zero hx fun h => ?_
    rw [h, Complex.zero_re] at hp; exact lt_irrefl 0 hp
  have hnX : ∃ z : ℂ, xi z ≠ 0 := ⟨0, by simpa using xi_ne_zero_of_real 0⟩
  set b₁ : ℂ := ((1 / 2 : ℝ) : ℂ) + T₁ * I with hb₁
  set b₂ : ℂ := ((2 : ℝ) : ℂ) + T₂ * I with hb₂
  have hb : b₁.re = 1 / 2 ∧ b₂.re = 2 ∧ b₁.im = T₁ ∧ b₂.im = T₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hb₁, hb₂]
  have hfinV := entire_zeros_closedRectangle_finite (analyticOnNhd_xiHermiteBiehler lam) hnV b₁ b₂
  have hfinX := entire_zeros_closedRectangle_finite xi_analyticOnNhd_univ hnX b₁ b₂
  set W : Finset ℂ := (hfinV.toFinset ∪ hfinX.toFinset).filter (fun w => 1 / 2 < w.re) with hW
  obtain ⟨η₂, hη₂, hη₂le⟩ := exists_pos_le_of_finset W (fun w => w.re - 1 / 2)
    (fun w hw => by have := (Finset.mem_filter.mp hw).2; show 0 < w.re - 1 / 2; linarith)
  have hinW : ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 2 → T₁ ≤ w.im → w.im ≤ T₂ →
      (V w = 0 ∨ xi w = 0) → w ∈ W := by
    intro w h1 h2 h3 h4 hz
    have hbox : w ∈ (uIcc b₁.re b₂.re ×ℂ uIcc b₁.im b₂.im) := by
      rw [Complex.mem_reProdIm, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, uIcc_of_le (by norm_num),
        uIcc_of_le hT.le]
      exact ⟨⟨h1.le, h2⟩, ⟨h3, h4⟩⟩
    refine Finset.mem_filter.mpr ⟨?_, h1⟩
    rcases hz with hz | hz
    · exact Finset.mem_union_left _ (hfinV.mem_toFinset.mpr ⟨hbox, hz⟩)
    · exact Finset.mem_union_right _ (hfinX.mem_toFinset.mpr ⟨hbox, hz⟩)
  set δ : ℝ := min (min δ₀ η₂) (1 / 4) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδδ₀ : δ < δ₀ := by
    have := min_le_left (min δ₀ η₂) (1 / 4); have := min_le_left δ₀ η₂; linarith
  have hδη : δ < η₂ := by
    have := min_le_left (min δ₀ η₂) (1 / 4); have := min_le_right δ₀ η₂; linarith
  have hδ8 : δ ≤ 1 / 8 := by have := min_le_right (min δ₀ η₂) (1 / 4); linarith
  set c : ℝ := 1 / 2 + δ with hc
  have hc2 : c < 2 := by linarith
  have hne1 : ∀ (x t : ℝ), xi ((x : ℂ) + t * I) ≠ 0 →
      0 < (1 + (lam : ℂ) * logDeriv xi ((x : ℂ) + t * I)).re →
      RatioLeftBoundary V xi (fun w => -(1 + (lam : ℂ) * logDeriv xi w)) ((x : ℂ) + t * I) :=
    fun x t h1 h2 => ratioLeftBoundary_xiHermiteBiehler h1 h2
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, hsum⟩ := sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg
    (analyticOnNhd_xiHermiteBiehler lam) xi_analyticOnNhd_univ hnV hnX hc2 hT
    (fun x hx => by
      rw [uIcc_of_le hc2.le] at hx
      obtain ⟨a, b⟩ := hhor T₁ hu₁ x (by linarith [hx.1])
      exact hne1 x T₁ a b)
    (fun x hx => by
      rw [uIcc_of_le hc2.le] at hx
      obtain ⟨a, b⟩ := hhor T₂ hu₂ x (by linarith [hx.1])
      exact hne1 x T₂ a b)
    (fun t _ => by obtain ⟨a, b⟩ := hright t; exact hne1 2 t a b)
    (fun t ht => by
      rw [uIcc_of_le hT.le] at ht
      obtain ⟨a, b⟩ := hedge δ hδ0 hδδ₀ t ht
      exact hne1 c t a b)
  have hsplit : ∀ w : ℂ, w = (w.re : ℂ) + w.im * I := fun w => (Complex.re_add_im w).symm
  -- boundary points are not zeros
  have hbd : ∀ w : ℂ, w ∈ (uIcc c 2 ×ℂ uIcc T₁ T₂) → (V w = 0 ∨ xi w = 0) →
      rightHalfWindow T₁ T₂ w := by
    intro w hmem hz
    rw [Complex.mem_reProdIm, uIcc_of_le hc2.le, uIcc_of_le hT.le] at hmem
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hmem
    have hkill : ∀ x t : ℝ, xi ((x : ℂ) + t * I) ≠ 0 →
        0 < (1 + (lam : ℂ) * logDeriv xi ((x : ℂ) + t * I)).re →
        w = (x : ℂ) + t * I → False := by
      intro x t hx hp hw
      have hR := ratioLeftBoundary_xiHermiteBiehler hx hp
      rw [← hw] at hR
      rcases hz with hz | hz
      · exact hR.1 hz
      · exact hR.2.1 hz
    have hne_lo : w.im ≠ T₁ := fun h => by
      obtain ⟨a, b⟩ := hhor T₁ hu₁ w.re (by linarith)
      exact hkill w.re T₁ a b (by rw [← h]; exact hsplit w)
    have hne_hi : w.im ≠ T₂ := fun h => by
      obtain ⟨a, b⟩ := hhor T₂ hu₂ w.re (by linarith)
      exact hkill w.re T₂ a b (by rw [← h]; exact hsplit w)
    have hne_2 : w.re ≠ 2 := fun h => by
      obtain ⟨a, b⟩ := hright w.im
      exact hkill 2 w.im a b (by rw [← h]; exact hsplit w)
    exact ⟨by linarith, lt_of_le_of_ne h2 hne_2, lt_of_le_of_ne h3 (Ne.symm hne_lo),
      lt_of_le_of_ne h4 hne_hi⟩
  have hinside : ∀ w : ℂ, rightHalfWindow T₁ T₂ w → (V w = 0 ∨ xi w = 0) →
      w ∈ (uIcc c 2 ×ℂ uIcc T₁ T₂) := by
    intro w hw hz
    have hwW := hη₂le w (hinW w hw.1 hw.2.1.le hw.2.2.1.le hw.2.2.2.le hz)
    rw [Complex.mem_reProdIm, uIcc_of_le hc2.le, uIcc_of_le hT.le]
    exact ⟨⟨by linarith, hw.2.1.le⟩, ⟨hw.2.2.1.le, hw.2.2.2.le⟩⟩
  refine ⟨Z₁, Z₀, fun w => ?_, fun w => ?_, hsum⟩
  · rw [hZ₁ w]
    exact ⟨fun ⟨hm, hz⟩ => ⟨hbd w hm (Or.inl hz), hz⟩,
      fun ⟨hw, hz⟩ => ⟨hinside w hw (Or.inl hz), hz⟩⟩
  · rw [hZ₀ w]
    exact ⟨fun ⟨hm, hz⟩ => ⟨hbd w hm (Or.inr hz), hz⟩,
      fun ⟨hw, hz⟩ => ⟨hinside w hw (Or.inr hz), hz⟩⟩

/-- **Under RH, `ξ + λξ'` has no zeros right of the line** (between unshadowed heights), and in
general its right zeros are equinumerous with the off-line right zeros of `ξ`. -/
theorem xiHermiteBiehler_ne_zero_right_of_re_zeros (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2)
    {lam : ℝ} (hlam : 0 < lam) {s : ℂ} (hs : 1 / 2 < s.re) :
    xiHermiteBiehler lam s ≠ 0 := by
  have hxi : xi s ≠ 0 := fun h => by have := hRH s h; linarith
  have hpos : 0 < (logDeriv xi s).re := re_logDeriv_xi_pos_of_disk_bound hs hxi fun q => by
    rw [hRH (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1), sub_self, zero_pow two_ne_zero]
    have : s.re - 1 / 2 ≠ 0 := by linarith
    have := pow_pos (abs_pos.mpr this) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (s.im - (q.1 : ℂ).im)]
  rw [xiHermiteBiehler_eq_mul hxi]
  refine mul_ne_zero hxi fun h => ?_
  have := congrArg Complex.re h
  simp at this
  nlinarith

end

end RHTower
