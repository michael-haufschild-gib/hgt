import GaloisForLFunctions.RHTower.SpeiserLocalDisk
import GaloisForLFunctions.RHTower.RectangleLeftHalfPlaneWinding
import GaloisForLFunctions.RHTower.FinitePeeling
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic

/-!
# Exact Speiser count between unshadowed heights

A height `T` is *unshadowed* if `(Re ρ − 1/2)² ≤ (T − Im ρ)²` for every zero `ρ` of `ξ`, i.e. `T`
lies in no shadow `[Im ρ − |Re ρ − 1/2|, Im ρ + |Re ρ − 1/2|]`.

**Theorem** (`exists_speiser_count_eq`). For unshadowed heights `101 ≤ T₁ < T₂`, `ζ` and `ζ'`
have the same number of zeros, counted with multiplicity, in `0 < Re s < 1/2`, `T₁ < Im s < T₂`.

**Proof.** On the boundary of `[c, 1/2 − δ] × [T₁, T₂]`, with `c = 1/(60 log(T₂ + 1))` and small
`δ > 0`, `Re ζ'/ζ < 0`:
- on the horizontal edges by the Speiser disk bound (`re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk`);
- on the left edge because no Speiser disk reaches `Re s = c` (`speiserDisk_strict_of_re_lt`);
- on the right edge by `exists_right_edge_re_logDeriv_neg`. On the critical line
  `2 Re ζ'/ζ = Re χ'/χ < 0`, the on-line zeros contribute purely imaginary poles, and compactness
  moves the sign to `Re s = 1/2 − δ`, where each pole contributes `−mδ/(δ² + (t − γ)²) ≤ 0`.

So the ratio of the entire functions `(s − 1)²ζ'` and `(s − 1)²ζ` stays in the left half-plane on
the boundary, and the winding lemma (`sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg`) equates the
two zero counts.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- A finite family of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ η : ℝ, 0 < η ∧ ∀ i ∈ s, η ≤ f i := by
  rcases s.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨i, hi, hmin⟩ := s.exists_min_image f h
    exact ⟨f i, hf i hi, hmin⟩

/-- On the critical line, `2 Re ζ'/ζ = Re χ'/χ` wherever `ζ ≠ 0`. -/
theorem two_mul_re_logDeriv_riemannZeta_criticalLine {t : ℝ}
    (hζ : riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0) :
    2 * (logDeriv riemannZeta ((1 / 2 : ℂ) + t * I)).re =
      (logDeriv zetaChi ((1 / 2 : ℂ) + t * I)).re := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hconj : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext
    · simp [hs]; norm_num
    · simp [hs]
  have h1s : riemannZeta (1 - s) ≠ 0 := by
    rw [hconj, riemannZeta_conj]; exact (map_ne_zero _).mpr hζ
  have hrefl := logDeriv_riemannZeta_add_reflect_of_strip (by rw [hsre]; norm_num)
    (by rw [hsre]; norm_num) hζ h1s
  have hchi := logDeriv_zetaChi_off_poles (div_two_ne_neg_nat_of_re_pos (by rw [hsre]; norm_num))
    (div_two_ne_neg_nat_of_re_pos (by rw [Complex.sub_re, Complex.one_re, hsre]; norm_num))
  have hL : logDeriv riemannZeta s = logDeriv zetaChi s - logDeriv riemannZeta (1 - s) := by
    rw [hchi]; linear_combination hrefl
  have hc : logDeriv riemannZeta (1 - s) = (starRingEnd ℂ) (logDeriv riemannZeta s) := by
    rw [hconj, logDeriv_riemannZeta_conj]
  have h := congrArg Complex.re hL
  rw [Complex.sub_re, hc, Complex.conj_re] at h
  linarith

/-- The logarithmic derivative only depends on the germ. -/
theorem logDeriv_eq_of_germ_eq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- `Re (m / (x + i y)) ≤ 0` for `x ≤ 0` and `m ≥ 0`. -/
theorem re_natCast_div_le_zero {m : ℕ} {z : ℂ} (hz : z.re ≤ 0) : ((m : ℂ) / z).re ≤ 0 := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hz)
    (Complex.normSq_nonneg _)

/-- **The right edge.** For `101 ≤ T₁ ≤ T₂` there is `δ₀ > 0` such that for `0 < δ < δ₀`,
`ζ ≠ 0` and `Re ζ'/ζ < 0` on the segment `Re s = 1/2 − δ`, `T₁ ≤ Im s ≤ T₂`. -/
theorem exists_right_edge_re_logDeriv_neg {T₁ T₂ : ℝ} (h101 : 101 ≤ T₁) (hT : T₁ ≤ T₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ t ∈ Icc T₁ T₂,
      riemannZeta (((1 / 2 - δ : ℝ) : ℂ) + t * I) ≠ 0 ∧
        (logDeriv riemannZeta (((1 / 2 - δ : ℝ) : ℂ) + t * I)).re < 0 := by
  classical
  -- the zeros of `ζ` in a box around the segment
  set z₁ : ℂ := ((1 / 4 : ℝ) : ℂ) + ((T₁ - 1 : ℝ) : ℂ) * I with hz₁
  set z₂ : ℂ := ((3 / 4 : ℝ) : ℂ) + ((T₂ + 1 : ℝ) : ℂ) * I with hz₂
  have hfin := RHTower.Sieve.zetaResidueUnit_zeros_closedRectangle_finite z₁ z₂
  set Zf := hfin.toFinset with hZf
  have hbox : ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 / 4 → T₁ - 1 ≤ z.im → z.im ≤ T₂ + 1 →
      riemannZeta z = 0 → z ∈ Zf := by
    intro z h1 h2 h3 h4 hz
    have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_im] at h3; linarith
    rw [hZf, Set.Finite.mem_toFinset, Set.mem_sep_iff]
    refine ⟨?_, ?_⟩
    · rw [Complex.mem_reProdIm]
      have e1 : z₁.re = 1 / 4 := by simp [hz₁]
      have e2 : z₂.re = 3 / 4 := by simp [hz₂]
      have e3 : z₁.im = T₁ - 1 := by simp [hz₁]
      have e4 : z₂.im = T₂ + 1 := by simp [hz₂]
      rw [e1, e2, e3, e4, uIcc_of_le (by norm_num), uIcc_of_le (by linarith)]
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · rw [(zetaResidueUnit_eventuallyEq hz1).eq_of_nhds, hz, mul_zero]
  -- a positive gap from the line for the off-line zeros of the box
  obtain ⟨η₁, hη₁, hη₁le⟩ := exists_pos_le_of_finset (Zf.filter fun w => w.re ≠ 1 / 2)
    (fun w => |w.re - 1 / 2|) (fun w hw => abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hw).2))
  set η : ℝ := min η₁ (1 / 4) with hη
  have hη0 : 0 < η := lt_min hη₁ (by norm_num)
  have hηle : η ≤ 1 / 4 := min_le_right _ _
  have hηη₁ : η ≤ η₁ := min_le_left _ _
  -- the thin open neighbourhood of the segment
  set U : Set ℂ := {z : ℂ | |z.re - 1 / 2| < η / 2 ∧ T₁ - 1 / 2 < z.im ∧ z.im < T₂ + 1 / 2}
    with hUdef
  have hUopen : IsOpen U := by
    refine (isOpen_lt (f := fun z : ℂ => |z.re - 1 / 2|) (g := fun _ => η / 2) (by fun_prop)
      continuous_const).inter ((isOpen_lt (f := fun _ : ℂ => T₁ - 1 / 2) (g := fun z : ℂ => z.im)
        continuous_const (by fun_prop)).inter (isOpen_lt (f := fun z : ℂ => z.im)
          (g := fun _ => T₂ + 1 / 2) (by fun_prop) continuous_const))
  have hU1 : ∀ z ∈ U, z ≠ 1 := fun z hz h => by
    have := hz.2.1; rw [h, Complex.one_im] at this; linarith
  have hζU : AnalyticOnNhd ℂ riemannZeta U := fun z hz =>
    GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta (hU1 z hz)
  set ton : Finset ℂ := Zf.filter (· ∈ U) with hton
  have hzeroU : ∀ z ∈ U, riemannZeta z = 0 → z ∈ ton := by
    intro z hz hζ
    have hr := abs_lt.mp hz.1
    refine Finset.mem_filter.mpr ⟨hbox z (by linarith) (by linarith) (by linarith [hz.2.1])
      (by linarith [hz.2.2]) hζ, hz⟩
  have hon : ∀ w ∈ ton, w.re = 1 / 2 := by
    intro w hw
    obtain ⟨hwZ, hwU⟩ := Finset.mem_filter.mp hw
    by_contra hne
    have := hη₁le w (Finset.mem_filter.mpr ⟨hwZ, hne⟩)
    have := hwU.1
    linarith
  have hord : ∀ w ∈ ton, analyticOrderAt riemannZeta w ≠ ⊤ := by
    intro w hw htop
    have hw1 : w ≠ 1 := hU1 w (Finset.mem_filter.mp hw).2
    have hA := RHTower.Sieve.zetaResidueUnit_order_ne_top w
    rw [analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hw1)] at hA
    have hmul : analyticOrderAt ((fun s : ℂ => s - 1) * riemannZeta) w =
        analyticOrderAt (fun s : ℂ => s - 1) w + analyticOrderAt riemannZeta w :=
      analyticOrderAt_mul (by fun_prop) (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1)
    apply hA
    change analyticOrderAt ((fun s : ℂ => s - 1) * riemannZeta) w = ⊤
    rw [hmul, htop]
    simp
  obtain ⟨m, h, hh, -, hh0, hfact⟩ := exists_finite_peel hUopen hζU ton
    (fun w hw => (Finset.mem_filter.mp hw).2) hord
  have hhne : ∀ z ∈ U, h z ≠ 0 := by
    intro z hz
    by_cases hzt : z ∈ ton
    · exact hh0 z hzt
    · intro h0
      have : riemannZeta z = 0 := by rw [hfact z hz, h0, mul_zero]
      exact hzt (hzeroU z hz this)
  -- the logarithmic derivative splits into the pole part and `h'/h`
  have hdecomp : ∀ z ∈ U, z ∉ ton →
      logDeriv riemannZeta z = (∑ w ∈ ton, (m w : ℂ) / (z - w)) + logDeriv h z := by
    intro z hz hzt
    have hev : riemannZeta =ᶠ[𝓝 z] fun y => (∏ w ∈ ton, (y - w) ^ m w) * h y := by
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
  -- continuity of `Re h'/h` on `U`
  have hcont : ContinuousOn (fun z => (logDeriv h z).re) U := fun z hz =>
    (Complex.continuous_re.continuousAt.comp
      (continuousAt_logDeriv_of_analyticAt (hh z hz) (hhne z hz))).continuousWithinAt
  -- the line segment
  set p : ℝ → ℂ := fun t => ((1 / 2 : ℝ) : ℂ) + t * I with hp
  have hpcont : Continuous p := by rw [hp]; fun_prop
  have hpre : ∀ t, (p t).re = 1 / 2 := fun t => by simp [hp]
  have hpim : ∀ t, (p t).im = t := fun t => by simp [hp]
  have hpU : ∀ t, T₁ - 1 / 2 < t → t < T₂ + 1 / 2 → p t ∈ U := fun t h1 h2 => by
    refine ⟨?_, by rw [hpim]; exact h1, by rw [hpim]; exact h2⟩
    rw [hpre, sub_self, abs_zero]; linarith
  -- off the zeros the bound comes from the chi factor
  have hgood : ∀ t, 100 ≤ t → T₁ - 1 / 2 < t → t < T₂ + 1 / 2 → p t ∉ ton →
      (logDeriv h (p t)).re ≤ -1 / 2 := by
    intro t ht h1 h2 hpt
    have hU' := hpU t h1 h2
    have hζ : riemannZeta (p t) ≠ 0 := fun h0 => hpt (hzeroU _ hU' h0)
    have hsplit := hdecomp (p t) hU' hpt
    have hpole : (∑ w ∈ ton, (m w : ℂ) / (p t - w)).re = 0 := by
      rw [Complex.re_sum]
      refine Finset.sum_eq_zero fun w hw => ?_
      have hd : p t - w = ((t - w.im : ℝ) : ℂ) * I := by
        apply Complex.ext
        · simp [hp, hon w hw]
        · simp [hp]
      rw [hd]
      simp [Complex.div_re]
    have hline : riemannZeta ((1 / 2 : ℂ) + t * I) ≠ 0 := by
      have : p t = (1 / 2 : ℂ) + t * I := by simp [hp]
      rwa [← this]
    have h2re := two_mul_re_logDeriv_riemannZeta_criticalLine hline
    have hchi := re_logDeriv_zetaChi_le (s := (1 / 2 : ℂ) + t * I) (by simp)
      (by norm_num) (by simpa using ht)
    have hpeq : p t = (1 / 2 : ℂ) + t * I := by simp [hp]
    rw [hpeq] at hsplit
    have hlog := one_fifth_lt_log_div_two_pi ht
    have hlog2 : 2 < Real.log (t / (2 * Real.pi)) := by
      have hπ := Real.pi_lt_d2
      have hx : 15 ≤ t / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have := Real.add_one_le_exp 2
      have h7 : Real.exp 2 < 15 := by
        have := Real.exp_one_lt_d9
        have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [e]; nlinarith [Real.exp_pos 1]
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      linarith
    have hims : ((1 / 2 : ℂ) + t * I).im = t := by simp
    rw [hims] at hchi
    rw [hpeq] at hpole
    rw [hsplit, Complex.add_re, hpole] at h2re
    rw [hpeq]
    linarith
  -- by continuity also at the zeros on the segment
  have hseg : ∀ t ∈ Icc T₁ T₂, (logDeriv h (p t)).re ≤ -1 / 2 := by
    intro t ht
    have hU' : p t ∈ U := hpU t (by linarith [ht.1]) (by linarith [ht.2])
    have hca : ContinuousAt (fun u => (logDeriv h (p u)).re) t :=
      ((hcont (p t) hU').continuousAt (hUopen.mem_nhds hU')).comp (f := p) hpcont.continuousAt
    have hfinpre : {u : ℝ | p u ∈ ton}.Finite := by
      refine (ton.finite_toSet.preimage ?_)
      intro u _ v _ huv
      have := congrArg Complex.im huv
      rwa [hpim, hpim] at this
    have hev : ∀ᶠ u in 𝓝[≠] t, (logDeriv h (p u)).re ≤ -1 / 2 := by
      have hc : ({u : ℝ | p u ∈ ton} \ {t})ᶜ ∈ 𝓝 t :=
        ((hfinpre.subset Set.sdiff_subset).isClosed).compl_mem_nhds (fun h => h.2 rfl)
      have hball : Ioo (t - 1 / 2) (t + 1 / 2) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [nhdsWithin_le_nhds hc, nhdsWithin_le_nhds hball, self_mem_nhdsWithin]
        with u hu hub hne
      refine hgood u (by linarith [hub.1, ht.1]) (by linarith [hub.1, ht.1])
        (by linarith [hub.2, ht.2]) fun hmem => hu ⟨hmem, hne⟩
    exact le_of_tendsto (hca.tendsto.mono_left nhdsWithin_le_nhds) hev
  -- compactness: the sign persists on a thickening of the segment
  set S : Set ℂ := p '' Icc T₁ T₂ with hS
  have hScpt : IsCompact S := isCompact_Icc.image hpcont
  set O : Set ℂ := U ∩ (fun z => (logDeriv h z).re) ⁻¹' Iio 0 with hO
  have hOopen : IsOpen O := hcont.isOpen_inter_preimage hUopen isOpen_Iio
  have hSO : S ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hpU t (by linarith [ht.1]) (by linarith [ht.2]),
      show (logDeriv h (p t)).re < 0 by linarith [hseg t ht]⟩
  obtain ⟨ε, hε, hsub⟩ := hScpt.exists_cthickening_subset_open hOopen hSO
  refine ⟨min ε (η / 2), lt_min hε (by linarith), fun δ hδ hδ₀ t ht => ?_⟩
  set z : ℂ := ((1 / 2 - δ : ℝ) : ℂ) + t * I with hzdef
  have hzre : z.re = 1 / 2 - δ := by simp [hzdef]
  have hzim : z.im = t := by simp [hzdef]
  have hzO : z ∈ O := by
    apply hsub
    refine Metric.mem_cthickening_of_dist_le z (p t) ε S ⟨t, ht, rfl⟩ ?_
    have : z - p t = ((-δ : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hzdef, hp]
      · simp [hzdef, hp]
    rw [dist_eq_norm, this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hδ]
    linarith [min_le_left ε (η / 2)]
  have hzt : z ∉ ton := fun hmem => by
    have := hon z hmem; rw [hzre] at this; linarith
  have hζz : riemannZeta z ≠ 0 := fun h0 => hzt (hzeroU z hzO.1 h0)
  refine ⟨hζz, ?_⟩
  rw [hdecomp z hzO.1 hzt, Complex.add_re, Complex.re_sum]
  have hpole : ∑ w ∈ ton, ((m w : ℂ) / (z - w)).re ≤ 0 :=
    Finset.sum_nonpos fun w hw => re_natCast_div_le_zero (by
      rw [Complex.sub_re, hzre, hon w hw]; linarith)
  have hh' : (logDeriv h z).re < 0 := hzO.2
  linarith

/-- `(s − 1)²ζ'(s)`, as an entire function. -/
def zetaDerivResidueUnit (s : ℂ) : ℂ := (s - 1) * deriv zetaResidueUnit s - zetaResidueUnit s

/-- `(s − 1)²ζ(s)`, as an entire function. -/
def zetaResidueUnitSq (s : ℂ) : ℂ := (s - 1) * zetaResidueUnit s

theorem analyticOnNhd_zetaDerivResidueUnit : AnalyticOnNhd ℂ zetaDerivResidueUnit Set.univ := by
  have hG := RHTower.Sieve.zetaResidueUnit_analyticOnNhd_univ
  have hG' := hG.deriv
  intro z _
  exact ((analyticAt_id.sub analyticAt_const).mul (hG' z trivial)).sub (hG z trivial)

theorem analyticOnNhd_zetaResidueUnitSq : AnalyticOnNhd ℂ zetaResidueUnitSq Set.univ := by
  have hG := RHTower.Sieve.zetaResidueUnit_analyticOnNhd_univ
  intro z _
  exact (analyticAt_id.sub analyticAt_const).mul (hG z trivial)

theorem zetaDerivResidueUnit_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    zetaDerivResidueUnit =ᶠ[𝓝 s] fun z => (z - 1) ^ 2 * deriv riemannZeta z := by
  have hV : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hEq : Set.EqOn zetaResidueUnit (fun z => (z - 1) * riemannZeta z) ({1}ᶜ : Set ℂ) :=
    fun z hz => (zetaResidueUnit_eventuallyEq hz).eq_of_nhds
  have hD := hEq.deriv hV
  filter_upwards [hV.mem_nhds hs] with z hz
  have hz1 : z ≠ 1 := hz
  have hd : deriv (fun w => (w - 1) * riemannZeta w) z =
      riemannZeta z + (z - 1) * deriv riemannZeta z := by
    rw [deriv_fun_mul (by fun_prop) (differentiableAt_riemannZeta hz1), deriv_sub_const,
      deriv_id'', one_mul]
  simp only [zetaDerivResidueUnit]
  rw [hD hz, hd, hEq hz]
  ring

theorem zetaResidueUnitSq_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnitSq =ᶠ[𝓝 s] fun z => (z - 1) ^ 2 * riemannZeta z := by
  filter_upwards [zetaResidueUnit_eventuallyEq hs] with z hz
  simp only [zetaResidueUnitSq, hz]
  ring

/-- Away from `1` the orders of `(s − 1)²ζ'` and `ζ'` agree. -/
theorem analyticOrderAt_zetaDerivResidueUnit {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt zetaDerivResidueUnit s = analyticOrderAt (deriv riemannZeta) s := by
  rw [analyticOrderAt_congr (zetaDerivResidueUnit_eventuallyEq hs)]
  change analyticOrderAt ((fun z : ℂ => (z - 1) ^ 2) * deriv riemannZeta) s = _
  rw [analyticOrderAt_mul (by fun_prop)
    (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hs).deriv,
    (analyticOrderAt_eq_zero (f := fun z : ℂ => (z - 1) ^ 2) (z₀ := s)).mpr
      (Or.inr (pow_ne_zero 2 (sub_ne_zero.mpr hs))), zero_add]

/-- Away from `1` the orders of `(s − 1)²ζ` and `ζ` agree. -/
theorem analyticOrderAt_zetaResidueUnitSq {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt zetaResidueUnitSq s = analyticOrderAt riemannZeta s := by
  rw [analyticOrderAt_congr (zetaResidueUnitSq_eventuallyEq hs)]
  change analyticOrderAt ((fun z : ℂ => (z - 1) ^ 2) * riemannZeta) s = _
  rw [analyticOrderAt_mul (by fun_prop) (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hs),
    (analyticOrderAt_eq_zero (f := fun z : ℂ => (z - 1) ^ 2) (z₀ := s)).mpr
      (Or.inr (pow_ne_zero 2 (sub_ne_zero.mpr hs))), zero_add]

/-- **The boundary condition for the pair `(s − 1)²ζ'`, `(s − 1)²ζ`.** Wherever `ζ ≠ 0` and
`Re ζ'/ζ < 0` (away from `1`), the ratio `ζ'/ζ` satisfies the winding hypothesis. -/
theorem ratioLeftBoundary_zeta {z : ℂ} (hz1 : z ≠ 1) (hζ : riemannZeta z ≠ 0)
    (hre : (logDeriv riemannZeta z).re < 0) :
    RatioLeftBoundary zetaDerivResidueUnit zetaResidueUnitSq (logDeriv riemannZeta) z := by
  have hA := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hz1
  have hL0 : logDeriv riemannZeta z ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hre; exact lt_irrefl 0 hre
  have hd : deriv riemannZeta z ≠ 0 := fun h => hL0 (by rw [logDeriv_apply, h, zero_div])
  have hsq : (z - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz1)
  have hlogfun : logDeriv riemannZeta = fun w => deriv riemannZeta w / riemannZeta w :=
    funext fun w => logDeriv_apply _ _
  refine ⟨?_, ?_, ?_, hre, ?_⟩
  · rw [(zetaDerivResidueUnit_eventuallyEq hz1).eq_of_nhds]; exact mul_ne_zero hsq hd
  · rw [(zetaResidueUnitSq_eventuallyEq hz1).eq_of_nhds]; exact mul_ne_zero hsq hζ
  · rw [hlogfun]; exact hA.deriv.div hA hζ
  · rw [logDeriv_eq_of_germ_eq (zetaDerivResidueUnit_eventuallyEq hz1),
      logDeriv_eq_of_germ_eq (zetaResidueUnitSq_eventuallyEq hz1),
      logDeriv_mul z hsq hd (by fun_prop) hA.deriv.differentiableAt,
      logDeriv_mul z hsq hζ (by fun_prop) hA.differentiableAt, hlogfun,
      logDeriv_div z hd hζ hA.deriv.differentiableAt hA.differentiableAt,
      logDeriv_apply riemannZeta z, div_eq_mul_inv]
    ring

/-- A height lies in no Speiser shadow. -/
def SpeiserUnshadowed (T : ℝ) : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → (ρ.re - 1 / 2) ^ 2 ≤ (T - ρ.im) ^ 2

/-- At an unshadowed height `T ≥ 100`, every point of `0 < Re s < 1/2` at height `T` has `ζ ≠ 0`
and `Re ζ'/ζ < 0`. -/
theorem re_logDeriv_riemannZeta_neg_of_unshadowed {T x : ℝ} (hT : 100 ≤ T)
    (hu : SpeiserUnshadowed T) (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    riemannZeta ((x : ℂ) + T * I) ≠ 0 ∧ (logDeriv riemannZeta ((x : ℂ) + T * I)).re < 0 := by
  have hre : ((x : ℂ) + T * I).re = x := by simp
  have him : ((x : ℂ) + T * I).im = T := by simp
  obtain ⟨hζ, hle⟩ := re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
    (s := (x : ℂ) + T * I) (by rw [hre]; exact hx0) (by rw [hre]; exact hx1) (by rw [him]; exact hT)
    (fun ρ hρ _ _ => by
      rw [hre, him]
      have h1 := hu ρ hρ
      have h2 : 0 < (x - 1 / 2) ^ 2 := by
        have : x - 1 / 2 ≠ 0 := by linarith
        positivity
      linarith)
  refine ⟨hζ, ?_⟩
  rw [him] at hle
  have := one_fifth_lt_log_div_two_pi hT
  linarith

theorem zetaDerivResidueUnit_one : zetaDerivResidueUnit 1 = -1 := by
  simp [zetaDerivResidueUnit]

theorem zetaResidueUnitSq_two_ne_zero : zetaResidueUnitSq 2 ≠ 0 := by
  rw [(zetaResidueUnitSq_eventuallyEq (by norm_num : (2 : ℂ) ≠ 1)).eq_of_nhds]
  refine mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

/-- The window `0 < Re s < 1/2`, `T₁ < Im s < T₂`. -/
def speiserWindow (T₁ T₂ : ℝ) (w : ℂ) : Prop :=
  0 < w.re ∧ w.re < 1 / 2 ∧ T₁ < w.im ∧ w.im < T₂

/-- **Exact Speiser count.** For unshadowed heights `101 ≤ T₁ < T₂`, `ζ'` and `ζ` have the same
number of zeros, with multiplicity, in `0 < Re s < 1/2`, `T₁ < Im s < T₂`. -/
theorem exists_speiser_count_eq {T₁ T₂ : ℝ} (h101 : 101 ≤ T₁) (hT : T₁ < T₂)
    (hu₁ : SpeiserUnshadowed T₁) (hu₂ : SpeiserUnshadowed T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ w : ℂ, w ∈ Z₁ ↔ speiserWindow T₁ T₂ w ∧ deriv riemannZeta w = 0) ∧
      (∀ w : ℂ, w ∈ Z₀ ↔ speiserWindow T₁ T₂ w ∧ riemannZeta w = 0) ∧
      ∑ w ∈ Z₁, (analyticOrderAt (deriv riemannZeta) w).toNat =
        ∑ w ∈ Z₀, (analyticOrderAt riemannZeta w).toNat := by
  classical
  have hLpos : 0 < Real.log (T₂ + 1) := Real.log_pos (by linarith)
  set c : ℝ := 1 / (60 * Real.log (T₂ + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hL1 : 1 < Real.log (T₂ + 1) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hc14 : c < 1 / 4 := by
    rw [hc, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hcthr : ∀ t : ℝ, 100 ≤ t → t ≤ T₂ + 1 / 2 → c < 1 / 58 / Real.log (t + 1 / 2) := by
    intro t ht1 ht2
    have hl : Real.log (t + 1 / 2) ≤ Real.log (T₂ + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlp : 0 < Real.log (t + 1 / 2) := Real.log_pos (by linarith)
    rw [hc, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hne1 : ∀ x t : ℝ, 100 ≤ t → (x : ℂ) + t * I ≠ 1 := fun x t ht h => by
    have := congrArg Complex.im h; simp at this; linarith
  -- the right edge
  obtain ⟨δ₀, hδ₀, hright⟩ := exists_right_edge_re_logDeriv_neg h101 hT.le
  -- the zeros of both entire functions in the box `[c, 1/2] × [T₁, T₂]`
  have hn₁ : ∃ z : ℂ, zetaDerivResidueUnit z ≠ 0 := ⟨1, by rw [zetaDerivResidueUnit_one]; norm_num⟩
  have hn₀ : ∃ z : ℂ, zetaResidueUnitSq z ≠ 0 := ⟨2, zetaResidueUnitSq_two_ne_zero⟩
  set b₁ : ℂ := (c : ℂ) + T₁ * I with hb₁
  set b₂ : ℂ := ((1 / 2 : ℝ) : ℂ) + T₂ * I with hb₂
  have hb : b₁.re = c ∧ b₂.re = 1 / 2 ∧ b₁.im = T₁ ∧ b₂.im = T₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hb₁, hb₂]
  have hfin₁ := entire_zeros_closedRectangle_finite analyticOnNhd_zetaDerivResidueUnit hn₁ b₁ b₂
  have hfin₀ := entire_zeros_closedRectangle_finite analyticOnNhd_zetaResidueUnitSq hn₀ b₁ b₂
  set W : Finset ℂ := (hfin₁.toFinset ∪ hfin₀.toFinset).filter (fun w => w.re < 1 / 2) with hW
  obtain ⟨η₂, hη₂, hη₂le⟩ := exists_pos_le_of_finset W (fun w => 1 / 2 - w.re)
    (fun w hw => by have := (Finset.mem_filter.mp hw).2; show 0 < 1 / 2 - w.re; linarith)
  have hinW : ∀ w : ℂ, c ≤ w.re → w.re < 1 / 2 → T₁ ≤ w.im → w.im ≤ T₂ →
      (zetaDerivResidueUnit w = 0 ∨ zetaResidueUnitSq w = 0) → w ∈ W := by
    intro w h1 h2 h3 h4 hz
    have hbox : w ∈ (uIcc b₁.re b₂.re ×ℂ uIcc b₁.im b₂.im) := by
      rw [Complex.mem_reProdIm, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, uIcc_of_le (by linarith),
        uIcc_of_le hT.le]
      exact ⟨⟨h1, h2.le⟩, ⟨h3, h4⟩⟩
    refine Finset.mem_filter.mpr ⟨?_, h2⟩
    rcases hz with hz | hz
    · exact Finset.mem_union_left _ (hfin₁.mem_toFinset.mpr ⟨hbox, hz⟩)
    · exact Finset.mem_union_right _ (hfin₀.mem_toFinset.mpr ⟨hbox, hz⟩)
  set δ : ℝ := min (min δ₀ η₂) (1 / 8) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδδ₀ : δ < δ₀ := by
    have := min_le_left (min δ₀ η₂) (1 / 8); have := min_le_left δ₀ η₂; linarith
  have hδη : δ < η₂ := by
    have := min_le_left (min δ₀ η₂) (1 / 8); have := min_le_right δ₀ η₂; linarith
  have hδ8 : δ ≤ 1 / 16 := by have := min_le_right (min δ₀ η₂) (1 / 8); linarith
  set d : ℝ := 1 / 2 - δ with hd
  have hcd : c < d := by linarith
  -- the winding lemma
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, hsum⟩ := sum_analyticOrderAt_eq_of_logDeriv_ratio_re_neg
    analyticOnNhd_zetaDerivResidueUnit analyticOnNhd_zetaResidueUnitSq hn₁ hn₀ hcd hT
    (fun x hx => by
      rw [uIcc_of_le hcd.le] at hx
      obtain ⟨h1, h2⟩ := re_logDeriv_riemannZeta_neg_of_unshadowed (x := x) (by linarith) hu₁
        (by linarith [hx.1]) (by linarith [hx.2])
      exact ratioLeftBoundary_zeta (hne1 _ _ (by linarith)) h1 h2)
    (fun x hx => by
      rw [uIcc_of_le hcd.le] at hx
      obtain ⟨h1, h2⟩ := re_logDeriv_riemannZeta_neg_of_unshadowed (x := x) (by linarith) hu₂
        (by linarith [hx.1]) (by linarith [hx.2])
      exact ratioLeftBoundary_zeta (hne1 _ _ (by linarith)) h1 h2)
    (fun t ht => by
      rw [uIcc_of_le hT.le] at ht
      obtain ⟨h1, h2⟩ := hright δ hδ0 hδδ₀ t ht
      exact ratioLeftBoundary_zeta (hne1 _ _ (by linarith [ht.1])) h1 h2)
    (fun t ht => by
      rw [uIcc_of_le hT.le] at ht
      have hre : ((c : ℂ) + t * I).re = c := by simp
      have him : ((c : ℂ) + t * I).im = t := by simp
      obtain ⟨h1, h2⟩ := re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
        (s := (c : ℂ) + t * I) (by rw [hre]; exact hc0) (by rw [hre]; linarith)
        (by rw [him]; linarith [ht.1])
        (speiserDisk_strict_of_re_lt (by rw [hre]; exact hc0)
          (by rw [hre, him]; exact hcthr t (by linarith [ht.1]) (by linarith [ht.2]))
          (by rw [him]; linarith [ht.1]))
      rw [him] at h2
      have := one_fifth_lt_log_div_two_pi (show 100 ≤ t by linarith [ht.1])
      exact ratioLeftBoundary_zeta (hne1 _ _ (by linarith [ht.1])) h1 (by linarith))
  -- a point of the closed rectangle is not on the boundary if a boundary function vanishes there
  have hsplit : ∀ w : ℂ, w = (w.re : ℂ) + w.im * I := fun w => (Complex.re_add_im w).symm
  have hbotF : ∀ x : ℝ, c ≤ x → x ≤ d →
      zetaDerivResidueUnit ((x : ℂ) + T₁ * I) ≠ 0 ∧ zetaResidueUnitSq ((x : ℂ) + T₁ * I) ≠ 0 :=
    fun x h1 h2 => by
      obtain ⟨a, b⟩ := re_logDeriv_riemannZeta_neg_of_unshadowed (x := x) (by linarith) hu₁
        (by linarith) (by linarith)
      exact ⟨(ratioLeftBoundary_zeta (hne1 _ _ (by linarith)) a b).1,
        (ratioLeftBoundary_zeta (hne1 _ _ (by linarith)) a b).2.1⟩
  have htopF : ∀ x : ℝ, c ≤ x → x ≤ d →
      zetaDerivResidueUnit ((x : ℂ) + T₂ * I) ≠ 0 ∧ zetaResidueUnitSq ((x : ℂ) + T₂ * I) ≠ 0 :=
    fun x h1 h2 => by
      obtain ⟨a, b⟩ := re_logDeriv_riemannZeta_neg_of_unshadowed (x := x) (by linarith) hu₂
        (by linarith) (by linarith)
      exact ⟨(ratioLeftBoundary_zeta (hne1 _ _ (by linarith)) a b).1,
        (ratioLeftBoundary_zeta (hne1 _ _ (by linarith)) a b).2.1⟩
  have hwin : ∀ w : ℂ, w ∈ (uIcc c d ×ℂ uIcc T₁ T₂) →
      (zetaDerivResidueUnit w = 0 ∨ zetaResidueUnitSq w = 0) → speiserWindow T₁ T₂ w := by
    intro w hmem hz
    rw [Complex.mem_reProdIm, uIcc_of_le hcd.le, uIcc_of_le hT.le] at hmem
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hmem
    have hne_lo : w.im ≠ T₁ := fun h => by
      have := hbotF w.re h1 h2
      rw [← h, ← hsplit w] at this
      rcases hz with hz | hz
      · exact this.1 hz
      · exact this.2 hz
    have hne_hi : w.im ≠ T₂ := fun h => by
      have := htopF w.re h1 h2
      rw [← h, ← hsplit w] at this
      rcases hz with hz | hz
      · exact this.1 hz
      · exact this.2 hz
    exact ⟨by linarith, by linarith, lt_of_le_of_ne h3 (Ne.symm hne_lo),
      lt_of_le_of_ne h4 hne_hi⟩
  have hw1 : ∀ w : ℂ, speiserWindow T₁ T₂ w → w ≠ 1 := fun w hw h => by
    have := hw.2.2.1; rw [h, Complex.one_im] at this; linarith
  refine ⟨Z₁, Z₀, fun w => ?_, fun w => ?_, ?_⟩
  · rw [hZ₁ w]
    constructor
    · rintro ⟨hmem, hF⟩
      have hW' := hwin w hmem (Or.inl hF)
      refine ⟨hW', ?_⟩
      rw [(zetaDerivResidueUnit_eventuallyEq (hw1 w hW')).eq_of_nhds] at hF
      exact (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr (hw1 w hW')))
    · rintro ⟨hW', hz⟩
      have hF : zetaDerivResidueUnit w = 0 := by
        rw [(zetaDerivResidueUnit_eventuallyEq (hw1 w hW')).eq_of_nhds, hz, mul_zero]
      have hcw : c ≤ w.re := by
        by_contra hlt
        push Not at hlt
        exact deriv_riemannZeta_ne_zero_of_re_lt hW'.1
          (lt_trans hlt (hcthr w.im (by linarith [hW'.2.2.1]) (by linarith [hW'.2.2.2])))
          (by linarith [hW'.2.2.1]) hz
      have hwW := hη₂le w (hinW w hcw hW'.2.1 hW'.2.2.1.le hW'.2.2.2.le (Or.inl hF))
      refine ⟨?_, hF⟩
      rw [Complex.mem_reProdIm, uIcc_of_le hcd.le, uIcc_of_le hT.le]
      refine ⟨⟨hcw, ?_⟩, ⟨hW'.2.2.1.le, hW'.2.2.2.le⟩⟩
      linarith
  · rw [hZ₀ w]
    constructor
    · rintro ⟨hmem, hF⟩
      have hW' := hwin w hmem (Or.inr hF)
      refine ⟨hW', ?_⟩
      rw [(zetaResidueUnitSq_eventuallyEq (hw1 w hW')).eq_of_nhds] at hF
      exact (mul_eq_zero.mp hF).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr (hw1 w hW')))
    · rintro ⟨hW', hz⟩
      have hF : zetaResidueUnitSq w = 0 := by
        rw [(zetaResidueUnitSq_eventuallyEq (hw1 w hW')).eq_of_nhds, hz, mul_zero]
      have hcw : c ≤ w.re := by
        have hlow := one_div_le_re_of_zeta_zero hW'.1 (by linarith [hW'.2.1]) hz
        have hγ : |w.im| = w.im := abs_of_pos (by linarith [hW'.2.2.1])
        rw [hγ] at hlow
        have hl : Real.log w.im ≤ Real.log (T₂ + 1) :=
          Real.log_le_log (by linarith [hW'.2.2.1]) (by linarith [hW'.2.2.2])
        have hlp : 0 < Real.log w.im := Real.log_pos (by linarith [hW'.2.2.1])
        have : c ≤ 1 / 58 / Real.log w.im := by
          rw [hc, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      have hwW := hη₂le w (hinW w hcw hW'.2.1 hW'.2.2.1.le hW'.2.2.2.le (Or.inr hF))
      refine ⟨?_, hF⟩
      rw [Complex.mem_reProdIm, uIcc_of_le hcd.le, uIcc_of_le hT.le]
      refine ⟨⟨hcw, ?_⟩, ⟨hW'.2.2.1.le, hW'.2.2.2.le⟩⟩
      linarith
  · have e₁ : ∑ w ∈ Z₁, (analyticOrderAt (deriv riemannZeta) w).toNat =
        ∑ w ∈ Z₁, (analyticOrderAt zetaDerivResidueUnit w).toNat := by
      refine Finset.sum_congr rfl fun w hw => ?_
      have := (hZ₁ w).mp hw
      rw [analyticOrderAt_zetaDerivResidueUnit (hw1 w (hwin w this.1 (Or.inl this.2)))]
    have e₀ : ∑ w ∈ Z₀, (analyticOrderAt riemannZeta w).toNat =
        ∑ w ∈ Z₀, (analyticOrderAt zetaResidueUnitSq w).toNat := by
      refine Finset.sum_congr rfl fun w hw => ?_
      have := (hZ₀ w).mp hw
      rw [analyticOrderAt_zetaResidueUnitSq (hw1 w (hwin w this.1 (Or.inr this.2)))]
    rw [e₁, e₀, hsum]

end

end RHTower
