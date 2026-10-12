import GaloisForLFunctions.RHTower.XiCriticalityResonanceDensity
import GaloisForLFunctions.HTGeometry.PolyaClassLocalPhase

/-!
# The critical-density law for every lossless port

`eventually_card_critical_resonances_ge` assumed `E t ≠ 0` for every real `t`. A lossless port may
vanish on the real line: the Levinson port `Ξ + iλΞ'` vanishes exactly at the multiple zeros of `Ξ`.
That hypothesis is not needed. A real zero of `E` is a resonance of depth `0`, and the local argument
only uses the resonance-free box, which contains the real segment.

* `StrictLowerPolyaClass.phaseSpeed_window_local`: nonnegative, log-Lipschitz phase speed on `[X, Y]`
  from a zero-free box alone.
* `rigidAt_of_resonance_free_box`: local rigidity from a zero-free box alone, via the local phase
  representation `exists_phase_rep_Ioo`.
* `eventually_card_critical_resonances_ge_of_rh`: **uniform law.** Under RH there is one threshold
  `T₀` such that for every `T ≥ T₀`, *every* strict lower Pólya `E` with `Re E = Ξ` on `ℝ`, and every
  finite set `F` containing the zeros of `E` in the critical box, satisfy `T log T / 10⁷⁹ ≤ #F`.
* `eventually_card_port_resonances_ge`: the law for one port, with no nonvanishing hypothesis.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory Polynomial
open GaloisForLFunctions.HTGeometry (phaseSpeed poissonTerm poissonTerm_le_exp_mul
  poissonTerm_le_exp_mul_of_far poissonTerm_le_exp_mul_of_far_left neg_im_logDeriv_eval_eq_sum
  exists_phase_rep_Ioo gap_rigidity_of_phase_window_on)

namespace RHTower

/-- **Windowed phase rigidity from a zero-free box.** Let `E` be strict lower Pólya with no zero in
`[X − m, Y + m] × [−h, 0]`. On `[X, Y]` its phase speed is nonnegative and log-Lipschitz with
constant `2 / min h m`. -/
theorem StrictLowerPolyaClass.phaseSpeed_window_local {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    {h m X Y : ℝ} (hh : 0 < h) (hm : 0 < m) (hXY : X ≤ Y)
    (hfree : ∀ z : ℂ, X - m ≤ z.re → z.re ≤ Y + m → -h ≤ z.im → z.im ≤ 0 → E z ≠ 0) :
    (∀ t ∈ Icc X Y, 0 ≤ phaseSpeed E 0 t) ∧ ∀ s ∈ Icc X Y, ∀ t ∈ Icc X Y,
      phaseSpeed E 0 s ≤ Real.exp (2 * |s - t| / min h m) * phaseSpeed E 0 t := by
  have hEd := hE.differentiable
  have hne : ∀ u ∈ Icc X Y, E ((u : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 := by
    intro u hu
    refine hfree _ ?_ ?_ ?_ ?_ <;> simp <;> linarith [hu.1, hu.2]
  obtain ⟨p, hroots, hconv⟩ := hE
  have hU := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hD := hU.deriv (Eventually.of_forall fun m =>
    (Polynomial.differentiable (p m)).differentiableOn) isOpen_univ
  have hval : ∀ z : ℂ, Tendsto (fun m => (p m).eval z) atTop (𝓝 (E z)) := fun z =>
    hU.tendsto_at (mem_univ z)
  have hder : ∀ z : ℂ, Tendsto (fun m => (p m).derivative.eval z) atTop (𝓝 (deriv E z)) := by
    intro z
    have := hD.tendsto_at (mem_univ z)
    simp only [Function.comp_def, Polynomial.deriv] at this
    exact this
  have hω : ∀ u ∈ Icc X Y, Tendsto (fun m => -(((p m).derivative.eval ((u : ℂ) +
      ((0 : ℝ) : ℂ) * I)) / ((p m).eval ((u : ℂ) + ((0 : ℝ) : ℂ) * I))).im) atTop
        (𝓝 (phaseSpeed E 0 u)) := by
    intro u hu
    have := (hder ((u : ℂ) + ((0 : ℝ) : ℂ) * I)).div (hval ((u : ℂ) + ((0 : ℝ) : ℂ) * I))
      (hne u hu)
    exact (Complex.continuous_im.tendsto _).comp this |>.neg
  have hev : ∀ u ∈ Icc X Y, ∀ᶠ m in atTop, (p m).eval ((u : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 :=
    fun u hu => (hval _).eventually_ne (hne u hu)
  have hpos : ∀ m, ∀ r ∈ (p m).roots, ∀ u, 0 ≤ poissonTerm r.re (0 - r.im) u := by
    intro m r hr u
    have : 0 < 0 - r.im := by linarith [hroots m r hr]
    unfold poissonTerm; positivity
  set R : Set ℂ := Icc (X - m) (Y + m) ×ℂ Icc (-h) 0 with hRdef
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hRne : R.Nonempty := ⟨(X : ℂ), Complex.mem_reProdIm.mpr
    ⟨by simp only [Complex.ofReal_re, mem_Icc]; constructor <;> linarith,
      by simp only [Complex.ofReal_im, mem_Icc]; constructor <;> linarith⟩⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hRc.exists_isMinOn hRne hEd.continuous.norm.continuousOn
  have hER : ∀ z ∈ R, E z ≠ 0 := fun z hz => by
    rw [hRdef, Complex.mem_reProdIm] at hz
    exact hfree z hz.1.1 hz.1.2 hz.2.1 hz.2.2
  have hμ : 0 < ‖E z₀‖ := norm_pos_iff.mpr (hER z₀ hz₀)
  have hunif := Metric.tendstoUniformlyOn_iff.mp
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv R hRc) _ hμ
  have hroot : ∀ᶠ m in atTop, ∀ r ∈ (p m).roots, r ∉ R := by
    filter_upwards [hunif] with m hm r hr hrR
    have h0 : (p m).eval r = 0 := (Polynomial.isRoot_of_mem_roots hr).eq_zero
    have h1 := hm r hrR
    rw [h0, dist_zero_right] at h1
    exact lt_irrefl _ (h1.trans_le (isMinOn_iff.mp hmin r hrR))
  have hm1 : 0 < min h m := lt_min hh hm
  have hterm : ∀ n, (∀ r ∈ (p n).roots, r ∉ R) → ∀ r ∈ (p n).roots, ∀ s ∈ Icc X Y,
      ∀ t ∈ Icc X Y, poissonTerm r.re (0 - r.im) s ≤
        Real.exp (2 * |s - t| / min h m) * poissonTerm r.re (0 - r.im) t := by
    intro n hn r hr s hs t ht
    have hb : 0 < 0 - r.im := by linarith [hroots n r hr]
    have hmono : Real.exp (2 * |s - t| / m) ≤ Real.exp (2 * |s - t| / min h m) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hm1 (min_le_right _ _))
    have hpt := hpos n r hr t
    by_cases hdeep : h ≤ 0 - r.im
    · exact poissonTerm_le_exp_mul hm1 ((min_le_left _ _).trans hdeep) s t
    · have hrR := hn r hr
      rw [hRdef, Complex.mem_reProdIm] at hrR
      have him : r.im ∈ Icc (-h) 0 := ⟨by linarith, (hroots n r hr).le⟩
      have hre : r.re ∉ Icc (X - m) (Y + m) := fun h1 => hrR ⟨h1, him⟩
      rw [mem_Icc, not_and_or, not_le, not_le] at hre
      rcases hre with hre | hre
      · exact (poissonTerm_le_exp_mul_of_far hb hm (by linarith [hs.1])
          (by linarith [ht.1])).trans (mul_le_mul_of_nonneg_right hmono hpt)
      · exact (poissonTerm_le_exp_mul_of_far_left hb hm (by linarith [hs.2])
          (by linarith [ht.2])).trans (mul_le_mul_of_nonneg_right hmono hpt)
  refine ⟨fun t ht => ?_, fun s hs t ht => ?_⟩
  · refine ge_of_tendsto (hω t ht) ?_
    filter_upwards [hev t ht] with m hm
    rw [neg_im_logDeriv_eval_eq_sum hm]
    exact Multiset.sum_nonneg fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
      exact hpos m r hr t
  · refine le_of_tendsto_of_tendsto (hω s hs) ((hω t ht).const_mul _) ?_
    filter_upwards [hev s hs, hev t ht, hroot] with m hms hmt hmR
    rw [neg_im_logDeriv_eval_eq_sum hms, neg_im_logDeriv_eval_eq_sum hmt,
      ← Multiset.sum_map_mul_left]
    exact Multiset.sum_map_le_sum_map _ _ fun r hr => hterm m hmR r hr s hs t ht

/-- **Local rigidity from a resonance-free box, with no nonvanishing hypothesis on `ℝ`.** -/
theorem rigidAt_of_resonance_free_box {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) {h m X Y : ℝ} (hh : 0 < h) (hm : 0 < m) (hXY : X < Y)
    (hfree : ∀ z : ℂ, X - m ≤ z.re → z.re ≤ Y + m → -h ≤ z.im → z.im ≤ 0 → E z ≠ 0)
    {k : ℕ} (hk1 : X ≤ xiOrderedPositiveOrdinate k)
    (hk2 : xiOrderedPositiveOrdinate (k + 2) ≤ Y) :
    RigidAt (min h m / 2) k := by
  have hRH := riemannHypothesis_of_strictLowerPolya_realization hE hrep
  have hEd := hE.differentiable
  have hrep' : ∀ t : ℝ, Xi t = (E ((t : ℂ) + ((0 : ℝ) : ℂ) * I)).re := fun t => by
    simpa using hrep t
  have hneSeg : ∀ t ∈ Icc (X - m) (Y + m), E ((t : ℂ) + ((0 : ℝ) : ℂ) * I) ≠ 0 := by
    intro t ht
    refine hfree _ ?_ ?_ ?_ ?_ <;> simp <;> linarith [ht.1, ht.2]
  obtain ⟨A, φ, hA, hφ, hAφ⟩ := exists_phase_rep_Ioo hEd (by linarith) hneSeg
  have hin : ∀ t ∈ Icc X Y, t ∈ Ioo (X - m) (Y + m) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hXi : ∀ t ∈ Icc X Y, Xi t = A t * Real.cos (φ t) := fun t ht => by
    rw [hrep' t, hAφ t (hin t ht)]
  have hAW : ∀ t ∈ Icc X Y, 0 < A t := fun t ht => hA t (hin t ht)
  have hφW : ∀ t ∈ Icc X Y, HasDerivAt φ (-phaseSpeed E 0 t) t := fun t ht => hφ t (hin t ht)
  have hφc : ContinuousOn φ (Icc X Y) := fun x hx => (hφW x hx).continuousAt.continuousWithinAt
  have hm1 : 0 < min h m := lt_min hh hm
  set γ := xiOrderedPositiveOrdinate with hγ
  have hk01 : γ k ≤ γ (k + 1) := xiOrderedPositiveOrdinate_monotone (Nat.le_succ _)
  have hk12 : γ (k + 1) ≤ γ (k + 2) := xiOrderedPositiveOrdinate_monotone (Nat.le_succ _)
  obtain ⟨hω0, hLL⟩ := hE.phaseSpeed_window_local hh hm hXY.le hfree
  have hωpos : ∀ t ∈ Icc X Y, 0 < phaseSpeed E 0 t := by
    intro t₀ ht₀
    by_contra hle
    push Not at hle
    have h0 : phaseSpeed E 0 t₀ = 0 := le_antisymm hle (hω0 t₀ ht₀)
    have hz : ∀ s ∈ Icc X Y, phaseSpeed E 0 s = 0 := fun s hs => by
      have := hLL s hs t₀ ht₀
      rw [h0, mul_zero] at this
      exact le_antisymm this (hω0 s hs)
    have hconst : ∀ y ∈ Icc X Y, φ y = φ X := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with hXy | hXy
      · rw [hXy]
      obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope φ (fun t => -phaseSpeed E 0 t) hXy
        (hφc.mono (Icc_subset_Icc le_rfl hy.2))
        fun x hx => hφW x ⟨hx.1.le, hx.2.le.trans hy.2⟩
      have hyX : y - X ≠ 0 := by linarith
      rw [hz ξ ⟨hξ.1.le, hξ.2.le.trans hy.2⟩, eq_div_iff hyX] at hmv
      linarith
    have hkW : γ k ∈ Icc X Y := ⟨hk1, by linarith⟩
    have hcos0 : Real.cos (φ X) = 0 := by
      have := Xi_orderedPositiveOrdinate_eq_zero hRH k
      rw [hXi _ hkW, hconst _ hkW] at this
      exact (mul_eq_zero.mp this).resolve_left (hAW _ hkW).ne'
    have hY0 : 0 < Y := lt_of_lt_of_le (xiOrderedPositiveOrdinate_pos (k + 2)) hk2
    have hsub : Ioo (max X 0) Y ⊆ γ '' Iio (xiZeroCount Y).toNat := by
      intro y hy
      have hy0 : 0 < y := lt_of_le_of_lt (le_max_right _ _) hy.1
      have hyX : X < y := lt_of_le_of_lt (le_max_left _ _) hy.1
      have hyW : y ∈ Icc X Y := ⟨hyX.le, hy.2.le⟩
      have hXiy : Xi y = 0 := by rw [hXi _ hyW, hconst y hyW, hcos0, mul_zero]
      obtain ⟨n, hn⟩ := exists_orderedPositiveOrdinate_eq_of_Xi_eq_zero hy0 hXiy
      exact ⟨n, lt_toNat_xiZeroCount_iff.mpr (by rw [hn]; exact hy.2.le), hn⟩
    exact Set.Ioo_infinite (max_lt hXY hY0) (((Set.finite_Iio _).image γ).subset hsub)
  have hk0W : γ k ∈ Icc X Y := ⟨hk1, by linarith⟩
  have hk1W : γ (k + 1) ∈ Icc X Y := ⟨by linarith, by linarith⟩
  have hk2W : γ (k + 2) ∈ Icc X Y := ⟨by linarith, hk2⟩
  have hs0 := ordinate_lt_succ_of_phaseSpeed_pos hEd hrep' hRH
    (hneSeg _ ⟨by linarith [hk0W.1], by linarith [hk0W.2]⟩) (hωpos _ hk0W)
  have hs1 := ordinate_lt_succ_of_phaseSpeed_pos hEd hrep' hRH
    (hneSeg _ ⟨by linarith [hk1W.1], by linarith [hk1W.2]⟩) (hωpos _ hk1W)
  have hz : ∀ j, γ j ∈ Icc X Y → A (γ j) * Real.cos (φ (γ j)) = 0 := fun j hj => by
    rw [← hXi _ hj]; exact Xi_orderedPositiveOrdinate_eq_zero hRH j
  have hno : ∀ j, γ j ∈ Icc X Y → γ (j + 1) ∈ Icc X Y →
      ∀ x ∈ Ioo (γ j) (γ (j + 1)), A x * Real.cos (φ x) ≠ 0 := fun j hj hj' x hx => by
    rw [← hXi x ⟨by linarith [hj.1, hx.1], by linarith [hj'.2, hx.2]⟩]
    exact Xi_ne_zero_of_mem_Ioo_ordinates hx
  have hgr := gap_rigidity_of_phase_window_on hm1 hAW hφW hωpos hLL hk1 hk2 hs0 hs1
    (hz k hk0W) (hz (k + 1) hk1W) (hz (k + 2) hk2W) (hno k hk0W hk1W) (hno (k + 1) hk1W hk2W)
  have he : 2 * (γ (k + 2) - γ k) / min h m =
      (ordinateGap k + ordinateGap (k + 1)) / (min h m / 2) := by
    simp only [ordinateGap, hγ]
    field_simp
    ring
  rw [he] at hgr
  have e1 : γ (k + 2) - γ (k + 1) = ordinateGap (k + 1) := by simp only [ordinateGap, hγ]
  have e2 : γ (k + 1) - γ k = ordinateGap k := by simp only [ordinateGap, hγ]
  rw [e1, e2] at hgr
  exact ⟨hs0, hgr.1, hgr.2⟩

/-- **A non-rigid good height has a critical resonance nearby**, for every lossless port. -/
theorem exists_resonance_near_of_not_rigidAt_box {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) {T t : ℝ} {k : ℕ}
    (hL : 10 ^ 25 ≤ Real.log T)
    (hgrid : ∀ j : ℤ, |j| ≤ 9 → ∃ n, |xiOrderedPositiveOrdinate n -
      (t + 2 * j * (32 * 10 ^ 13 / Real.log T))| < 32 * 10 ^ 13 / Real.log T)
    (hk : |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / Real.log T))
    (hnr : ¬ RigidAt (10 ^ 60 / Real.log T) k) :
    ∃ z : ℂ, E z = 0 ∧ |z.re - t| ≤ 17 * (32 * 10 ^ 13 / Real.log T) + 2 * 10 ^ 60 / Real.log T ∧
      -(2 * 10 ^ 60 / Real.log T) ≤ z.im ∧ z.im ≤ 0 := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set τ₂ : ℝ := 32 * 10 ^ 13 / L with hτ₂
  have hτ₂0 : 0 < τ₂ := by positivity
  set γ := xiOrderedPositiveOrdinate with hγ
  have hg0 := ordinateGap_lt_of_gridExt hτ₂0 hgrid (m := k) (by linarith [hk])
  rw [abs_le] at hk
  have hk1 : γ (k + 1) = γ k + ordinateGap k := by simp [ordinateGap, hγ]
  have hk2 : γ (k + 2) = γ (k + 1) + ordinateGap (k + 1) := by simp [ordinateGap, hγ]
  have hgk0 := ordinateGap_nonneg k
  have hgk1 := ordinateGap_nonneg (k + 1)
  have hg1 := ordinateGap_lt_of_gridExt hτ₂0 hgrid (m := k + 1)
    (by rw [abs_le]; constructor <;> linarith)
  by_contra hcon
  apply hnr
  have hfree : ∀ z : ℂ, (γ k - τ₂) - 2 * 10 ^ 60 / L ≤ z.re →
      z.re ≤ (γ (k + 2) + τ₂) + 2 * 10 ^ 60 / L → -(2 * 10 ^ 60 / L) ≤ z.im → z.im ≤ 0 →
      E z ≠ 0 := by
    intro z h1 h2 h3 h4 hz
    refine hcon ⟨z, hz, ?_, h3, h4⟩
    rw [abs_le]; constructor <;> linarith
  have hR := rigidAt_of_resonance_free_box hE hrep (h := 2 * 10 ^ 60 / L)
    (m := 2 * 10 ^ 60 / L) (by positivity) (by positivity) (by linarith) hfree
    (by linarith : γ k - τ₂ ≤ γ k) (by linarith : γ (k + 2) ≤ γ (k + 2) + τ₂)
  rwa [min_self, show 2 * 10 ^ 60 / L / 2 = 10 ^ 60 / L by ring] at hR

/-- **Uniform critical-density law.** Under RH, for all large `T`, every lossless port of `Ξ` has
at least `T log T / 10⁷⁹` resonances in the critical box, with one threshold for all ports. -/
theorem eventually_card_critical_resonances_ge_of_rh (hRH : RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop, ∀ E : ℂ → ℂ, StrictLowerPolyaClass E → (∀ t : ℝ, Xi t = (E t).re) →
      ∀ F : Finset ℂ,
      (∀ z : ℂ, E z = 0 → 3 * T ^ (1 / 2 : ℝ) - 1 ≤ z.re → z.re ≤ T + 1 →
        -(2 * 10 ^ 60 / Real.log T) ≤ z.im → z.im ≤ 0 → z ∈ F) →
      T * Real.log T / 10 ^ 79 ≤ F.card := by
  have hzero : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := fun q =>
    riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH _ (xi_xiZeroCopy_eq_zero q)
  filter_upwards [eventually_volume_nonRigidHeights_gt hRH,
    Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 25), eventually_ge_atTop (2 : ℝ),
    eventually_narrowMass_bound, eventually_lorentzMassW_le, eventually_selbergLength_le,
    Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 61)]
    with T hN hL hT2 hV hW hlen hL61 E hE hrep F hF
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (by norm_num) hL
  have hx1 : 1 < T ^ (1 / 20 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hlx : Real.log (T ^ (1 / 20 : ℝ)) = Real.log T / 20 := by rw [Real.log_rpow hT0]; ring
  have hV' := hV fun q _ _ => hzero q
  set R := 17 * (32 * 10 ^ 13 / Real.log T) + 2 * 10 ^ 60 / Real.log T with hR
  have hRle : R ≤ 3 * 10 ^ 60 / Real.log T := by
    rw [hR]
    have : 17 * (32 * 10 ^ 13 / Real.log T) ≤ 10 ^ 60 / Real.log T := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by norm_num) hL0.le
    have e : 3 * 10 ^ 60 / Real.log T = 10 ^ 60 / Real.log T + 2 * 10 ^ 60 / Real.log T := by
      ring
    linarith
  have hR1 : R ≤ 1 / 2 := by
    refine hRle.trans ?_
    rw [div_le_iff₀ hL0]
    nlinarith
  have hcover : (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩
      nonRigidHeights (10 ^ 60 / Real.log T) (32 * 10 ^ 13 / Real.log T)) \
        criticalBadSetExt (T ^ (1 / 20 : ℝ)) (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
          ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ⊆
      ⋃ z ∈ F, Icc (z.re - R) (z.re + R) := by
    rintro t ⟨⟨htI, k, hk, hnr⟩, htB⟩
    have hgrid := exists_ordinate_near_gridExt hT1 hL hlx htI.1 htI.2 hV' hW htB
    obtain ⟨z, hz, hzre, hzim1, hzim2⟩ :=
      exists_resonance_near_of_not_rigidAt_box hE hrep hL hgrid hk hnr
    rw [abs_le] at hzre
    have hzF : z ∈ F := hF z hz (by linarith [htI.1]) (by linarith [htI.2]) hzim1 hzim2
    rw [Set.mem_iUnion₂]
    exact ⟨z, hzF, by constructor <;> linarith⟩
  have hvolS := volume_le_of_cover_finset hcover
  have hvolB := volume_criticalBadSetExt_le_critical hT1 hL hx1 hlen
  have hNle := (measure_mono (μ := volume) (Set.subset_sdiff_union
    (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩
      nonRigidHeights (10 ^ 60 / Real.log T) (32 * 10 ^ 13 / Real.log T))
    (criticalBadSetExt (T ^ (1 / 20 : ℝ)) (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
      ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2)))).trans
    (measure_union_le _ _)
  have htot := hN.trans_le (hNle.trans (add_le_add hvolS hvolB))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at htot
  exact card_ge_of_volume_bounds hT0 hL0 (by positivity) hRle
    ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp htot)

/-- **Critical resonances of one lossless port**, with no nonvanishing hypothesis on `ℝ`. -/
theorem eventually_card_port_resonances_ge {E : ℂ → ℂ} (hE : StrictLowerPolyaClass E)
    (hrep : ∀ t : ℝ, Xi t = (E t).re) :
    ∀ᶠ T : ℝ in atTop, ∀ F : Finset ℂ,
      (∀ z : ℂ, E z = 0 → 3 * T ^ (1 / 2 : ℝ) - 1 ≤ z.re → z.re ≤ T + 1 →
        -(2 * 10 ^ 60 / Real.log T) ≤ z.im → z.im ≤ 0 → z ∈ F) →
      T * Real.log T / 10 ^ 79 ≤ F.card :=
  (eventually_card_critical_resonances_ge_of_rh
    (riemannHypothesis_of_strictLowerPolya_realization hE hrep)).mono
    fun _ hT F hF => hT E hE hrep F hF

end RHTower
