import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftCriticalScaleProducer
import GaloisForLFunctions.RHTower.XiTwoPortProducerEdges

/-!
# Every shadow cluster carries an exceptional point

Call a height `T` *shadow-free* if `(Im w)² < (T − Re w)²` for every zero `w` of `Ξ`. Equivalently,
`|T − γ| > |β − ½|` for every zero `ρ = β + iγ` of `ξ`.

**Theorem** (`exists_exceptionalPoint_of_shadowFree_window`). Let `T₁ < T₂` be shadow-free and let
`Ξ` have a non-real zero `w` with `T₁ < Re w < T₂`. Then for some `0 < h < ½`, `cos(hD)Ξ` has a
multiple real zero `x` with `T₁ < x < T₂`.

**Proof.** This localises `riemannHypothesis_iff_cosProducer_no_exceptionalPoint`.
* A non-real zero of `cos(hD)Ξ` has real part inside a shadow
  (`exists_xiZero_shadow_of_cosineShift_nonreal`). So no defect ever sits on the window's sides
  (`cosProducer_nonreal_re_ne_of_shadowFree`).
* A multiple real zero needs a zero `w` with `(x − Re w)² + h² ≤ (Im w)²`. So none sits on the sides
  either.
* Hurwitz gives a defect near `w` at small depth, and defect disks bound the defective depths below
  `½`. At the last defective depth in the window, a conjugate pair of defects has collapsed onto
  the real axis: a multiple real zero.

With the shadow confinement of exceptional points (`deriv_cosineShiftXi_ne_zero_of_local`), this
gives a two-sided description. The exceptional points of the PTR producer lie in the union of the
off-line shadows, and every window between shadow-free heights that contains an off-line zero
contains one of them.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A defect of `cos(hD)Ξ` never sits at a shadow-free height. -/
theorem cosProducer_nonreal_re_ne_of_shadowFree {T h : ℝ} (hh : 0 < h)
    (hg : ∀ v, XiC v = 0 → v.im ^ 2 < (T - v.re) ^ 2) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : cosProducer h z = 0) : z.re ≠ T := by
  intro hzT
  obtain ⟨ρ, hρ, -, hdist⟩ := exists_xiZero_shadow_of_cosineShift_nonreal hh hz h0
  set v : ℂ := (ρ.im : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * I with hv
  have hXv : XiC v = 0 := by
    rw [XiC]
    have : (1 / 2 : ℂ) + v * I = ρ := by
      rw [hv]; apply Complex.ext <;> simp
    rw [this]; exact hρ
  have h1 := hg v hXv
  simp only [hv, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, zero_sub, Complex.sub_re, Complex.mul_re, sub_zero,
    mul_one] at h1
  rw [hzT] at hdist
  have h2 : (T - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
    have := sq_le_sq' (abs_le.mp hdist).1 (abs_le.mp hdist).2
    rwa [sq_abs] at this
  nlinarith

/-- A multiple real zero of `cos(hD)Ξ` never sits at a shadow-free height. -/
theorem deriv_cosProducer_ne_zero_of_shadowFree {T h : ℝ} (hh : 0 < h)
    (hg : ∀ v, XiC v = 0 → v.im ^ 2 < (T - v.re) ^ 2) (h0 : cosProducer h T = 0) :
    deriv (cosProducer h) T ≠ 0 := by
  refine deriv_cosineShiftXi_ne_zero_of_local hh (fun w hw => ?_) h0
  have := hg w hw
  nlinarith [sq_nonneg h]

/-- **Every shadow-free window containing an off-line zero carries an exceptional point.** -/
theorem exists_exceptionalPoint_of_shadowFree_window {T₁ T₂ : ℝ}
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2)
    {w : ℂ} (hw : XiC w = 0) (hwim : w.im ≠ 0) (hwre : w.re ∈ Ioo T₁ T₂) :
    ∃ h : ℝ, 0 < h ∧ h < 1 / 2 ∧ ∃ x ∈ Ioo T₁ T₂,
      cosProducer h x = 0 ∧ deriv (cosProducer h) x = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- no multiple real zero in the closed window
  have hno : ∀ h : ℝ, 0 < h → h < 1 / 2 → ∀ x : ℝ, x ∈ Icc T₁ T₂ → cosProducer h x = 0 →
      deriv (cosProducer h) x ≠ 0 := by
    intro h hh hh2 x hx h0
    rcases eq_or_lt_of_le hx.1 with hx1 | hx1
    · rw [← hx1]; exact deriv_cosProducer_ne_zero_of_shadowFree hh hg₁ (by rw [hx1]; exact h0)
    rcases eq_or_lt_of_le hx.2 with hx2 | hx2
    · rw [hx2]; exact deriv_cosProducer_ne_zero_of_shadowFree hh hg₂ (by rw [← hx2]; exact h0)
    exact hcon h hh hh2 x ⟨hx1, hx2⟩ h0
  have hT : T₁ < T₂ := hwre.1.trans hwre.2
  -- a defect near `w` at a small depth
  have hconv0 : TendstoLocallyUniformly (fun (n : ℕ) => cosProducer (1 / ((n : ℝ) + 1))) XiC
      atTop := tendstoLocallyUniformly_cosineShift_XiC
  set r : ℝ := min (|w.im| / 2) (min (w.re - T₁) (T₂ - w.re)) with hrdef
  have hr : 0 < r := lt_min (by have := abs_pos.mpr hwim; positivity)
    (lt_min (by linarith [hwre.1]) (by linarith [hwre.2]))
  obtain ⟨n, ⟨z₀, hz₀b, hz₀⟩, hn2⟩ := ((eventually_exists_zero_mem_ball
    (fun n => differentiable_cosProducer _) differentiable_XiC analyticOrderAt_XiC_ne_top hconv0 hw
    hr).and (eventually_ge_atTop 2)).exists
  set h₀ : ℝ := 1 / ((n : ℝ) + 1) with hh₀def
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hh₀ : 0 < h₀ := by positivity
  have hh₀half : h₀ < 1 / 2 := by
    rw [hh₀def, div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hz₀d := mem_ball.mp hz₀b
  have hz₀im : z₀.im ≠ 0 := by
    intro h0
    have him : |z₀.im - w.im| ≤ dist z₀ w := by
      rw [dist_eq_norm]; have := Complex.abs_im_le_norm (z₀ - w); simpa using this
    rw [h0, zero_sub, abs_neg] at him
    linarith [min_le_left (|w.im| / 2) (min (w.re - T₁) (T₂ - w.re))]
  have hz₀re : z₀.re ∈ Icc T₁ T₂ := by
    have hre : |z₀.re - w.re| ≤ dist z₀ w := by
      rw [dist_eq_norm]; have := Complex.abs_re_le_norm (z₀ - w); simpa using this
    have h1 := min_le_right (|w.im| / 2) (min (w.re - T₁) (T₂ - w.re))
    have h2 := min_le_left (w.re - T₁) (T₂ - w.re)
    have h3 := min_le_right (w.re - T₁) (T₂ - w.re)
    constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2,
      (abs_lt.mp (lt_of_le_of_lt hre hz₀d)).1, (abs_lt.mp (lt_of_le_of_lt hre hz₀d)).2]
  -- a depth bound over the window
  set R : ℝ := |T₁| + |T₂| + 2 with hRdef
  have hEfin : {w' ∈ closedBall (0 : ℂ) R | XiC w' = 0}.Finite :=
    finite_zeros_closedBall (fun z _ => differentiable_XiC.analyticAt z)
      (fun z _ h => analyticOrderAt_XiC_ne_top z (analyticOrderAt_eq_top.mpr h))
  obtain ⟨m, hmhalf, hm0, hmE⟩ := exists_depth_bound_of_finite hEfin (fun w' hw' => hw'.2)
  set htop : ℝ := max h₀ m with hhtop
  have htophalf : htop < 1 / 2 := max_lt hh₀half hmhalf
  have hnodef : ∀ h : ℝ, htop < h → ∀ z : ℂ, z.re ∈ Icc T₁ T₂ → cosProducer h z = 0 →
      z.im = 0 := by
    intro h hh z hzR h0
    by_contra hz
    have hhpos : 0 < h := lt_of_le_of_lt (le_trans hh₀.le (le_max_left _ _)) hh
    obtain ⟨w', hw', hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hhpos hz h0
    have hw'sq : w'.im ^ 2 ≤ 1 / 4 :=
      DeBruijn.riemannKernel_zeros_im_sq_le w'
        (by rw [DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hw')
    have hzsq : 0 < z.im ^ 2 := by positivity
    have hclose : |w'.re - z.re| ≤ 1 / 2 := by
      have := sq_le_sq.mp (show (w'.re - z.re) ^ 2 ≤ (1 / 2) ^ 2 by nlinarith)
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    have hw'im : |w'.im| ≤ 1 / 2 := by
      have := sq_le_sq.mp (show w'.im ^ 2 ≤ (1 / 2) ^ 2 by linarith)
      rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    have hzabs : |z.re| ≤ |T₁| + |T₂| := by
      rw [abs_le]; constructor <;> linarith [hzR.1, hzR.2, neg_abs_le T₁, le_abs_self T₂,
        abs_nonneg T₁, abs_nonneg T₂]
    have hw'E : w' ∈ {w' ∈ closedBall (0 : ℂ) R | XiC w' = 0} := by
      refine ⟨?_, hw'⟩
      rw [mem_closedBall, dist_zero_right]
      have := Complex.norm_le_abs_re_add_abs_im w'
      have := abs_sub_abs_le_abs_sub w'.re z.re
      linarith
    have h1 := hmE w' hw'E
    have hdeep : h < |w'.im| := by
      have h2 : h ^ 2 < w'.im ^ 2 := by nlinarith [sq_nonneg (w'.re - z.re)]
      have := sq_lt_sq.mp h2
      rwa [abs_of_pos hhpos] at this
    have : m ≤ htop := le_max_right _ _
    linarith
  -- the supremum of the defective depths in the window
  set SF : Set ℝ := {h : ℝ | h₀ ≤ h ∧ ∃ z : ℂ, z.re ∈ Icc T₁ T₂ ∧ z.im ≠ 0 ∧ cosProducer h z = 0}
    with hSFdef
  have hh₀SF : h₀ ∈ SF := ⟨le_rfl, z₀, hz₀re, hz₀im, hz₀⟩
  have hbdd : BddAbove SF := by
    refine ⟨htop, fun h hh => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨-, z, hzR, hz, h0⟩ := hh
    exact hz (hnodef h hlt z hzR h0)
  set hstar := sSup SF with hstardef
  have hstar_ge : h₀ ≤ hstar := le_csSup hbdd hh₀SF
  have hstar_le : hstar ≤ htop := csSup_le ⟨h₀, hh₀SF⟩ fun h hh => by
    by_contra hlt
    push Not at hlt
    obtain ⟨-, z, hzR, hz, h0⟩ := hh
    exact hz (hnodef h hlt z hzR h0)
  have hstarpos : 0 < hstar := lt_of_lt_of_le hh₀ hstar_ge
  have hstarhalf : hstar < 1 / 2 := lt_of_le_of_lt hstar_le htophalf
  obtain ⟨u, -, hu, huSF⟩ := exists_seq_tendsto_sSup ⟨h₀, hh₀SF⟩ hbdd
  choose zs hzsR hzsim hzs0 using fun k => (huSF k).2
  have hupos : ∀ k, 0 < u k := fun k => lt_of_lt_of_le hh₀ (huSF k).1
  have hzsK : ∀ k, zs k ∈ closedBall (0 : ℂ) R := by
    intro k
    rw [mem_closedBall, dist_zero_right]
    have := Complex.norm_le_abs_re_add_abs_im (zs k)
    have := abs_im_le_half_of_cosProducer_eq_zero (hupos k) (hzs0 k)
    have hzabs : |(zs k).re| ≤ |T₁| + |T₂| := by
      rw [abs_le]; constructor <;> linarith [(hzsR k).1, (hzsR k).2, neg_abs_le T₁,
        le_abs_self T₂, abs_nonneg T₁, abs_nonneg T₂]
    linarith
  obtain ⟨zstar, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq hzsK
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 hstar) := hu.comp hφ.tendsto_atTop
  have hzstar0 : cosProducer hstar zstar = 0 := by
    have hpair : Tendsto (fun k => (u (φ k), zs (φ k))) atTop (𝓝 (hstar, zstar)) :=
      huφ.prodMk_nhds hlim
    have h1 := (continuous_cosProducer_uncurry.tendsto (hstar, zstar)).comp hpair
    have h2 : (fun k => cosProducer (u (φ k)) (zs (φ k))) = fun _ => (0 : ℂ) := by
      funext k; exact hzs0 (φ k)
    have h3 : Tendsto (fun k => cosProducer (u (φ k)) (zs (φ k))) atTop
        (𝓝 (cosProducer hstar zstar)) := h1
    rw [h2] at h3
    exact (tendsto_nhds_unique h3 tendsto_const_nhds)
  have hzstarR : zstar.re ∈ Icc T₁ T₂ := by
    have hc : Tendsto (fun k => (zs (φ k)).re) atTop (𝓝 zstar.re) :=
      (Complex.continuous_re.tendsto zstar).comp hlim
    exact isClosed_Icc.mem_of_tendsto hc (Eventually.of_forall fun k => hzsR (φ k))
  by_cases hzim : zstar.im = 0
  · -- the limit is real: a collision
    obtain ⟨x, hx⟩ : ∃ x : ℝ, zstar = (x : ℂ) :=
      ⟨zstar.re, Complex.ext (by simp) (by simp [hzim])⟩
    subst hx
    have hxR : x ∈ Icc T₁ T₂ := by simpa using hzstarR
    have hd := hno hstar hstarpos hstarhalf x hxR hzstar0
    have hm1 := zeroMult_eq_one_of_deriv_ne_zero (differentiable_cosProducer hstar) hzstar0 hd
    obtain ⟨r₀, hr₀, hiso⟩ := exists_radius_zeroSumBall_eq_zeroMult
      (differentiable_cosProducer hstar) (analyticOrderAt_cosProducer_ne_top hstar) (x : ℂ)
    obtain ⟨hsph, hcount⟩ := hiso r₀ hr₀ le_rfl
    rw [hm1] at hcount
    have hconv := tendstoLocallyUniformly_cosProducer hstar
    have hevc := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      (fun h => differentiable_cosProducer h) (differentiable_cosProducer hstar) hconv hr₀
      (by linarith : r₀ < 2 * r₀) hsph
    have hevs := LeeYangCount.eventually_ne_zero_on_sphere
      (differentiable_cosProducer hstar).continuous hconv hsph
    have hball : ∀ᶠ k in atTop, zs (φ k) ∈ ball (x : ℂ) r₀ :=
      hlim.eventually (Metric.ball_mem_nhds (x : ℂ) hr₀)
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := ((huφ.eventually (hevc.and hevs)).and hball).exists
    set h := u (φ k)
    set z := zs (φ k)
    have hzc0 : cosProducer h ((starRingEnd ℂ) z) = 0 := by
      rw [cosProducer_conj, hzs0 (φ k), map_zero]
    have hzcb : (starRingEnd ℂ) z ∈ ball (x : ℂ) r₀ := by
      rw [mem_ball] at hk3 ⊢
      rw [dist_eq_norm] at hk3 ⊢
      have e : (starRingEnd ℂ) z - x = (starRingEnd ℂ) (z - x) := by
        rw [map_sub, Complex.conj_ofReal]
      rw [e, Complex.norm_conj]; exact hk3
    have hne : z ≠ (starRingEnd ℂ) z := by
      intro he
      have := congrArg Complex.im he
      rw [Complex.conj_im] at this
      exact hzsim (φ k) (by linarith)
    obtain ⟨Z, hZball, hZzero, hsum⟩ := exists_zeroSet_zeroSumBall hr₀ (by linarith : r₀ < 2 * r₀)
      isOpen_univ (subset_univ _) (differentiable_cosProducer h).differentiableOn hk2
    have hzZ : z ∈ Z := (hZzero z hk3).mp (hzs0 (φ k))
    have hzcZ : (starRingEnd ℂ) z ∈ Z := (hZzero _ hzcb).mp hzc0
    have hpairsub : ({z, (starRingEnd ℂ) z} : Finset ℂ) ⊆ Z := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hzZ
      · rw [Finset.mem_singleton.mp hy]; exact hzcZ
    have hge : 2 ≤ ∑ ρ ∈ Z, zeroMult (cosProducer h) ρ := by
      calc 2 = ∑ ρ ∈ ({z, (starRingEnd ℂ) z} : Finset ℂ), 1 := by
            rw [Finset.sum_const, Finset.card_pair hne]; rfl
        _ ≤ ∑ ρ ∈ ({z, (starRingEnd ℂ) z} : Finset ℂ), zeroMult (cosProducer h) ρ := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            refine one_le_zeroMult_of_eq_zero (differentiable_cosProducer h)
              (analyticOrderAt_cosProducer_ne_top h) ?_
            rcases Finset.mem_insert.mp hρ with rfl | hρ
            · exact hzs0 (φ k)
            · rw [Finset.mem_singleton.mp hρ]; exact hzc0
        _ ≤ ∑ ρ ∈ Z, zeroMult (cosProducer h) ρ :=
            Finset.sum_le_sum_of_subset_of_nonneg hpairsub fun _ _ _ => Nat.zero_le _
    have hk1' : zeroSumBall (cosProducer h) (x : ℂ) r₀ = ((1 : ℕ) : ℂ) := hk1.trans hcount
    rw [hk1'] at hsum
    have : ∑ ρ ∈ Z, zeroMult (cosProducer h) ρ = 1 := by exact_mod_cast hsum.symm
    omega
  · -- the limit is non-real: the defect persists past `hstar` inside the window
    have hside₁ := cosProducer_nonreal_re_ne_of_shadowFree hstarpos hg₁ hzim hzstar0
    have hside₂ := cosProducer_nonreal_re_ne_of_shadowFree hstarpos hg₂ hzim hzstar0
    have hin₁ : T₁ < zstar.re := lt_of_le_of_ne hzstarR.1 (Ne.symm hside₁)
    have hin₂ : zstar.re < T₂ := lt_of_le_of_ne hzstarR.2 hside₂
    set ρr : ℝ := min (|zstar.im|) (min (zstar.re - T₁) (T₂ - zstar.re)) with hρr
    have hρr0 : 0 < ρr := lt_min (abs_pos.mpr hzim) (lt_min (by linarith) (by linarith))
    have hev := eventually_exists_zero_mem_ball (fun h => differentiable_cosProducer h)
      (differentiable_cosProducer hstar) (analyticOrderAt_cosProducer_ne_top hstar)
      (tendstoLocallyUniformly_cosProducer hstar) hzstar0 hρr0
    obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨z, hzb, hz0⟩ := hδev (y := hstar + δ / 2)
      (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    have hd : dist z zstar < ρr := mem_ball.mp hzb
    have hzim' : z.im ≠ 0 := by
      intro h0
      have : |z.im - zstar.im| ≤ dist z zstar := by
        rw [dist_eq_norm]; have := Complex.abs_im_le_norm (z - zstar); simpa using this
      rw [h0, zero_sub, abs_neg] at this
      linarith [min_le_left (|zstar.im|) (min (zstar.re - T₁) (T₂ - zstar.re))]
    have hzre' : z.re ∈ Icc T₁ T₂ := by
      have hre : |z.re - zstar.re| ≤ dist z zstar := by
        rw [dist_eq_norm]; have := Complex.abs_re_le_norm (z - zstar); simpa using this
      have h1 := min_le_right (|zstar.im|) (min (zstar.re - T₁) (T₂ - zstar.re))
      have h2 := min_le_left (zstar.re - T₁) (T₂ - zstar.re)
      have h3 := min_le_right (zstar.re - T₁) (T₂ - zstar.re)
      constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
    have hmem : hstar + δ / 2 ∈ SF := ⟨by linarith, z, hzre', hzim', hz0⟩
    have := le_csSup hbdd hmem
    linarith

end

end RHTower
