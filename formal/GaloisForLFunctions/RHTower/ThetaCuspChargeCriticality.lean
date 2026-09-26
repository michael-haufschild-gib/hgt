import GaloisForLFunctions.RHTower.ThetaCuspChargeReality
import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem thetaGroupXi_one_neg (w : ℂ) : thetaGroupXi 1 (-w) = thetaGroupXi 1 w := by
  unfold thetaGroupXi
  exact modXi_neg (differentiableOn_thetaGroupBasis 1) (thetaGroupBasis_axis 1) w

theorem XiC_ofReal_im_eq_zero (x : ℝ) : (XiC (x : ℂ)).im = 0 := by
  rw [XiC_ofReal]; simp

/-- A real minimizer of `Ξ/Ξ₁` with nonpositive value, inside the dominance range. -/
theorem exists_interior_min_ratio {U : ℝ}
    (hneg : ∀ u : ℝ, U ≤ u → (thetaGroupXi 1 (u : ℂ)).re < 0) :
    ∃ p q u : ℝ, U ≤ p ∧ p < u ∧ u < q ∧
      (XiC (u : ℂ)).re / (thetaGroupXi 1 (u : ℂ)).re ≤ 0 ∧
      ∀ x ∈ Icc p q, (XiC (u : ℂ)).re / (thetaGroupXi 1 (u : ℂ)).re ≤
        (XiC (x : ℂ)).re / (thetaGroupXi 1 (x : ℂ)).re := by
  set r : ℝ → ℝ := fun x => (XiC (x : ℂ)).re / (thetaGroupXi 1 (x : ℂ)).re with hr
  have hcont : ∀ a b : ℝ, U ≤ a → ContinuousOn r (Icc a b) := by
    intro a b ha
    have h1 : Continuous fun x : ℝ => (XiC (x : ℂ)).re :=
      Complex.continuous_re.comp (XiC_differentiable.continuous.comp Complex.continuous_ofReal)
    have h2 : Continuous fun x : ℝ => (thetaGroupXi 1 (x : ℂ)).re :=
      Complex.continuous_re.comp
        ((differentiable_thetaGroupXi 1).continuous.comp Complex.continuous_ofReal)
    exact (h1.continuousOn).div h2.continuousOn fun x hx => (hneg x (le_trans ha hx.1)).ne
  have hzero : ∀ z : ℝ, Xi z = 0 → r z = 0 := by
    intro z hz; simp only [hr]; rw [XiC_ofReal, hz]; simp
  obtain ⟨z₁, hz₁, hX₁⟩ := exists_Xi_zero_gt U
  obtain ⟨z₂, hz₂, hX₂⟩ := exists_Xi_zero_gt z₁
  obtain ⟨z₃, hz₃, hX₃⟩ := exists_Xi_zero_gt z₂
  have hr₁ := hzero z₁ hX₁
  have hr₂ := hzero z₂ hX₂
  have hr₃ := hzero z₃ hX₃
  obtain ⟨a, ha, hamin⟩ := (isCompact_Icc (a := z₁) (b := z₂)).exists_isMinOn
    (nonempty_Icc.mpr hz₂.le) (hcont z₁ z₂ hz₁.le)
  obtain ⟨b, hb, hbmin⟩ := (isCompact_Icc (a := z₂) (b := z₃)).exists_isMinOn
    (nonempty_Icc.mpr hz₃.le) (hcont z₂ z₃ (le_trans hz₁.le hz₂.le))
  by_cases hA : r a < 0
  · have ha1 : a ≠ z₁ := by rintro rfl; linarith
    have ha2 : a ≠ z₂ := by rintro rfl; linarith
    exact ⟨z₁, z₂, a, hz₁.le, lt_of_le_of_ne ha.1 (Ne.symm ha1), lt_of_le_of_ne ha.2 ha2, hA.le,
      fun x hx => hamin hx⟩
  by_cases hB : r b < 0
  · have hb1 : b ≠ z₂ := by rintro rfl; linarith
    have hb2 : b ≠ z₃ := by rintro rfl; linarith
    exact ⟨z₂, z₃, b, (le_trans hz₁.le hz₂.le), lt_of_le_of_ne hb.1 (Ne.symm hb1),
      lt_of_le_of_ne hb.2 hb2, hB.le, fun x hx => hbmin hx⟩
  push Not at hA hB
  refine ⟨z₁, z₃, z₂, hz₁.le, hz₂, hz₃, hr₂.le, fun x hx => ?_⟩
  change r z₂ ≤ r x
  rw [hr₂]
  rcases le_total x z₂ with hx2 | hx2
  · exact le_trans hA (hamin ⟨hx.1, hx2⟩)
  · exact le_trans hB (hbmin ⟨hx2, hx.2⟩)

/-- **Criticality of `ξ` in the exactly modular charge direction.**  For every `ε > 0` there is
`0 < s < ε` such that `Ξ + sΞ₁` has a zero strictly inside the upper half of the critical strip. -/
theorem thetaGroup_charge_critical {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧
      XiC z + (s : ℂ) * thetaGroupXi 1 z = 0 := by
  obtain ⟨U, hU, hdom⟩ := XiC_le_eps_thetaGroupXi_one (ε := ε / 2) (by positivity)
  obtain ⟨p, q, u, hpU, hpu, huq, hm0, hmin⟩ :=
    exists_interior_min_ratio (U := U) (fun v hv => (hdom v hv).1)
  set f : ℂ → ℂ := XiC with hf
  set g : ℂ → ℂ := thetaGroupXi 1 with hg
  have hfd : Differentiable ℂ f := XiC_differentiable
  have hgd : Differentiable ℂ g := differentiable_thetaGroupXi 1
  -- real values
  have hgreal : ∀ x : ℝ, g (x : ℂ) = (((g (x : ℂ)).re : ℝ) : ℂ) := fun x =>
    Complex.ext (by simp) (by simp [hg, thetaGroupXi_one_ofReal_im])
  have hfreal : ∀ x : ℝ, f (x : ℂ) = (((f (x : ℂ)).re : ℝ) : ℂ) := fun x =>
    Complex.ext (by simp) (by simp [hf, XiC_ofReal_im_eq_zero])
  have hgu : g (u : ℂ) ≠ 0 := by
    intro h; have := (hdom u (le_trans hpU hpu.le)).1; rw [h] at this; simp at this
  set m : ℝ := (f (u : ℂ)).re / (g (u : ℂ)).re with hm
  have hmabs : |m| ≤ ε / 2 := by
    have hb := (hdom u (le_trans hpU hpu.le)).2
    have hgre := (hdom u (le_trans hpU hpu.le)).1
    rw [hm, abs_div, div_le_iff₀ (abs_pos.mpr hgre.ne)]
    rw [hfreal u, hgreal u, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs] at hb
    exact hb
  -- the ratio and its analyticity at `u`
  set R : ℂ → ℂ := fun w => f w / g w with hR
  have hRan : AnalyticAt ℂ R (u : ℂ) :=
    (hfd.analyticAt _).div (hgd.analyticAt _) hgu
  have hRu : R (u : ℂ) = (m : ℂ) := by
    simp only [hR]; rw [hfreal u, hgreal u, hm]; push_cast; ring
  rcases hRan.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · -- constant ratio forces `ξ ≡ mΞ₁`, impossible at a zero of `ξ` unless `ξ ≡ 0`
    exfalso
    have hgev : ∀ᶠ w in 𝓝 (u : ℂ), g w ≠ 0 :=
      hgd.continuous.continuousAt.eventually_ne hgu
    have hzero : (fun w => f w - (m : ℂ) * g w) =ᶠ[𝓝 (u : ℂ)] 0 := by
      filter_upwards [hconst, hgev] with w hw hgw
      simp only [Pi.zero_apply]
      rw [hRu] at hw; simp only [hR] at hw
      rw [div_eq_iff hgw] at hw; rw [hw]; ring
    have han : AnalyticOnNhd ℂ (fun w => f w - (m : ℂ) * g w) univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hfd.sub (hgd.const_mul _))
    have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ _) hzero
    obtain ⟨z₁, hz₁, hX₁⟩ := exists_Xi_zero_gt U
    have h1 := heq (mem_univ (z₁ : ℂ))
    have h0 : f (z₁ : ℂ) = 0 := by simp only [hf]; rw [XiC_ofReal, hX₁]; simp
    have hgz : g (z₁ : ℂ) ≠ 0 := by
      intro h; have := (hdom z₁ hz₁.le).1; rw [h] at this; simp at this
    simp only [Pi.zero_apply] at h1
    rw [h0, zero_sub, neg_eq_zero, mul_eq_zero] at h1
    have hm0' : (m : ℂ) = 0 := h1.resolve_right hgz
    have h2 := heq (mem_univ (-Complex.I / 2))
    simp only [Pi.zero_apply, hm0', zero_mul, sub_zero, hf] at h2
    rw [XiC_neg_I_half] at h2; norm_num at h2
  · -- open mapping near the minimizer
    have hgev : ∀ᶠ w in 𝓝 (u : ℂ), g w ≠ 0 :=
      hgd.continuous.continuousAt.eventually_ne hgu
    obtain ⟨ρ₀, hρ₀, hρ₀ball⟩ := Metric.eventually_nhds_iff.mp hgev
    set ρ : ℝ := min (min ρ₀ (1 / 4)) (min (u - p) (q - u)) with hρ
    have hρpos : 0 < ρ := by
      simp only [hρ]; apply lt_min (lt_min hρ₀ (by norm_num)) (lt_min (by linarith) (by linarith))
    have hball : Metric.ball (u : ℂ) ρ ∈ 𝓝 (u : ℂ) := Metric.ball_mem_nhds _ hρpos
    have himg : R '' Metric.ball (u : ℂ) ρ ∈ 𝓝 (m : ℂ) := by
      rw [← hRu]; exact hopen (Filter.image_mem_map hball)
    obtain ⟨δ₀, hδ₀, hδ₀ball⟩ := Metric.mem_nhds_iff.mp himg
    set δ : ℝ := min (δ₀ / 2) (ε / 4) with hδ
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hmem : ((m - δ : ℝ) : ℂ) ∈ Metric.ball (m : ℂ) δ₀ := by
      rw [Metric.mem_ball, Complex.dist_eq]
      rw [show ((m - δ : ℝ) : ℂ) - (m : ℂ) = ((-δ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_neg, abs_of_pos hδpos]
      have : δ ≤ δ₀ / 2 := min_le_left _ _
      linarith
    obtain ⟨w, hw, hRw⟩ := hδ₀ball hmem
    have hwdist : dist w (u : ℂ) < ρ := hw
    have hgw : g w ≠ 0 := hρ₀ball (lt_of_lt_of_le hwdist
      (le_trans (min_le_left _ _) (min_le_left _ _)))
    -- `w` is not real
    have hwim : w.im ≠ 0 := by
      intro him
      have hwre : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      have hd : |w.re - u| < ρ := by
        have := hwdist
        rw [hwre, Complex.dist_eq, show ((w.re : ℝ) : ℂ) - (u : ℂ) = ((w.re - u : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at this
        exact this
      have hρ1 : ρ ≤ u - p := le_trans (min_le_right _ _) (min_le_left _ _)
      have hρ2 : ρ ≤ q - u := le_trans (min_le_right _ _) (min_le_right _ _)
      have hx : w.re ∈ Icc p q := by
        constructor <;> linarith [abs_lt.mp hd]
      have hle := hmin w.re hx
      have hRw' : R w = (((f (w.re : ℂ)).re / (g (w.re : ℂ)).re : ℝ) : ℂ) := by
        have e : R w = R ((w.re : ℝ) : ℂ) := by rw [← hwre]
        rw [e]; simp only [hR]; rw [Complex.ofReal_div, ← hfreal w.re, ← hgreal w.re]
      rw [hRw', Complex.ofReal_inj] at hRw
      simp only [hf, hg] at hRw hle
      linarith
    -- the zero
    have hzero : f w + ((δ - m : ℝ) : ℂ) * g w = 0 := by
      simp only [hR] at hRw
      rw [div_eq_iff hgw] at hRw
      rw [hRw]; push_cast; ring
    have hs : 0 < δ - m := by linarith
    have hsε : δ - m < ε := by
      have : δ ≤ ε / 4 := min_le_right _ _
      have := neg_abs_le m
      linarith
    have hwim1 : |w.im| < 1 / 2 := by
      have := Complex.abs_im_le_norm (w - (u : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      rw [← Complex.dist_eq] at this
      have hρ4 : ρ ≤ 1 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
      linarith
    refine ⟨δ - m, hs, hsε, ?_⟩
    rcases lt_or_gt_of_ne hwim with hlt | hgt
    · refine ⟨-w, by simp; linarith, by simp; linarith [abs_lt.mp hwim1], ?_⟩
      have e1 : f (-w) = f w := XiC_neg w
      have e2 : g (-w) = g w := thetaGroupXi_one_neg w
      rw [e1, e2]; exact hzero
    · exact ⟨w, hgt, by linarith [abs_lt.mp hwim1], hzero⟩

end RHTower
