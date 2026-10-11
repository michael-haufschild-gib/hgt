import GaloisForLFunctions.RHTower.XiCosineShiftLaguerreTraces
import GaloisForLFunctions.RHTower.XiCosineShiftCriticalScaleDefectCount
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMomentExponential

/-!
# The Laguerre criterion at the critical scale

`Q(s) = (Im ξ'(s))² + Re ξ(s) · Re ξ''(s)`, and RH is `Q > 0` on `½ < Re s < 1`
(`riemannHypothesis_iff_strict_laguerre_strip`).

**Theorem** (`exists_volume_laguerreFail_criticalScale_le`). There are `D, K ≥ 0` such that for all
large `U` some window `[T₁, T₂]`, with `T₁ ≈ U/4` and `T₂ ≈ U/2`, has the following property. For
every `c ≥ 2`, the heights `t ∈ [T₁ + 1, T₂ − 1]` at which `Q(½ + h + it) < 0` for some depth
`h ≥ c/log U` have measure at most `4((D/c)(T₂ − T₁) + K log² U)`.

So at depths at least `c/log U` the strict-strip criterion holds at all but an `O(1/c)` proportion
of heights, unconditionally. With the exponential near-line density the proportion improves to
`O(e^{−c/28})` (`exists_volume_laguerreFail_criticalScale_le_exp`).

**Proof.** A failure at `(h, t)` lies in the doubled trace `|t − γ| < 2√((β − ½)² − h²)` of a zero
`ρ = β + iγ` with `β − ½ > h ≥ c/log U` (`laguerre_nonneg_of_trace`). The trace has length at most
`4(β − ½)`. So the failure set has measure at most `4 Σ_{β − ½ ≥ c/log U} m_ρ (β − ½)`, which is the
critical-scale tail moment (`volume_laguerreFail_le_tailMoment`), bounded by
`exists_offLineTailMoment_window_le` and `exists_offLineTailMoment_window_le_exp`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- The zeta zeros of a Littlewood box form a finite set. -/
theorem exists_finset_zetaZeros_box {T₁ T₂ : ℝ} (hT₁ : 1 < T₁) (hT12 : T₁ < T₂) :
    ∃ Z : Finset ℂ, ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
  classical
  have hfinZ : {z : ℂ | z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0}.Finite := by
    have hxi : AnalyticOnNhd ℂ xi univ := xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have hfin := entire_zeros_closedRectangle_finite hxi ⟨2, xi_ne_zero_of_one_le (by simp)⟩
      (((1 / 2 : ℝ) : ℂ) + T₁ * I) (((15 / 2 : ℝ) : ℂ) + T₂ * I)
    refine hfin.subset ?_
    rintro z ⟨hzR, hz0⟩
    refine ⟨by simpa using hzR, ?_⟩
    have hre := (mem_reProdIm.mp hzR).1
    have him := (mem_reProdIm.mp hzR).2
    rw [uIcc_of_le (by norm_num)] at hre
    rw [uIcc_of_le hT12.le] at him
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at him; simp at him; linarith [him.1]
    exact (xi_eq_zero_iff (by linarith [hre.1]) hz1).mpr hz0
  exact ⟨hfinZ.toFinset, fun z => by rw [Set.Finite.mem_toFinset]; rfl⟩

/-- **Covering by doubled traces.** On a box `[½, 15/2] × [T₁, T₂]`, the heights
`t ∈ [T₁ + 1, T₂ − 1]` at which `Q(½ + h + it) < 0` for some depth `h ≥ δ > 0` have measure at most
four times the off-line first moment of the zeros with `Re ρ − ½ ≥ δ`. -/
theorem volume_laguerreFail_le_tailMoment {T₁ T₂ δ : ℝ} (hT12 : T₁ < T₂) (hδ : 0 < δ)
    {Z : Finset ℂ} (hZmem : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧ ∃ h : ℝ, δ ≤ h ∧
        foldFx h t ^ 2 - foldF h t * foldFxx h t < 0}
      ≤ ENNReal.ofReal (4 * ∑ w ∈ Z.filter (fun w => 1 / 2 + δ ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)) := by
  classical
  set F := Z.filter (fun w => 1 / 2 + δ ≤ w.re) with hF
  have hsub : {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧ ∃ h : ℝ, δ ≤ h ∧
      foldFx h t ^ 2 - foldF h t * foldFxx h t < 0} ⊆
      ⋃ w ∈ F, Icc (w.im - 2 * (w.re - 1 / 2)) (w.im + 2 * (w.re - 1 / 2)) := by
    rintro t ⟨ht, h, hch, hQ⟩
    have hh : 0 < h := lt_of_lt_of_le hδ hch
    obtain ⟨w, hw, hwh, hlt⟩ : ∃ w : ℂ, XiC w = 0 ∧ h ^ 2 < w.im ^ 2 ∧
        (t - w.re) ^ 2 < 4 * (w.im ^ 2 - h ^ 2) := by
      by_contra hno
      push Not at hno
      exact absurd (laguerre_nonneg_of_trace hh hno) (not_le.mpr hQ)
    have him2 : w.im ^ 2 ≤ 1 / 4 := by
      have h0 : DeBruijn.cosTransform riemannKernelReal w = 0 := by
        rw [DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hw
      exact DeBruijn.riemannKernel_zeros_im_sq_le w h0
    have habs : |w.im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    have hhw : h < |w.im| := by
      by_contra hle; push Not at hle
      nlinarith [sq_abs w.im, abs_nonneg w.im]
    have hdist : |t - w.re| < 2 * |w.im| := by
      have : (t - w.re) ^ 2 < (2 * |w.im|) ^ 2 := by
        rw [mul_pow, sq_abs]; nlinarith [sq_nonneg h]
      exact abs_lt_of_sq_lt_sq this (by positivity)
    set ρ : ℂ := 1 / 2 + I * w with hρ
    have hρ0 : xi ρ = 0 := by
      have e : XiC w = xi ρ := by rw [hρ, XiC, mul_comm]
      rw [← e]; exact hw
    have hρre : ρ.re = 1 / 2 - w.im := by simp [hρ]; ring
    have hρim : ρ.im = w.re := by simp [hρ]
    obtain ⟨u, hu, hure, huim⟩ : ∃ u : ℂ, xi u = 0 ∧ u.re = 1 / 2 + |w.im| ∧ u.im = w.re := by
      rcases le_or_gt w.im 0 with hcw | hcw
      · refine ⟨ρ, hρ0, ?_, hρim⟩
        rw [hρre, abs_of_nonpos hcw]; ring
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ0, map_zero], ?_, ?_⟩
        · rw [abs_of_pos hcw]; simp [hρre]; ring
        · simp [hρim]
    have hdist' := abs_lt.mp hdist
    have hu1 : u.re < 1 := xi_zero_re_lt_one hu
    have huF : u ∈ F := by
      rw [hF, Finset.mem_filter, hZmem]
      have hu1' : u ≠ 1 := fun e => by rw [e] at hu1; simp at hu1
      refine ⟨⟨?_, (xi_eq_zero_iff (by rw [hure]; linarith [abs_nonneg w.im]) hu1').mp hu⟩, ?_⟩
      · rw [mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le hT12.le]
        refine ⟨⟨by rw [hure]; linarith [abs_nonneg w.im], by linarith⟩, ?_, ?_⟩
        · rw [huim]; linarith [ht.1, hdist'.2, habs]
        · rw [huim]; linarith [ht.2, hdist'.1, habs]
      · rw [hure]; linarith
    refine Set.mem_iUnion₂.mpr ⟨u, huF, ?_, ?_⟩
    · rw [huim, hure]; linarith [hdist'.2]
    · rw [huim, hure]; linarith [hdist'.1]
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - 2 * (w.re - 1 / 2)) (w.im + 2 * (w.re - 1 / 2))) ≤
      ENNReal.ofReal (4 * (((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    rw [hF, Finset.mem_filter, hZmem] at hw
    obtain ⟨⟨-, hw0⟩, hwre⟩ := hw
    have hwre' : 1 / 2 < w.re := by linarith
    have hwlt1 : w.re < 1 := by
      by_contra hcon; push Not at hcon
      exact riemannZeta_ne_zero_of_one_le_re hcon hw0
    have hw1 : w ≠ 1 := fun e => by rw [e] at hwlt1; simp at hwlt1
    have hxi0 : xi w = 0 := (xi_eq_zero_iff (by linarith) hw1).mpr hw0
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi hxi0
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨by linarith, hwlt1⟩] at hm
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : ∀ w ∈ F, 0 ≤ 4 * (((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)) := by
    intro w hw
    rw [hF, Finset.mem_filter] at hw
    have : (0 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ w.re - 1 / 2 := by linarith [hw.2]
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.mul_sum]

/-- **The strict-strip criterion at the critical scale.** -/
theorem exists_volume_laguerreFail_criticalScale_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 2 ≤ c →
        volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧ ∃ h : ℝ, c / Real.log U ≤ h ∧
            foldFx h t ^ 2 - foldF h t * foldFxx h t < 0}
          ≤ ENNReal.ofReal (4 * (D / c * (T₂ - T₁) + K * Real.log U ^ 2)) := by
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (100 : ℝ)] with U hU hU1
  obtain ⟨T₁, hT₁, T₂, hT₂, hmom⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc => ?_⟩
  have hL : 0 < Real.log U := Real.log_pos (by linarith)
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZmem⟩ := exists_finset_zetaZeros_box (by linarith [hT₁.1]) hT12
  refine (volume_laguerreFail_le_tailMoment hT12 (by positivity) hZmem).trans ?_
  apply ENNReal.ofReal_le_ofReal
  linarith [hmom Z hZmem c hc]

/-- **The strict-strip criterion at the critical scale, exponential form.** The heights
`t ∈ [T₁ + 1, T₂ − 1]` at which `Q(½ + h + it) < 0` for some depth `h ≥ c/log U` have measure at
most `4(B e^{−c/28}(T₂ − T₁) + K log² U)`. -/
theorem exists_volume_laguerreFail_criticalScale_le_exp :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 2 ≤ c →
        volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧ ∃ h : ℝ, c / Real.log U ≤ h ∧
            foldFx h t ^ 2 - foldF h t * foldFxx h t < 0}
          ≤ ENNReal.ofReal
            (4 * (B * Real.exp (-(c / 28)) * (T₂ - T₁) + K * Real.log U ^ 2)) := by
  obtain ⟨B, K, hB, hK, htail⟩ := exists_offLineTailMoment_window_le_exp
  refine ⟨B, K, hB, hK, ?_⟩
  filter_upwards [htail, eventually_gt_atTop (100 : ℝ)] with U hU hU1
  obtain ⟨T₁, hT₁, T₂, hT₂, hmom⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc => ?_⟩
  have hL : 0 < Real.log U := Real.log_pos (by linarith)
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZmem⟩ := exists_finset_zetaZeros_box (by linarith [hT₁.1]) hT12
  refine (volume_laguerreFail_le_tailMoment hT12 (by positivity) hZmem).trans ?_
  apply ENNReal.ofReal_le_ofReal
  linarith [hmom Z hZmem c hc]

end

end RHTower
