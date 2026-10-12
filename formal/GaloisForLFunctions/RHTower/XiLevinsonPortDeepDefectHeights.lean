import GaloisForLFunctions.RHTower.XiLevinsonPortLosslessHeights
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMomentExponential
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodRectangle
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# Deep defects of the canonical producer are exponentially rare

For `λ > 0` call a zero `s` of `ξ − λξ'` with `Re s < ½` a defect of depth `½ − Re s`.

**Theorem** (`exists_levinsonDeepDefectHeights_le_exp`). There are constants `B, K ≥ 0` such that
for all large `U` there is a Littlewood window `[T₁, T₂] ≈ [U/4, U/2]` on which, for every
`c ≥ 2`, the heights `t ∈ [T₁ + 1, T₂ − 1]` carrying a defect of depth at least `c / log U`, for
some `λ > 0`, have measure at most `2(B e^{−c/28}(T₂ − T₁) + K log² U)`.

**Proof.** A defect of depth `d` lies in the shadow disk of an off-line zero `ρ`
(`exists_offLine_shadow_of_levinson_defect`), so `|β − ½| ≥ d` and `|t − γ| ≤ |β − ½|`. The zero
right of the line with ordinate `γ` is a zero of `ζ` in Selberg's box with `Re ≥ ½ + c/log U`.
The defect heights are covered by its intervals `[γ − (β − ½), γ + (β − ½)]`, whose total length
is twice the critical-scale tail moment, which is exponentially small in `c`
(`exists_offLineTailMoment_window_le_exp`, from Selberg's near-line density).

Together with `volume_levinsonDefectHeights_le`, this means the producer is lossless outside the
critical layer `½ − C/log U < Re s < ½` at all but an `O(e^{−C/28})` proportion of heights,
uniformly in the coupling.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Deep defects of the canonical producer occupy exponentially few heights.** -/
theorem exists_levinsonDeepDefectHeights_le_exp :
    ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2), ∀ c : ℝ, 2 ≤ c →
        volume {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ s : ℂ,
            s.im = t ∧ s.re ≤ 1 / 2 - c / Real.log U ∧ xi s - (lam : ℂ) * deriv xi s = 0}
          ≤ ENNReal.ofReal (2 * (B * Real.exp (-(c / 28)) * (T₂ - T₁) + K * Real.log U ^ 2)) := by
  classical
  obtain ⟨B, K, hB, hK, hev⟩ := exists_offLineTailMoment_window_le_exp
  refine ⟨B, K, hB, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (8 : ℝ)]
    with U hU hUe hU8
  obtain ⟨T₁, hT₁, T₂, hT₂, htail⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc => ?_⟩
  set L := Real.log U with hLdef
  have hL1 : 1 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hUe
    rwa [Real.log_exp] at this
  have hcL : 0 < c / L := div_pos (by linarith) (by linarith)
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  -- the zeros of `ζ` in Selberg's box
  have hfinZ : {z : ℂ | z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0}.Finite := by
    have hxi : AnalyticOnNhd ℂ xi univ :=
      xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ
    have hfin := entire_zeros_closedRectangle_finite hxi ⟨2, fun h2 => riemannZeta_ne_zero_of_one_le_re (s := 2) (by simp)
      ((xi_eq_zero_iff (by simp) (by norm_num)).mp h2)⟩
      (((1 / 2 : ℝ) : ℂ) + T₁ * I) (((15 / 2 : ℝ) : ℂ) + T₂ * I)
    refine hfin.subset ?_
    rintro z ⟨hzR, hz0⟩
    refine ⟨by simpa using hzR, ?_⟩
    have hre := (mem_reProdIm.mp hzR).1
    have him := (mem_reProdIm.mp hzR).2
    rw [uIcc_of_le (by norm_num)] at hre
    rw [uIcc_of_le hT12] at him
    have hz1 : z ≠ 1 := by
      intro h1; rw [h1] at him; simp at him; linarith [him.1, hT₁.1]
    exact (xi_eq_zero_iff (by linarith [hre.1]) hz1).mpr hz0
  set Z := hfinZ.toFinset with hZ
  have hZmem : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧
      riemannZeta z = 0 := fun z => by rw [hZ, Set.Finite.mem_toFinset]; rfl
  set F := Z.filter (fun w => 1 / 2 + c / L ≤ w.re) with hF
  -- the cover by shadow intervals
  have hsub : {t : ℝ | t ∈ Icc (T₁ + 1) (T₂ - 1) ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ s : ℂ,
      s.im = t ∧ s.re ≤ 1 / 2 - c / L ∧ xi s - (lam : ℂ) * deriv xi s = 0} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, lam, hlam, s, hst, hre, hs⟩
    obtain ⟨q, hq, hle⟩ := exists_offLine_shadow_of_levinson_defect hlam hs (by linarith)
    set ρ : ℂ := (q.1 : ℂ) with hρ
    have hρ0 : xi ρ = 0 := xi_xiZeroCopy_eq_zero q
    have hpos : 0 < 1 / 2 - s.re := by linarith
    have hdepth : 1 / 2 - s.re ≤ |ρ.re - 1 / 2| := by
      rw [← Real.sqrt_sq hpos.le, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (s.im - ρ.im)])
    have hoff : |t - ρ.im| ≤ |ρ.re - 1 / 2| := by
      rw [← hst, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 / 2 - s.re)])
    obtain ⟨u, hu, hure, huim⟩ : ∃ u : ℂ, xi u = 0 ∧ u.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        u.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with hc' | hc'
      · exact ⟨ρ, hρ0, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ0, map_zero], ?_, ?_⟩
        · rw [abs_of_neg (by linarith)]; simp; ring
        · simp
    have hu1 := xi_zero_re_lt_one hu
    have hhalf : |ρ.re - 1 / 2| < 1 / 2 := by linarith
    have hoff' := abs_le.mp hoff
    have hu1' : u ≠ 1 := by intro h1; rw [h1] at hu1; simp at hu1
    have humem : u ∈ F := by
      rw [hF, Finset.mem_filter, hZmem]
      refine ⟨⟨?_, (xi_eq_zero_iff (by linarith) hu1').mp hu⟩, by linarith⟩
      rw [mem_reProdIm, uIcc_of_le (by norm_num), uIcc_of_le hT12]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by rw [huim]; linarith [ht.1],
        by rw [huim]; linarith [ht.2]⟩⟩
    refine Set.mem_iUnion₂.mpr ⟨u, humem, ?_, ?_⟩
    · rw [huim, hure]; linarith
    · rw [huim, hure]; linarith
  -- the length of the cover is twice the tail moment
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) ≤
      ENNReal.ofReal (2 * (((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    rw [hF, Finset.mem_filter, hZmem] at hw
    obtain ⟨⟨hR, hw0⟩, hwre⟩ := hw
    have hre1 : w.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hw0
    have hw1 : w ≠ 1 := by intro h1; rw [h1] at hre1; simp at hre1
    have hreh : 1 / 2 < w.re := by linarith
    have hxw : xi w = 0 := (xi_eq_zero_iff (by linarith) hw1).mpr hw0
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi hxw
    rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨by linarith, hre1⟩] at hm
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : ∀ w ∈ F, 0 ≤ 2 * (((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2)) := by
    intro w hw
    rw [hF, Finset.mem_filter] at hw
    have : 0 ≤ w.re - 1 / 2 := by linarith [hw.2]
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  have h := htail Z hZmem c hc
  linarith

end

end RHTower
