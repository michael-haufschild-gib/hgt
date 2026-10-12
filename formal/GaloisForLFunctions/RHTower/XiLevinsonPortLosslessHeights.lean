import GaloisForLFunctions.RHTower.XiLevinsonPortDefectShadows
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper
import GaloisForLFunctions.RHTower.EMAnnulusSupply

/-!
# The canonical producer is lossless at most heights, uniformly in the coupling

For `λ > 0` the canonical producer `ξ − λξ'` has a defect at height `t` if it vanishes at a point
`s` with `Im s = t` and `Re s < ½`.

**Theorem** (`volume_levinsonDefectHeights_le`). The heights `t ∈ [20, V]` at which the producer
has a defect for *some* coupling `λ > 0` have Lebesgue measure at most `2·M(V + 1)`, where
`M(U) = Σ m_ρ (β − ½)` is the off-line first moment over the zeros with `½ < β`, `0 ≤ γ ≤ U`.

**Proof.** A defect `s` lies in the shadow disk of an off-line zero `ρ`
(`exists_offLine_shadow_of_levinson_defect`), so `|Im s − γ| ≤ |β − ½|`. The zero `ρ` or its mirror
`1 − ρ̄` lies right of the line with the same ordinate. The defect heights are therefore covered by
the intervals `[γ − (β − ½), γ + (β − ½)]` of the box zeros, of total length `2·M(V + 1)`.

**Corollary** (`eventually_volume_levinsonDefectHeights_le`). With the corpus bound
`M(V) ≤ 0.067 V`, for all large `V` the defect heights have measure at most `0.134 (V + 1)`. So on at
least `86%` of the heights in `[20, V]`, the producer has no defect on the horizontal line for
any `λ > 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- **Defect heights of the canonical producer** have measure at most twice the off-line
moment. -/
theorem volume_levinsonDefectHeights_le (V : ℝ) :
    volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ s : ℂ, s.im = t ∧ s.re < 1 / 2 ∧
        xi s - (lam : ℂ) * deriv xi s = 0}
      ≤ ENNReal.ofReal (2 * offLineMoment (V + 1)) := by
  classical
  set F := boxFinsetLe (V + 1) with hF
  have hsub : {t : ℝ | t ∈ Icc 20 V ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ s : ℂ, s.im = t ∧ s.re < 1 / 2 ∧
      xi s - (lam : ℂ) * deriv xi s = 0} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, lam, hlam, s, hst, hre, hs⟩
    obtain ⟨q, hq, hle⟩ := exists_offLine_shadow_of_levinson_defect hlam hs hre
    set ρ : ℂ := (q.1 : ℂ) with hρ
    have hρ0 : xi ρ = 0 := xi_xiZeroCopy_eq_zero q
    -- the ordinate offset is at most the depth
    have hoff : |t - ρ.im| ≤ |ρ.re - 1 / 2| := by
      rw [← hst, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 / 2 - s.re)])
    -- the zero right of the line with the same ordinate
    obtain ⟨u, hu, hure, huim⟩ : ∃ u : ℂ, xi u = 0 ∧ u.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        u.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with hc | hc
      · exact ⟨ρ, hρ0, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ0, map_zero], ?_, ?_⟩
        · rw [abs_of_neg (by linarith)]; simp; ring
        · simp
    have hpos : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq)
    have hu1 := xi_zero_re_lt_one hu
    have hhalf : |ρ.re - 1 / 2| < 1 / 2 := by linarith
    have hoff' := abs_le.mp hoff
    have humem : u ∈ F := by
      rw [hF, mem_boxFinsetLe]
      refine ⟨by linarith, hu1, ?_, ?_, hu⟩
      · rw [huim]; linarith [ht.1]
      · rw [huim]; linarith [ht.2]
    refine Set.mem_iUnion₂.mpr ⟨u, humem, ?_, ?_⟩
    · rw [huim, hure]; linarith
    · rw [huim, hure]; linarith
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) ≤
      ENNReal.ofReal (2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    obtain ⟨hw1, -, -, -, hw0⟩ := hw
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi hw0
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : ∀ w ∈ F, 0 ≤ 2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2)) :=
    fun w hw => mul_nonneg (by norm_num) (offLineMoment_term_nonneg hw)
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  rfl

/-- **The canonical producer is lossless at most heights.** For all large `V`, the heights in
`[20, V]` carrying a defect of `ξ − λξ'` for some `λ > 0` have measure at most `0.134 (V + 1)`. -/
theorem eventually_volume_levinsonDefectHeights_le :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ s : ℂ, s.im = t ∧ s.re < 1 / 2 ∧
          xi s - (lam : ℂ) * deriv xi s = 0}
        ≤ ENNReal.ofReal (134 / 1000 * (V + 1)) := by
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  filter_upwards [hshift.eventually ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper]
    with V hV
  refine (volume_levinsonDefectHeights_le V).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith

end

end RHTower
