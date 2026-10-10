import GaloisForLFunctions.RHTower.XiCosineShiftCriticalScaleProducer
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper

/-!
# Heights that are lossless at every depth

A non-real zero `z` of `cos(hD)Ξ`, for any `h > 0`, has real part in the shadow
`[γ − (β − ½), γ + (β − ½)]` of a zero `ρ = β + iγ` of `ξ` with `β > ½`
(`exists_xiZero_shadow_of_cosineShift_nonreal`, reflected by `ρ ↦ 1 − ρ̄`). The shadow does not
depend on `h`. The union of all shadows up to height `V` has measure at most twice the off-line first
moment `Σ m_ρ (β − ½)`:

* `volume_cosineShift_anyDepth_nonrealHeight_le`: the heights `t ∈ [20, V]` carrying a non-real
  zero of `cos(hD)Ξ` with real part `t`, for some `h > 0`, have measure at most
  `2·offLineMoment(V + 1)`;
* `eventually_volume_cosineShift_anyDepth_nonrealHeight_le`: with Selberg's weights
  (`offLineMoment V ≤ 67V/1000`), this measure is at most `67(V + 1)/500` for all large `V`.

So on at least `86.6%` of the heights the producer `cos(hD)Ξ` is lossless at *every* depth `h > 0`
simultaneously, unconditionally.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- **Lossless at every depth outside the off-line shadows.** -/
theorem volume_cosineShift_anyDepth_nonrealHeight_le (V : ℝ) :
    volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, 0 < h ∧
        ∃ z : ℂ, z.re = t ∧ z.im ≠ 0 ∧ (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0}
      ≤ ENNReal.ofReal (2 * offLineMoment (V + 1)) := by
  classical
  set F := boxFinsetLe (V + 1) with hF
  have hsub : {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, 0 < h ∧
      ∃ z : ℂ, z.re = t ∧ z.im ≠ 0 ∧ (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, h, hh, z, hzt, hz, h0⟩
    obtain ⟨ρ, hρ, hdeep, hdist⟩ := exists_xiZero_shadow_of_cosineShift_nonreal hh hz h0
    rw [hzt] at hdist
    have hlt1 : ρ.re < 1 := by
      by_contra hc; push Not at hc; exact xi_ne_zero_of_one_le_re hc hρ
    have hgt0 : 0 < ρ.re := by
      by_contra hc
      push Not at hc
      apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
      rw [xi_one_sub]; exact hρ
    obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, xi w = 0 ∧ w.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        w.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with hc | hc
      · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ, map_zero], ?_, by simp⟩
        rw [abs_of_neg (by linarith)]; simp; ring
    have hrhalf : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have htw : |t - w.im| ≤ w.re - 1 / 2 := by rw [hwim, hwre]; linarith
    have htw' := abs_le.mp htw
    have hwmem : w ∈ F := by
      rw [hF, mem_boxFinsetLe]
      refine ⟨by rw [hwre]; linarith [hh.trans hdeep], xi_zero_re_lt_one hw, ?_, ?_, hw⟩
      · linarith [ht.1]
      · linarith [ht.2]
    exact Set.mem_iUnion₂.mpr ⟨w, hwmem, by linarith, by linarith⟩
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
  have hnn : ∀ w ∈ F, 0 ≤ 2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2)) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    have := hw.1
    have : (0 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  rfl

/-- **At least `86.6%` of the heights are lossless at every depth.** -/
theorem eventually_volume_cosineShift_anyDepth_nonrealHeight_le :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ ∃ h : ℝ, 0 < h ∧
          ∃ z : ℂ, z.re = t ∧ z.im ≠ 0 ∧ (XiC (z + h * I) + XiC (z - h * I)) / 2 = 0}
        ≤ ENNReal.ofReal (67 / 500 * (V + 1)) := by
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  filter_upwards [hshift.eventually ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper] with V hV
  refine (volume_cosineShift_anyDepth_nonrealHeight_le V).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith

end

end RHTower
