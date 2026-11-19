import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheLogarithmicWallCuspOfAFiniteLayer

/-!
# Crowding and sample bounds saturate the logarithmic wall cusp

This module answers the model-separation question of §2.17: critical-line zero crowding,
Riemann–von Mangoldt ordinate density, bounded rescaled unit-window sample sums, bounded
imaginary-axis derivative, and the shift-invariant `Γ_ℝ` half-line energy domain **jointly admit**
rescaled Laplace amplitudes of order `1 / √(log y)` and **sustain** a strictly positive
logarithmic wall-cusp coefficient.

Specifically, for every amplitude `ℓ ∈ ℝ`, the compactly supported collar profile
`smoothedWallLogProfile ℓ (u) = ℓ (1 + 8u)² (log(1/|u|))^{-1/2} 1_{(-1/8, 0)}(u)` satisfies:

1. `CriticalHalfLineEnergyDomain (smoothedWallLogProfile ℓ)`;
2. `(log(1/h)/h) ∫_{-h}^0 F_ℓ(u)² du → ℓ²` as `h → 0⁺` (admitting no vanishing subsequence when
   `ℓ ≠ 0`), `(x log x) ∫_0^∞ e^{-2xv} F_ℓ(-v)² dv → ℓ² / 2`,
   `(x log x) ∫_ℝ ‖L F_ℓ(x + iy)‖² dy → π ℓ²`, while `h⁻¹ ∫_{-h}^0 F_ℓ(u)² du → 0` and
   `h⁻¹ ∫_ℝ (F_ℓ(u) - F_ℓ(u + h))² e^{-8u} du → 0`;
3. `‖(w + 5) L F_ℓ(w)‖ ≤ C |ℓ| / √(log(‖w‖ + 4))` uniformly on `Re w ≥ -4`, uniform Lipschitz
   continuity of `y ↦ (iy + 5) L F_ℓ(iy)`, and the exact imaginary-axis asymptotic
   `y √(log y) L F_ℓ(iy) → -i ℓ` (`y² (log y) ‖L F_ℓ(iy)‖² → ℓ²`) as `y → +∞`;
4. Unconditional boundedness of the rescaled unit-window sample sum and `σ = -4` Poisson row on
   `onLineCopies` of `ζ`, paired with fixed-window mass saturation `(c_h / 2) ℓ²` over every
   crowding family (retaining explicit window-width and zero-multiplicity dependence), realized
   both unconditionally on an explicit Riemann–von Mangoldt ordinate family and on `onLineCopies`
   under `BacklundConverse.FiniteOffLine`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open scoped ComplexConjugate ENNReal NNReal

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The smoothed inverse-root-logarithm profile on `(-1/8, 0)` -/

/-- Squared piecewise-linear cutoff `(min (max (1 + 8u) 0) 1)²`: vanishes on `(-∞, -1/8]`, equals
`(1 + 8u)²` on `[-1/8, 0]`, equals `1` on `[0, ∞)`, and is globally `16`-Lipschitz. -/
def collarSmoothCutoff (u : ℝ) : ℝ := (min (max (1 + 8 * u) 0) 1) ^ 2

/-- Explicit logarithmic wall-cusp profile with cusp amplitude `ℓ`:
`ℓ (1 + 8u)² (log(1/|u|))^{-1/2}` on `(-1/8, 0)` and `0` elsewhere. -/
def smoothedWallLogProfile (ℓ u : ℝ) : ℝ :=
  ℓ * (collarSmoothCutoff u * wallLogProfile (1 / 8) u)

theorem measurable_collarSmoothCutoff : Measurable collarSmoothCutoff := by
  unfold collarSmoothCutoff
  exact ((((measurable_id.const_mul 8).const_add 1).max measurable_const).min
    measurable_const).pow_const 2

theorem collarSmoothCutoff_nonneg (u : ℝ) : 0 ≤ collarSmoothCutoff u := sq_nonneg _

theorem collarSmoothCutoff_le_one (u : ℝ) : collarSmoothCutoff u ≤ 1 := by
  unfold collarSmoothCutoff
  have h0 : 0 ≤ min (max (1 + 8 * u) 0) 1 := le_min (le_max_right _ _) zero_le_one
  have h1 : min (max (1 + 8 * u) 0) 1 ≤ 1 := min_le_right _ _
  nlinarith

theorem abs_collarSmoothCutoff_le_one (u : ℝ) : |collarSmoothCutoff u| ≤ 1 := by
  rw [abs_of_nonneg (collarSmoothCutoff_nonneg u)]
  exact collarSmoothCutoff_le_one u

theorem collarSmoothCutoff_of_mem {u : ℝ} (h1 : -(1 / 8) ≤ u) (h2 : u ≤ 0) :
    collarSmoothCutoff u = (1 + 8 * u) ^ 2 := by
  unfold collarSmoothCutoff
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]

theorem abs_collarSmoothCutoff_sub_le (u v : ℝ) :
    |collarSmoothCutoff u - collarSmoothCutoff v| ≤ 16 * |u - v| := by
  let c : ℝ → ℝ := fun t => min (max (1 + 8 * t) 0) 1
  have hc0 : ∀ t, 0 ≤ c t := fun _ => le_min (le_max_right _ _) zero_le_one
  have hc1 : ∀ t, c t ≤ 1 := fun _ => min_le_right _ _
  have hclip : |c u - c v| ≤ 8 * |u - v| := by
    calc |c u - c v|
        ≤ max |max (1 + 8 * u) 0 - max (1 + 8 * v) 0| |(1 : ℝ) - 1| :=
          abs_min_sub_min_le_max _ _ _ _
      _ = |max (1 + 8 * u) 0 - max (1 + 8 * v) 0| := by
          rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      _ ≤ |(1 + 8 * u) - (1 + 8 * v)| := abs_max_sub_max_le_abs _ _ _
      _ = 8 * |u - v| := by
          rw [show (1 + 8 * u) - (1 + 8 * v) = 8 * (u - v) by ring, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  change |c u ^ 2 - c v ^ 2| ≤ 16 * |u - v|
  rw [show c u ^ 2 - c v ^ 2 = (c u + c v) * (c u - c v) by ring, abs_mul,
    abs_of_nonneg (add_nonneg (hc0 u) (hc0 v))]
  calc (c u + c v) * |c u - c v|
      ≤ 2 * (8 * |u - v|) :=
        mul_le_mul (by linarith [hc1 u, hc1 v]) hclip (abs_nonneg _) (by norm_num)
    _ = 16 * |u - v| := by ring

theorem smoothedWallLogProfile_of_mem {ℓ u : ℝ} (h1 : -(1 / 8) < u) (h2 : u < 0) :
    smoothedWallLogProfile ℓ u = ℓ * ((1 + 8 * u) ^ 2 * (wallRootLog (-u))⁻¹) := by
  unfold smoothedWallLogProfile
  rw [collarSmoothCutoff_of_mem h1.le h2.le, wallLogProfile_of_mem h1 h2]

theorem smoothedWallLogProfile_of_le {ℓ u : ℝ} (h : u ≤ -(1 / 8)) :
    smoothedWallLogProfile ℓ u = 0 := by
  unfold smoothedWallLogProfile
  rw [wallLogProfile_of_le h, mul_zero, mul_zero]

theorem smoothedWallLogProfile_of_nonneg {ℓ u : ℝ} (h : 0 ≤ u) :
    smoothedWallLogProfile ℓ u = 0 := by
  unfold smoothedWallLogProfile
  rw [wallLogProfile_of_nonneg h, mul_zero, mul_zero]

theorem abs_smoothedWallLogProfile_le (ℓ u : ℝ) : |smoothedWallLogProfile ℓ u| ≤ |ℓ| := by
  unfold smoothedWallLogProfile
  rw [abs_mul, abs_mul]
  have h1 := abs_collarSmoothCutoff_le_one u
  have h2 := abs_wallLogProfile_le_one (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4) u
  have hp : |collarSmoothCutoff u| * |wallLogProfile (1 / 8) u| ≤ 1 := by
    nlinarith [abs_nonneg (collarSmoothCutoff u), abs_nonneg (wallLogProfile (1 / 8) u)]
  exact (mul_le_mul_of_nonneg_left hp (abs_nonneg ℓ)).trans_eq (mul_one _)

/-- **Energy-domain membership.** Every `smoothedWallLogProfile ℓ` belongs to
`CriticalHalfLineEnergyDomain`. -/
theorem criticalHalfLineEnergyDomain_smoothedWallLogProfile (ℓ : ℝ) :
    CriticalHalfLineEnergyDomain (smoothedWallLogProfile ℓ) :=
  (criticalHalfLineEnergyDomain_lipschitz_mul
    (criticalHalfLineEnergyDomain_wallLogProfile (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4))
    measurable_collarSmoothCutoff abs_collarSmoothCutoff_le_one
    abs_collarSmoothCutoff_sub_le).const_mul ℓ

/-! ### Time-domain logarithmic wall cusp, Abel mass, vertical trace, and increment laws -/

private theorem tendsto_log_div_mul_integral_inv_neg_log :
    Tendsto (fun h : ℝ => Real.log (1 / h) / h * ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹)
      (𝓝[>] 0) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η := min (1 / 4) (ε / 4)
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηε : η ≤ ε / 4 := min_le_right _ _
  set δ := min (1 / 8) (Real.exp (-(Real.log (1 / η) / η)))
  have hδ0 : 0 < δ := lt_min (by norm_num) (Real.exp_pos _)
  refine ⟨δ, hδ0, fun h (hh0 : 0 < h) hhδ => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hh0] at hhδ
  have hh8 : h < 1 / 8 := lt_of_lt_of_le hhδ (min_le_left _ _)
  have hhexp : h < Real.exp (-(Real.log (1 / η) / η)) := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hh4 : h ≤ 1 / 4 := by linarith
  have hlogh_pos : 0 < Real.log (1 / h) := Real.log_pos (by rw [lt_div_iff₀ hh0]; linarith)
  have hlogh_big : Real.log (1 / η) / η < Real.log (1 / h) := by
    have hl := Real.log_lt_log hh0 hhexp
    rw [Real.log_exp] at hl
    rw [one_div h, Real.log_inv]
    linarith
  let f : ℝ → ℝ := fun u => (-Real.log (-u))⁻¹
  have hf_eq_sq : ∀ u ∈ Ioo (-h) (0 : ℝ), f u = wallLogProfile (1 / 8) u ^ 2 := fun u hu => by
    rw [wallLogProfile_of_mem (by linarith [hu.1]) hu.2, inv_pow,
      wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1])]
  have hfi : IntegrableOn f (Ioo (-h) 0) :=
    ((criticalHalfLineEnergyDomain_wallLogProfile (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)).sq.integrableOn
      (s := Ioo (-h) 0)).congr_fun (fun u hu => (hf_eq_sq u hu).symm) measurableSet_Ioo
  have hf_nn : ∀ u ∈ Ioo (-h) (0 : ℝ), 0 ≤ f u := fun u hu => by
    rw [hf_eq_sq u hu]; exact sq_nonneg _
  have hub_int : ∫ u in Ioo (-h) 0, f u ≤ h * (Real.log (1 / h))⁻¹ := by
    have hpt : ∀ u ∈ Ioo (-h) (0 : ℝ), f u ≤ (Real.log (1 / h))⁻¹ := fun u hu => by
      dsimp only [f]
      rw [log_one_div_eq_neg_log]
      refine inv_anti₀ ?_ ?_
      · linarith [one_le_neg_log hh0 hh4]
      · linarith [Real.log_le_log (by linarith [hu.2]) (by linarith [hu.1] : -u ≤ h)]
    have hm := setIntegral_mono_on hfi
      ((continuousOn_const (c := (Real.log (1 / h))⁻¹)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      measurableSet_Ioo hpt
    rwa [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith), sub_neg_eq_add, zero_add,
      smul_eq_mul] at hm
  have hlb_int : ((1 - η) * h) * ((1 + η) * Real.log (1 / h))⁻¹ ≤ ∫ u in Ioo (-h) 0, f u := by
    have hsub : Ioo (-h) (-(η * h)) ⊆ Ioo (-h) 0 := fun u hu =>
      ⟨hu.1, lt_trans hu.2 (neg_neg_of_pos (mul_pos hη0 hh0))⟩
    have hm1 : ∫ u in Ioo (-h) (-(η * h)), f u ≤ ∫ u in Ioo (-h) 0, f u :=
      setIntegral_mono_set hfi
        ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hf_nn u hu)
        (Eventually.of_forall hsub)
    have hpt : ∀ u ∈ Ioo (-h) (-(η * h)), ((1 + η) * Real.log (1 / h))⁻¹ ≤ f u := fun u hu => by
      have hu_pos : 0 < -u := by linarith [hu.2, mul_pos hη0 hh0]
      have hgt : η * h < -u := by linarith [hu.2]
      have hl1 : Real.log (1 / (-u)) ≤ Real.log (1 / (η * h)) :=
        Real.log_le_log (one_div_pos.mpr hu_pos) (one_div_le_one_div_of_le (mul_pos hη0 hh0) hgt.le)
      have hl2 : Real.log (1 / (η * h)) = Real.log (1 / η) + Real.log (1 / h) := by
        rw [show 1 / (η * h) = (1 / η) * (1 / h) by ring,
          Real.log_mul (one_div_pos.mpr hη0).ne' (one_div_pos.mpr hh0).ne']
      have hl3 : Real.log (1 / η) < Real.log (1 / h) * η := (div_lt_iff₀ hη0).mp hlogh_big
      have hfu_pos : 0 < -Real.log (-u) := by
        rw [← log_one_div_eq_neg_log]
        exact Real.log_pos (by rw [lt_div_iff₀ hu_pos]; linarith [hu.1])
      dsimp only [f]
      refine inv_anti₀ hfu_pos ?_
      rw [← log_one_div_eq_neg_log]
      linarith
    have hm2 := setIntegral_mono_on
      ((continuousOn_const (c := ((1 + η) * Real.log (1 / h))⁻¹)).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self)
      (hfi.mono_set hsub) measurableSet_Ioo hpt
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by nlinarith [hh0, hη4])] at hm2
    have hlen : -(η * h) - -h = (1 - η) * h := by ring
    rw [hlen, smul_eq_mul] at hm2
    exact hm2.trans hm1
  have hJ_ub : Real.log (1 / h) / h * (∫ u in Ioo (-h) 0, f u) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hub_int (div_nonneg hlogh_pos.le hh0.le)
    refine hm.trans_eq ?_
    rw [div_mul_eq_mul_div, mul_left_comm, mul_inv_cancel₀ hlogh_pos.ne', mul_one,
      div_self hh0.ne']
  have hJ_lb : (1 - η) / (1 + η) ≤ Real.log (1 / h) / h * (∫ u in Ioo (-h) 0, f u) := by
    have hm := mul_le_mul_of_nonneg_left hlb_int (div_nonneg hlogh_pos.le hh0.le)
    refine le_trans ?_ hm
    rw [mul_inv, show Real.log (1 / h) / h * (((1 - η) * h) * ((1 + η)⁻¹ * (Real.log (1 / h))⁻¹)) =
      ((1 - η) / (1 + η)) * ((h * h⁻¹) * (Real.log (1 / h) * (Real.log (1 / h))⁻¹)) by ring,
      mul_inv_cancel₀ hh0.ne', mul_inv_cancel₀ hlogh_pos.ne', mul_one, mul_one]
  have h1m : 1 - ε < (1 - η) / (1 + η) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith [hη0, hηε, hε]
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Sustained logarithmic wall cusp.** As `h → 0⁺`,
`(log(1/h)/h) ∫_{-h}^0 (smoothedWallLogProfile ℓ u)² du → ℓ²`. -/
theorem smoothedWallLogProfile_tendsto_terminal_sq (ℓ : ℝ) :
    Tendsto (fun h : ℝ => Real.log (1 / h) / h *
      ∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
  let J : ℝ → ℝ := fun h => Real.log (1 / h) / h * ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹
  have hJ := tendsto_log_div_mul_integral_inv_neg_log
  have hc : Tendsto (fun h : ℝ => ℓ ^ 2 * (1 - 8 * h) ^ 4) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
    have hcont : Continuous fun h : ℝ => ℓ ^ 2 * (1 - 8 * h) ^ 4 := by fun_prop
    have h0 := (hcont.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [mul_zero, sub_zero, one_pow, mul_one] at h0
  have hlo : Tendsto (fun h : ℝ => ℓ ^ 2 * (1 - 8 * h) ^ 4 * J h) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
    simpa only [mul_one] using hc.mul hJ
  have hhi : Tendsto (fun h : ℝ => ℓ ^ 2 * J h) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
    simpa only [mul_one] using hJ.const_mul (ℓ ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))] with h hh0 hh8
    have hh0' : (0 : ℝ) < h := hh0
    have hh8' : h < 1 / 8 := hh8
    have hlog_nn : 0 ≤ Real.log (1 / h) / h :=
      div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hh0']; linarith)) hh0'.le
    have hfi : IntegrableOn (fun u => (-Real.log (-u))⁻¹) (Ioo (-h) 0) := by
      refine ((criticalHalfLineEnergyDomain_wallLogProfile (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)).sq.integrableOn
        (s := Ioo (-h) 0)).congr_fun (fun u hu => ?_) measurableSet_Ioo
      dsimp only
      rw [wallLogProfile_of_mem (by linarith [hu.1, hh8']) hu.2, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1, hh8'])]
    have hF2i : IntegrableOn (fun u => smoothedWallLogProfile ℓ u ^ 2) (Ioo (-h) 0) :=
      (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ).sq.integrableOn
    have hle_int : (ℓ ^ 2 * (1 - 8 * h) ^ 4) * (∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹) ≤
        ∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hfi.const_mul _) hF2i measurableSet_Ioo fun u hu => ?_
      rw [smoothedWallLogProfile_of_mem (by linarith [hu.1, hh8']) hu.2, mul_pow, mul_pow, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1, hh8']), ← mul_assoc]
      have hpow : (1 - 8 * h) ^ 4 ≤ (1 + 8 * u) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith [hu.1]) 4
      rw [show ((1 + 8 * u) ^ 2) ^ 2 = (1 + 8 * u) ^ 4 by ring]
      have hinv_nn : 0 ≤ (-Real.log (-u))⁻¹ :=
        inv_nonneg.mpr (by linarith [one_le_neg_log (by linarith [hu.2] : 0 < -u) (by linarith [hu.1, hh8'])])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg ℓ)) hinv_nn
    have hm := mul_le_mul_of_nonneg_left hle_int hlog_nn
    dsimp only [J]
    linarith [show Real.log (1 / h) / h * ((ℓ ^ 2 * (1 - 8 * h) ^ 4) *
        ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹) =
      ℓ ^ 2 * (1 - 8 * h) ^ 4 * (Real.log (1 / h) / h *
        ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹) by ring]
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))] with h hh0 hh8
    have hh0' : (0 : ℝ) < h := hh0
    have hh8' : h < 1 / 8 := hh8
    have hlog_nn : 0 ≤ Real.log (1 / h) / h :=
      div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hh0']; linarith)) hh0'.le
    have hfi : IntegrableOn (fun u => (-Real.log (-u))⁻¹) (Ioo (-h) 0) := by
      refine ((criticalHalfLineEnergyDomain_wallLogProfile (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)).sq.integrableOn
        (s := Ioo (-h) 0)).congr_fun (fun u hu => ?_) measurableSet_Ioo
      dsimp only
      rw [wallLogProfile_of_mem (by linarith [hu.1, hh8']) hu.2, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1, hh8'])]
    have hF2i : IntegrableOn (fun u => smoothedWallLogProfile ℓ u ^ 2) (Ioo (-h) 0) :=
      (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ).sq.integrableOn
    have hle_int : ∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2 ≤
        ℓ ^ 2 * ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹ := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hF2i (hfi.const_mul _) measurableSet_Ioo fun u hu => ?_
      rw [smoothedWallLogProfile_of_mem (by linarith [hu.1, hh8']) hu.2, mul_pow, mul_pow, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1, hh8'])]
      have h1 : ((1 + 8 * u) ^ 2) ^ 2 ≤ 1 := by
        have hb : 0 ≤ 1 + 8 * u := by linarith [hu.1, hh8']
        have hu1 : 1 + 8 * u ≤ 1 := by linarith [hu.2]
        have hsq : (1 + 8 * u) ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ((1 + 8 * u) ^ 2)]
      have hinv_nn : 0 ≤ (-Real.log (-u))⁻¹ :=
        inv_nonneg.mpr (by linarith [one_le_neg_log (by linarith [hu.2] : 0 < -u) (by linarith [hu.1, hh8'])])
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right h1 hinv_nn).trans_eq (one_mul _)) (sq_nonneg ℓ)
    have hm := mul_le_mul_of_nonneg_left hle_int hlog_nn
    dsimp only [J]
    linarith [show Real.log (1 / h) / h * (ℓ ^ 2 * ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹) =
      ℓ ^ 2 * (Real.log (1 / h) / h * ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹) by ring]

/-- No positive sequence `h_j ↓ 0` can make the logarithmic wall cusp of `smoothedWallLogProfile ℓ`
vanish when `ℓ ≠ 0`. -/
theorem smoothedWallLogProfile_no_vanishing_cusp_subsequence {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    ¬ ∃ h : ℕ → ℝ, (∀ j, 0 < h j) ∧ Tendsto h atTop (𝓝 0) ∧
      Tendsto (fun j => Real.log (1 / h j) / h j *
        ∫ u in Ioo (-(h j)) 0, smoothedWallLogProfile ℓ u ^ 2) atTop (𝓝 0) := by
  rintro ⟨h, hpos, h0, hvan⟩
  have hnhds : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h h0 (Eventually.of_forall hpos)
  have hlim := (smoothedWallLogProfile_tendsto_terminal_sq ℓ).comp hnhds
  have heq : ℓ ^ 2 = 0 := tendsto_nhds_unique hlim hvan
  exact pow_ne_zero 2 hℓ heq

/-- Exact logarithmic Abelian square mass of `smoothedWallLogProfile ℓ`. -/
theorem smoothedWallLogProfile_tendsto_mul_log_dampedMass (ℓ : ℝ) :
    Tendsto (fun x : ℝ => (x * Real.log x) *
      ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * smoothedWallLogProfile ℓ (-v) ^ 2)
      atTop (𝓝 (ℓ ^ 2 / 2)) :=
  tendsto_mul_log_dampedMass_of_terminal_sq
    (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ).meas
    (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ).sq
    (smoothedWallLogProfile_tendsto_terminal_sq ℓ)

/-- Exact logarithmic vertical-line Laplace square trace of `smoothedWallLogProfile ℓ`. -/
theorem smoothedWallLogProfile_tendsto_mul_log_vertical_laplace_sq (ℓ : ℝ) :
    Tendsto (fun x : ℝ => (x * Real.log x) *
      ∫ y : ℝ, ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) (hardyVerticalLine x y)‖ ^ 2)
      atTop (𝓝 (Real.pi * ℓ ^ 2)) :=
  tendsto_mul_log_vertical_laplace_sq_of_terminal_sq
    (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ)
    (smoothedWallLogProfile_tendsto_terminal_sq ℓ)

/-- Vanishing unscaled mean-square wall trace `h⁻¹ ∫_{-h}^0 F_ℓ(u)² du → 0`. -/
theorem smoothedWallLogProfile_mean_square_wall_trace_zero (ℓ : ℝ) :
    Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2) / h)
      (𝓝[>] 0) (𝓝 0) := by
  have hcusp := smoothedWallLogProfile_tendsto_terminal_sq ℓ
  have hinv_log : Tendsto (fun h : ℝ => (Real.log (1 / h))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hcomp := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)))
    exact hcomp.congr fun h => by simp [one_div]
  have hprod := hcusp.mul hinv_log
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with h hh0 hh2
  have hh0' : (0 : ℝ) < h := hh0
  have hh2' : h < 1 / 2 := hh2
  have hlog : Real.log (1 / h) ≠ 0 :=
    (Real.log_pos (by rw [lt_div_iff₀ hh0']; linarith)).ne'
  rw [show Real.log (1 / h) / h * (∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2) *
      (Real.log (1 / h))⁻¹ =
    ((∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2) / h) *
      (Real.log (1 / h) * (Real.log (1 / h))⁻¹) by ring,
    mul_inv_cancel₀ hlog, mul_one]

/-- Vanishing weighted `L²` increment quotient `h⁻¹ ∫ (F_ℓ(u) - F_ℓ(u + h))² e^{-8u} du → 0`,
matching `criticalState_tendsto_weighted_sq_increment_div`. -/
theorem smoothedWallLogProfile_weighted_sq_increment_div_zero (ℓ : ℝ) :
    Tendsto (fun h : ℝ => (∫ u : ℝ,
      (smoothedWallLogProfile ℓ u - smoothedWallLogProfile ℓ (u + h)) ^ 2 *
        Real.exp (-(8 * u))) / h) (𝓝[>] 0) (𝓝 0) := by
  have hd_full := criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set K₀ := 64 * Real.exp 2 * (ℓ ^ 2 + 1)
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  set δ := min (1 / 16) (Real.exp (-(K₀ / ε)))
  have hδ0 : 0 < δ := lt_min (by norm_num) (Real.exp_pos _)
  have hδ16 : δ ≤ 1 / 16 := min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := by linarith
  have hδ_exp : δ ≤ Real.exp (-(K₀ / ε)) := min_le_right _ _
  have hroot_sq : (wallRootLog δ)⁻¹ ^ 2 ≤ ε / K₀ := by
    rw [inv_pow, wallRootLog_sq hδ0 hδ4]
    have hl : Real.log δ ≤ -(K₀ / ε) := by
      have h1 := Real.log_le_log hδ0 hδ_exp
      rwa [Real.log_exp] at h1
    have hge : K₀ / ε ≤ -Real.log δ := by linarith
    exact (inv_anti₀ (div_pos hK₀ hε) hge).trans_eq (inv_div K₀ ε)
  let χ : ℝ → ℝ := fun u => min (max (2 + 4 / δ * u) 0) 1
  have hχ0 : ∀ u, 0 ≤ χ u := fun _ => le_min (le_max_right _ _) zero_le_one
  have hχ1 : ∀ u, χ u ≤ 1 := fun _ => min_le_right _ _
  have hχ_left : ∀ u, u ≤ -(δ / 2) → χ u = 0 := fun u hu => by
    dsimp only [χ]
    have hm : 4 / δ * u ≤ -2 := by
      have h1 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 4 / δ)
      have he : 4 / δ * -(δ / 2) = -2 := by
        rw [div_eq_mul_inv, show 4 * δ⁻¹ * -(δ / 2) = -2 * (δ * δ⁻¹) by ring,
          mul_inv_cancel₀ hδ0.ne', mul_one]
      linarith
    rw [max_eq_right (by linarith), min_eq_left zero_le_one]
  have hχ_right : ∀ u, -(δ / 4) ≤ u → χ u = 1 := fun u hu => by
    dsimp only [χ]
    have hm : -1 ≤ 4 / δ * u := by
      have h1 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 4 / δ)
      have he : 4 / δ * -(δ / 4) = -1 := by
        rw [div_eq_mul_inv, show 4 * δ⁻¹ * -(δ / 4) = -(δ * δ⁻¹) by ring,
          mul_inv_cancel₀ hδ0.ne']
      linarith
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  have hχ_lip : ∀ u v, |χ u - χ v| ≤ (4 / δ) * |u - v| := fun u v => by
    calc |χ u - χ v|
        ≤ max |max (2 + 4 / δ * u) 0 - max (2 + 4 / δ * v) 0| |(1 : ℝ) - 1| :=
          abs_min_sub_min_le_max _ _ _ _
      _ = |max (2 + 4 / δ * u) 0 - max (2 + 4 / δ * v) 0| := by
          rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      _ ≤ |(2 + 4 / δ * u) - (2 + 4 / δ * v)| := abs_max_sub_max_le_abs _ _ _
      _ = (4 / δ) * |u - v| := by
          rw [show (2 + 4 / δ * u) - (2 + 4 / δ * v) = (4 / δ) * (u - v) by ring,
            abs_mul, abs_of_pos (by positivity)]
  let ψ_near : ℝ → ℝ := fun u => ℓ * (collarSmoothCutoff u * χ u)
  let Λ_near : ℝ := |ℓ| * (16 + 4 / δ)
  have hψ_near_abs : ∀ u, |ψ_near u| ≤ |ℓ| := fun u => by
    dsimp only [ψ_near]
    rw [abs_mul, abs_mul, abs_of_nonneg (collarSmoothCutoff_nonneg u), abs_of_nonneg (hχ0 u)]
    have hp : collarSmoothCutoff u * χ u ≤ 1 := by
      nlinarith [collarSmoothCutoff_nonneg u, collarSmoothCutoff_le_one u, hχ0 u, hχ1 u]
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg ℓ)).trans_eq (mul_one _)
  have hψ_near_lip : ∀ u v, |ψ_near u - ψ_near v| ≤ Λ_near * |u - v| := fun u v => by
    have hdecomp : ψ_near u - ψ_near v =
        ℓ * ((collarSmoothCutoff u - collarSmoothCutoff v) * χ u +
          collarSmoothCutoff v * (χ u - χ v)) := by dsimp only [ψ_near]; ring
    rw [hdecomp, abs_mul]
    have h1 : |(collarSmoothCutoff u - collarSmoothCutoff v) * χ u| ≤ 16 * |u - v| := by
      rw [abs_mul, abs_of_nonneg (hχ0 u)]
      exact (mul_le_mul_of_nonneg_left (hχ1 u) (abs_nonneg _)).trans
        ((mul_one _).le.trans (abs_collarSmoothCutoff_sub_le u v))
    have h2 : |collarSmoothCutoff v * (χ u - χ v)| ≤ (4 / δ) * |u - v| := by
      rw [abs_mul, abs_of_nonneg (collarSmoothCutoff_nonneg v)]
      exact (mul_le_mul_of_nonneg_right (collarSmoothCutoff_le_one v) (abs_nonneg _)).trans
        ((one_mul _).le.trans (hχ_lip u v))
    have htri := (abs_add_le _ _).trans (add_le_add h1 h2)
    calc |ℓ| * |_ + _| ≤ |ℓ| * (16 * |u - v| + (4 / δ) * |u - v|) :=
          mul_le_mul_of_nonneg_left htri (abs_nonneg ℓ)
      _ = Λ_near * |u - v| := by dsimp only [Λ_near]; ring
  let F_near : ℝ → ℝ := fun u => χ u * smoothedWallLogProfile ℓ u
  let F_far : ℝ → ℝ := fun u => (1 - χ u) * smoothedWallLogProfile ℓ u
  have hnear_eq : ∀ u, F_near u = ψ_near u * wallLogProfile δ u := fun u => by
    dsimp only [F_near, ψ_near, smoothedWallLogProfile]
    rcases le_or_gt u (-(δ / 2)) with hle | hgt
    · rw [hχ_left u hle, zero_mul, mul_zero, mul_zero, zero_mul]
    · rcases le_or_gt 0 u with h0 | h0
      · simp only [wallLogProfile_of_nonneg h0, mul_zero]
      · rw [wallLogProfile_of_mem (by linarith) h0, wallLogProfile_of_mem (by linarith) h0]
        ring
  let cl : ℝ → ℝ := fun u => min (max (-u) (δ / 4)) (1 / 8)
  have hcl_lo : ∀ u, δ / 4 ≤ cl u := fun u => le_min (le_max_right _ _) (by linarith)
  have hcl_hi : ∀ u, cl u ≤ 1 / 8 := fun u => min_le_right _ _
  have hcl_lip : ∀ u v, |cl u - cl v| ≤ |u - v| := fun u v => by
    calc |cl u - cl v|
        ≤ max |max (-u) (δ / 4) - max (-v) (δ / 4)| |(1 / 8 : ℝ) - 1 / 8| :=
          abs_min_sub_min_le_max _ _ _ _
      _ = |max (-u) (δ / 4) - max (-v) (δ / 4)| := by
          rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
      _ ≤ |(-u) - (-v)| := abs_max_sub_max_le_abs _ _ _
      _ = |u - v| := by rw [show (-u) - (-v) = -(u - v) by ring, abs_neg]
  let w_tr : ℝ → ℝ := fun u => (wallRootLog (cl u))⁻¹
  have hw_tr_abs : ∀ u, |w_tr u| ≤ 1 := fun u => by
    dsimp only [w_tr]
    have hge1 := one_le_wallRootLog (lt_of_lt_of_le (by positivity) (hcl_lo u))
      ((hcl_hi u).trans (by norm_num))
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hge1))]
    exact inv_le_one_of_one_le₀ hge1
  have hw_tr_lip : ∀ u v, |w_tr u - w_tr v| ≤ (2 / δ) * |u - v| := fun u v => by
    dsimp only [w_tr]
    have he_div : ∀ a : ℝ, a / (2 * (δ / 4)) = (2 / δ) * a := fun a => by
      rw [div_eq_mul_inv, show 2 * (δ / 4) = 2⁻¹ * δ by ring, mul_inv, inv_inv]
      ring
    rcases le_total (cl u) (cl v) with hle | hge
    · have hs : 0 < cl u := lt_of_lt_of_le (by positivity) (hcl_lo u)
      have hmono := inv_wallRootLog_mono hs hle ((hcl_hi v).trans (by norm_num))
      have hsub := inv_wallRootLog_sub_le hs hle ((hcl_hi v).trans (by norm_num))
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hmono)]
      calc (wallRootLog (cl v))⁻¹ - (wallRootLog (cl u))⁻¹
          ≤ (cl v - cl u) / (2 * cl u) := hsub
        _ ≤ (cl v - cl u) / (2 * (δ / 4)) :=
            div_le_div_of_nonneg_left (sub_nonneg.mpr hle) (by positivity)
              (mul_le_mul_of_nonneg_left (hcl_lo u) zero_le_two)
        _ = (2 / δ) * |cl u - cl v| := by
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle), he_div]
        _ ≤ (2 / δ) * |u - v| := mul_le_mul_of_nonneg_left (hcl_lip u v) (by positivity)
    · have hs : 0 < cl v := lt_of_lt_of_le (by positivity) (hcl_lo v)
      have hmono := inv_wallRootLog_mono hs hge ((hcl_hi u).trans (by norm_num))
      have hsub := inv_wallRootLog_sub_le hs hge ((hcl_hi u).trans (by norm_num))
      rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
      calc (wallRootLog (cl u))⁻¹ - (wallRootLog (cl v))⁻¹
          ≤ (cl u - cl v) / (2 * cl v) := hsub
        _ ≤ (cl u - cl v) / (2 * (δ / 4)) :=
            div_le_div_of_nonneg_left (sub_nonneg.mpr hge) (by positivity)
              (mul_le_mul_of_nonneg_left (hcl_lo v) zero_le_two)
        _ = (2 / δ) * |cl u - cl v| := by
            rw [abs_of_nonneg (sub_nonneg.mpr hge), he_div]
        _ ≤ (2 / δ) * |u - v| := mul_le_mul_of_nonneg_left (hcl_lip u v) (by positivity)
  let ψ_far : ℝ → ℝ := fun u => ℓ * ((1 - χ u) * collarSmoothCutoff u)
  have hfar_eq : ∀ u, F_far u = ψ_far u * w_tr u := fun u => by
    dsimp only [F_far, ψ_far, smoothedWallLogProfile, w_tr, cl]
    rcases le_or_gt u (-(1 / 8)) with hle | hgt
    · have hcut0 : collarSmoothCutoff u = 0 := by
        unfold collarSmoothCutoff
        rw [max_eq_right (by linarith), min_eq_left zero_le_one]
        norm_num
      simp only [hcut0, zero_mul, mul_zero]
    · rcases le_or_gt (-(δ / 4)) u with hge | hlt
      · simp only [hχ_right u hge, sub_self, zero_mul, mul_zero]
      · rw [wallLogProfile_of_mem hgt (by linarith),
          max_eq_left (by linarith), min_eq_left (by linarith)]
        ring
  let Λ_far : ℝ := |ℓ| * (16 + 6 / δ)
  have hfar_lip : ∀ u v, |F_far u - F_far v| ≤ Λ_far * |u - v| := fun u v => by
    rw [hfar_eq u, hfar_eq v]
    have hdecomp : ψ_far u * w_tr u - ψ_far v * w_tr v =
        ℓ * (((1 - χ u) * (collarSmoothCutoff u - collarSmoothCutoff v) -
          (χ u - χ v) * collarSmoothCutoff v) * w_tr u +
            ((1 - χ v) * collarSmoothCutoff v) * (w_tr u - w_tr v)) := by
      dsimp only [ψ_far]; ring
    rw [hdecomp, abs_mul]
    have h1mχ : ∀ t, |1 - χ t| ≤ 1 := fun t => by
      rw [abs_of_nonneg (sub_nonneg.mpr (hχ1 t))]; linarith [hχ0 t]
    have hp1 : |((1 - χ u) * (collarSmoothCutoff u - collarSmoothCutoff v) -
        (χ u - χ v) * collarSmoothCutoff v) * w_tr u| ≤ (16 + 4 / δ) * |u - v| := by
      rw [abs_mul]
      have ha1 : |(1 - χ u) * (collarSmoothCutoff u - collarSmoothCutoff v)| ≤ 16 * |u - v| := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (h1mχ u) (abs_nonneg _)).trans
          ((one_mul _).le.trans (abs_collarSmoothCutoff_sub_le u v))
      have ha2 : |(χ u - χ v) * collarSmoothCutoff v| ≤ (4 / δ) * |u - v| := by
        rw [abs_mul, abs_of_nonneg (collarSmoothCutoff_nonneg v)]
        exact (mul_le_mul_of_nonneg_left (collarSmoothCutoff_le_one v) (abs_nonneg _)).trans
          ((mul_one _).le.trans (hχ_lip u v))
      have hsub := (abs_sub _ _).trans (add_le_add ha1 ha2)
      calc |_ - _| * |w_tr u|
          ≤ ((16 + 4 / δ) * |u - v|) * 1 :=
            mul_le_mul (by linarith [hsub]) (hw_tr_abs u) (abs_nonneg _) (by positivity)
        _ = (16 + 4 / δ) * |u - v| := mul_one _
    have hp2 : |((1 - χ v) * collarSmoothCutoff v) * (w_tr u - w_tr v)| ≤ (2 / δ) * |u - v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (collarSmoothCutoff_nonneg v)]
      have hb : |1 - χ v| * collarSmoothCutoff v ≤ 1 := by
        nlinarith [h1mχ v, abs_nonneg (1 - χ v), collarSmoothCutoff_nonneg v,
          collarSmoothCutoff_le_one v]
      exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans
        ((one_mul _).le.trans (hw_tr_lip u v))
    have htri := (abs_add_le _ _).trans (add_le_add hp1 hp2)
    calc |ℓ| * |_ + _|
        ≤ |ℓ| * ((16 + 4 / δ) * |u - v| + (2 / δ) * |u - v|) :=
          mul_le_mul_of_nonneg_left htri (abs_nonneg ℓ)
      _ = Λ_far * |u - v| := by dsimp only [Λ_far]; ring
  set C_quad : ℝ := Real.exp 2 * (4 * Λ_near ^ 2 + 2 * Λ_far ^ 2)
  have hCq_nn : 0 ≤ C_quad := by dsimp only [C_quad]; positivity
  set h_max := min (1 / 16) (ε / (4 * (C_quad + 1)))
  have hh_max_pos : 0 < h_max := lt_min (by norm_num) (by positivity)
  refine ⟨h_max, hh_max_pos, fun h (hh0 : 0 < h) hh_lt => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hh0] at hh_lt
  have hh16 : h < 1 / 16 := lt_of_lt_of_le hh_lt (min_le_left _ _)
  have hh_small : h < ε / (4 * (C_quad + 1)) := lt_of_lt_of_le hh_lt (min_le_right _ _)
  have hwd_int : Integrable fun u => (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 := by
    have hdδ := criticalHalfLineEnergyDomain_wallLogProfile hδ4
    exact integrable_sq_of_memLp (hdδ.memLp_real.sub (memLp_two_shift hdδ.memLp_real h))
  have hwd_bound : ∫ u, (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 ≤
      2 * (wallRootLog δ)⁻¹ ^ 2 * h := by
    refine integral_sq_increment_le_of_antitone_collar (measurable_wallLogProfile δ)
      (criticalHalfLineEnergyDomain_wallLogProfile hδ4).integrable
      (wallLogProfile_nonneg δ)
      (fun u => ?_)
      (fun _ hu => wallLogProfile_of_le hu)
      (fun _ hu => wallLogProfile_of_nonneg hu)
      (fun u v hu huv hv => ?_) hh0
    · by_cases hm : -δ < u ∧ u < 0
      · rw [wallLogProfile_of_mem hm.1 hm.2]
        exact inv_wallRootLog_mono (by linarith [hm.2]) (by linarith [hm.1]) hδ4
      · rw [wallLogProfile, if_neg hm]
        exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    · rw [wallLogProfile_of_mem hu (lt_of_le_of_lt huv hv),
        wallLogProfile_of_mem (lt_of_lt_of_le hu huv) hv]
      exact inv_wallRootLog_mono (by linarith [hv]) (by linarith [huv]) (by linarith [hu, hδ4])
  let S_supp : Set ℝ := Icc (-(1 / 4 : ℝ)) 0
  have hind_int : Integrable (fun u : ℝ => S_supp.indicator (fun _ : ℝ => C_quad * h ^ 2) u) :=
    ((continuousOn_const (c := C_quad * h ^ 2)).integrableOn_Icc).integrable_indicator
      measurableSet_Icc
  have hinc_int : Integrable fun u : ℝ =>
      (smoothedWallLogProfile ℓ u - smoothedWallLogProfile ℓ (u + h)) ^ 2 *
        Real.exp (-(8 * u)) :=
    (criticalHalfLineEnergyDomain_increment hd_full hh0.le).exponential.congr
      (Eventually.of_forall fun u => by ring)
  have hpt : ∀ u : ℝ,
      (smoothedWallLogProfile ℓ u - smoothedWallLogProfile ℓ (u + h)) ^ 2 *
        Real.exp (-(8 * u)) ≤
      (4 * Real.exp 2 * ℓ ^ 2) * (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 +
        S_supp.indicator (fun _ => C_quad * h ^ 2) u := fun u => by
    by_cases hu_mem : u ∈ S_supp
    · rw [indicator_of_mem hu_mem]
      have hexp_le : Real.exp (-(8 * u)) ≤ Real.exp 2 :=
        Real.exp_le_exp.mpr (by linarith [hu_mem.1])
      have hsplit_F : ∀ t, smoothedWallLogProfile ℓ t = F_near t + F_far t := fun t => by
        dsimp only [F_near, F_far]; ring
      rw [hsplit_F u, hsplit_F (u + h)]
      have hq1 : (F_near u + F_far u - (F_near (u + h) + F_far (u + h))) ^ 2 ≤
          2 * (F_near u - F_near (u + h)) ^ 2 + 2 * (F_far u - F_far (u + h)) ^ 2 := by
        nlinarith only [sq_nonneg ((F_near u - F_near (u + h)) - (F_far u - F_far (u + h)))]
      have hfar_sq : (F_far u - F_far (u + h)) ^ 2 ≤ Λ_far ^ 2 * h ^ 2 := by
        have hl := hfar_lip u (u + h)
        rw [show u - (u + h) = -h by ring, abs_neg, abs_of_pos hh0] at hl
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hl 2
        rw [sq_abs] at hsq
        linarith [show (Λ_far * h) ^ 2 = Λ_far ^ 2 * h ^ 2 by ring]
      have hnear_sq : (F_near u - F_near (u + h)) ^ 2 ≤
          2 * ℓ ^ 2 * (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 +
            2 * Λ_near ^ 2 * h ^ 2 := by
        rw [hnear_eq u, hnear_eq (u + h)]
        have hid : ψ_near u * wallLogProfile δ u - ψ_near (u + h) * wallLogProfile δ (u + h) =
            ψ_near u * (wallLogProfile δ u - wallLogProfile δ (u + h)) +
              (ψ_near u - ψ_near (u + h)) * wallLogProfile δ (u + h) := by ring
        rw [hid]
        have ha1 : (ψ_near u * (wallLogProfile δ u - wallLogProfile δ (u + h))) ^ 2 ≤
            ℓ ^ 2 * (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 := by
          rw [mul_pow]
          have hsq := pow_le_pow_left₀ (abs_nonneg _) (hψ_near_abs u) 2
          rw [sq_abs, sq_abs] at hsq
          exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        have ha2 : ((ψ_near u - ψ_near (u + h)) * wallLogProfile δ (u + h)) ^ 2 ≤
            Λ_near ^ 2 * h ^ 2 := by
          rw [mul_pow]
          have hl := hψ_near_lip u (u + h)
          rw [show u - (u + h) = -h by ring, abs_neg, abs_of_pos hh0] at hl
          have hsq1 := pow_le_pow_left₀ (abs_nonneg _) hl 2
          rw [sq_abs] at hsq1
          have hw1 : wallLogProfile δ (u + h) ^ 2 ≤ 1 := by
            have := pow_le_pow_left₀ (wallLogProfile_nonneg δ (u + h))
              (wallLogProfile_le_one hδ4 (u + h)) 2
            linarith
          calc (ψ_near u - ψ_near (u + h)) ^ 2 * wallLogProfile δ (u + h) ^ 2
              ≤ (Λ_near * h) ^ 2 * 1 :=
                mul_le_mul hsq1 hw1 (sq_nonneg _) (sq_nonneg _)
            _ = Λ_near ^ 2 * h ^ 2 := by ring
        nlinarith only [sq_nonneg (ψ_near u * (wallLogProfile δ u - wallLogProfile δ (u + h)) -
          (ψ_near u - ψ_near (u + h)) * wallLogProfile δ (u + h)), ha1, ha2]
      have htot_sq : (F_near u + F_far u - (F_near (u + h) + F_far (u + h))) ^ 2 ≤
          4 * ℓ ^ 2 * (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 +
            (4 * Λ_near ^ 2 + 2 * Λ_far ^ 2) * h ^ 2 := by linarith
      have hm1 := mul_le_mul htot_sq hexp_le (Real.exp_pos _).le (by positivity)
      dsimp only [C_quad]
      linarith
    · rw [indicator_of_notMem hu_mem]
      rcases lt_or_ge u (-(1 / 4 : ℝ)) with hlt | hge
      · rw [smoothedWallLogProfile_of_le (by linarith),
          smoothedWallLogProfile_of_le (by linarith), sub_self]
        norm_num
        positivity
      · have hgt0 : 0 < u := not_le.mp fun hle0 => hu_mem ⟨hge, hle0⟩
        rw [smoothedWallLogProfile_of_nonneg hgt0.le,
          smoothedWallLogProfile_of_nonneg (by linarith), sub_self]
        norm_num
        positivity
  have hint_le : (∫ u : ℝ,
      (smoothedWallLogProfile ℓ u - smoothedWallLogProfile ℓ (u + h)) ^ 2 *
        Real.exp (-(8 * u))) ≤
      (4 * Real.exp 2 * ℓ ^ 2) * (2 * (wallRootLog δ)⁻¹ ^ 2 * h) + (1 / 4) * (C_quad * h ^ 2) := by
    have hm : (∫ u : ℝ,
        (smoothedWallLogProfile ℓ u - smoothedWallLogProfile ℓ (u + h)) ^ 2 *
          Real.exp (-(8 * u))) ≤
        ∫ u : ℝ, ((4 * Real.exp 2 * ℓ ^ 2) * (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 +
          S_supp.indicator (fun _ => C_quad * h ^ 2) u) :=
      integral_mono hinc_int ((hwd_int.const_mul (4 * Real.exp 2 * ℓ ^ 2)).add hind_int) hpt
    rw [integral_add (hwd_int.const_mul _) hind_int, integral_const_mul,
      integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by norm_num), sub_neg_eq_add, zero_add, smul_eq_mul] at hm
    have hm2 := mul_le_mul_of_nonneg_left hwd_bound (by positivity : (0 : ℝ) ≤ 4 * Real.exp 2 * ℓ ^ 2)
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg
    (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hh0.le)]
  have hdiv := div_le_div_of_nonneg_right hint_le hh0.le
  have hsimp : ((4 * Real.exp 2 * ℓ ^ 2) * (2 * (wallRootLog δ)⁻¹ ^ 2 * h) +
      (1 / 4) * (C_quad * h ^ 2)) / h =
      8 * Real.exp 2 * ℓ ^ 2 * (wallRootLog δ)⁻¹ ^ 2 + C_quad * h / 4 := by
    rw [show (4 * Real.exp 2 * ℓ ^ 2) * (2 * (wallRootLog δ)⁻¹ ^ 2 * h) +
        (1 / 4) * (C_quad * h ^ 2) =
      (8 * Real.exp 2 * ℓ ^ 2 * (wallRootLog δ)⁻¹ ^ 2 + C_quad * h / 4) * h by ring,
      mul_div_cancel_right₀ _ hh0.ne']
  rw [hsimp] at hdiv
  have hb1 : 8 * Real.exp 2 * ℓ ^ 2 * (wallRootLog δ)⁻¹ ^ 2 ≤ ε / 8 := by
    have hm1 := mul_le_mul_of_nonneg_left hroot_sq (by positivity : (0 : ℝ) ≤ 8 * Real.exp 2 * ℓ ^ 2)
    have hm2 : 8 * Real.exp 2 * ℓ ^ 2 * (ε / K₀) ≤ 8 * Real.exp 2 * (ℓ ^ 2 + 1) * (ε / K₀) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)
    have heq : 8 * Real.exp 2 * (ℓ ^ 2 + 1) * (ε / K₀) = ε / 8 := by
      set Z := Real.exp 2 * (ℓ ^ 2 + 1)
      have hZ : Z ≠ 0 := by positivity
      rw [div_eq_mul_inv, show K₀ = 64 * Z by dsimp only [K₀, Z]; ring, mul_inv,
        show 8 * Real.exp 2 * (ℓ ^ 2 + 1) * (ε * (64⁻¹ * Z⁻¹)) =
          (ε / 8) * (Z * Z⁻¹) by dsimp only [Z]; ring,
        mul_inv_cancel₀ hZ, mul_one]
    linarith
  have hb2 : C_quad * h / 4 ≤ ε / 16 := by
    have hm := mul_le_mul_of_nonneg_left hh_small.le hCq_nn
    have hle : C_quad * (ε / (4 * (C_quad + 1))) ≤ (C_quad + 1) * (ε / (4 * (C_quad + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have heq : (C_quad + 1) * (ε / (4 * (C_quad + 1))) = ε / 4 := by
      set Z := C_quad + 1
      have hZ : Z ≠ 0 := by linarith
      rw [div_eq_mul_inv, mul_inv,
        show Z * (ε * (4⁻¹ * Z⁻¹)) = (ε / 4) * (Z * Z⁻¹) by ring,
        mul_inv_cancel₀ hZ, mul_one]
    linarith
  linarith

/-! ### Exact Laplace integration by parts, uniform half-plane bound, and imaginary-axis limit -/

private theorem tendsto_sqrt_atTop : Tendsto Real.sqrt atTop atTop :=
  tendsto_atTop.mpr fun b => (eventually_ge_atTop (max b 0 ^ 2)).mono fun _ hx =>
    (le_max_left b 0).trans ((Real.sqrt_sq (le_max_right b 0)).symm.le.trans (Real.sqrt_le_sqrt hx))

private theorem intervalIntegrable_ofReal {a b : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume a b :=
  ⟨hf.1.ofReal, hf.2.ofReal⟩

private theorem measurable_wallRootLog : Measurable wallRootLog :=
  Real.continuous_sqrt.measurable.comp
    (Real.measurable_log.comp (measurable_const.div measurable_id))

private def invWallRootLogZero (v : ℝ) : ℝ := if v ≤ 0 then 0 else (wallRootLog v)⁻¹

private theorem measurable_invWallRootLogZero : Measurable invWallRootLogZero :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    measurable_wallRootLog.inv

private theorem tendsto_inv_wallRootLog_nhdsGT_zero :
    Tendsto (fun v : ℝ => (wallRootLog v)⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hcomp := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
    (tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))))
  exact hcomp.congr fun v => by simp [wallRootLog, one_div]

private theorem continuousOn_invWallRootLogZero :
    ContinuousOn invWallRootLogZero (Icc 0 (1 / 4)) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · rw [ContinuousWithinAt, show invWallRootLogZero 0 = 0 by simp [invWallRootLogZero]]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp
      tendsto_inv_wallRootLog_nhdsGT_zero ε hε
    refine ⟨δ, hδ0, fun v hv hdist => ?_⟩
    rcases eq_or_lt_of_le hv.1 with rfl | hv0
    · simp [invWallRootLogZero, hε]
    · have hd := hδ hv0 hdist
      simpa only [invWallRootLogZero, if_neg (not_le.mpr hv0)] using hd
  · have hpos_log : 0 < Real.log (1 / x) :=
      Real.log_pos (by rw [lt_div_iff₀ hx0]; linarith [hx.2])
    have hc : ContinuousAt (fun v : ℝ => (Real.sqrt (Real.log (1 / v)))⁻¹) x :=
      (Real.continuous_sqrt.continuousAt.comp
        ((Real.continuousAt_log (one_div_pos.mpr hx0).ne').comp
          (continuousAt_const.div continuousAt_id hx0.ne'))).inv₀
        (Real.sqrt_pos.mpr hpos_log).ne'
    have heq : invWallRootLogZero =ᶠ[𝓝 x] fun v : ℝ => (Real.sqrt (Real.log (1 / v)))⁻¹ := by
      filter_upwards [Ioi_mem_nhds hx0] with v (hv : 0 < v)
      simp [invWallRootLogZero, not_le.mpr hv, wallRootLog]
    exact (hc.congr heq.symm).continuousWithinAt

private theorem hasDerivAt_inv_wallRootLog {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4) :
    HasDerivAt (fun t : ℝ => (wallRootLog t)⁻¹) ((2 * v * wallRootLog v ^ 3)⁻¹) v := by
  have hw_pos : 0 < wallRootLog v := lt_of_lt_of_le zero_lt_one (one_le_wallRootLog hv0 hv4)
  refine ((hasDerivAt_wallRootLog hv0 hv4).inv hw_pos.ne').congr_deriv ?_
  have hw_ne := hw_pos.ne'
  rw [neg_neg, div_div, mul_inv]
  have he : (wallRootLog v)⁻¹ / (2 * v * wallRootLog v ^ 2) =
      (2 * v)⁻¹ * (wallRootLog v ^ 3)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, ← inv_pow, ← inv_pow,
      show (wallRootLog v)⁻¹ * ((2 * v)⁻¹ * ((wallRootLog v)⁻¹) ^ 2) =
        (2 * v)⁻¹ * ((wallRootLog v)⁻¹ ^ 3) by ring]
  exact he

private theorem hasDerivAt_invWallRootLogZero {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 1 / 4) :
    HasDerivAt invWallRootLogZero ((2 * v * wallRootLog v ^ 3)⁻¹) v := by
  refine (hasDerivAt_inv_wallRootLog hv0 hv4).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hv0] with t (ht : 0 < t)
  simp [invWallRootLogZero, not_le.mpr ht]

private theorem integrableOn_inv_two_mul_wallRootLog_cube {b : ℝ} (_ : 0 < b) (hb4 : b ≤ 1 / 4) :
    IntegrableOn (fun v : ℝ => (2 * v * wallRootLog v ^ 3)⁻¹) (Ioc 0 b) :=
  intervalIntegral.integrableOn_deriv_of_nonneg
    (continuousOn_invWallRootLogZero.mono (Icc_subset_Icc le_rfl hb4))
    (fun _ hv => hasDerivAt_invWallRootLogZero hv.1 (hv.2.le.trans hb4))
    (fun _ hv => inv_nonneg.mpr (mul_nonneg (mul_nonneg zero_le_two hv.1.le)
      (pow_nonneg (zero_le_one.trans (one_le_wallRootLog hv.1 (hv.2.le.trans hb4))) 3)))

private theorem intervalIntegrable_inv_two_mul_wallRootLog_cube {b : ℝ} (hb0 : 0 < b)
    (hb4 : b ≤ 1 / 4) :
    IntervalIntegrable (fun v : ℝ => (2 * v * wallRootLog v ^ 3)⁻¹) volume 0 b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le).mpr
    (integrableOn_inv_two_mul_wallRootLog_cube hb0 hb4)

private theorem intervalIntegral_inv_two_mul_wallRootLog_cube {b : ℝ} (hb0 : 0 < b)
    (hb4 : b ≤ 1 / 4) :
    (∫ v in (0 : ℝ)..b, (2 * v * wallRootLog v ^ 3)⁻¹) = (wallRootLog b)⁻¹ := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb0.le
    (continuousOn_invWallRootLogZero.mono (Icc_subset_Icc le_rfl hb4))
    (fun v hv => hasDerivAt_invWallRootLogZero hv.1 (hv.2.le.trans hb4))
    (intervalIntegrable_inv_two_mul_wallRootLog_cube hb0 hb4)
  simpa [invWallRootLogZero, not_le.mpr hb0] using hftc

private def reflectedCusp (v : ℝ) : ℝ :=
  if 0 < v ∧ v < 1 / 8 then (1 - 8 * v) ^ 2 * (wallRootLog v)⁻¹ else 0

private def cuspMainDeriv (v : ℝ) : ℝ :=
  (1 - 8 * v) ^ 2 * (2 * v * wallRootLog v ^ 3)⁻¹

private theorem measurable_cuspMainDeriv : Measurable cuspMainDeriv :=
  ((measurable_const.sub (measurable_const.mul measurable_id)).pow_const 2).mul
    (((measurable_const.mul measurable_id).mul (measurable_wallRootLog.pow_const 3)).inv)

private theorem intervalIntegrable_cuspMainDeriv_zero {b : ℝ} (hb0 : 0 < b) (hb8 : b ≤ 1 / 8) :
    IntervalIntegrable cuspMainDeriv volume 0 b := by
  have hb4 : b ≤ 1 / 4 := hb8.trans (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le]
  refine (integrableOn_inv_two_mul_wallRootLog_cube hb0 hb4).mono'
    measurable_cuspMainDeriv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hpos : 0 ≤ (2 * v * wallRootLog v ^ 3)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (mul_nonneg zero_le_two hv.1.le)
      (pow_nonneg (zero_le_one.trans (one_le_wallRootLog hv.1 (hv.2.trans hb4))) 3))
  dsimp only [cuspMainDeriv]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hpos)]
  have h1 : (1 - 8 * v) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2, hb8]
  exact (mul_le_mul_of_nonneg_right h1 hpos).trans_eq (one_mul _)

private def cuspSubDeriv (v : ℝ) : ℝ :=
  16 * (1 - 8 * v) * invWallRootLogZero v

private theorem smoothedWallLogProfile_eq_reflectedCusp (ℓ u : ℝ) :
    smoothedWallLogProfile ℓ u = ℓ * reflectedCusp (-u) := by
  by_cases hm : -(1 / 8) < u ∧ u < 0
  · rw [smoothedWallLogProfile_of_mem hm.1 hm.2]
    dsimp only [reflectedCusp]
    rw [if_pos ⟨by linarith [hm.2], by linarith [hm.1]⟩]
    ring
  · have hm' : ¬ (0 < -u ∧ -u < 1 / 8) := fun h => hm ⟨by linarith [h.2], by linarith [h.1]⟩
    dsimp only [reflectedCusp]
    rw [if_neg hm', mul_zero]
    rcases le_or_gt u (-(1 / 8)) with hle | hgt
    · exact smoothedWallLogProfile_of_le hle
    · exact smoothedWallLogProfile_of_nonneg (not_lt.mp fun hlt => hm ⟨hgt, hlt⟩)

private theorem laplace_smoothedWallLogProfile_eq_intervalIntegral (ℓ : ℝ) (w : ℂ) :
    negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w =
      (ℓ : ℂ) * ∫ v in (0 : ℝ)..(1 / 8),
        Complex.exp (-(w * (v : ℂ))) * (reflectedCusp v : ℂ) := by
  unfold negativeHalfLineLaplace
  rw [← integral_neg_eq_self
    (fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx (smoothedWallLogProfile ℓ) u) volume]
  have heq : (fun v : ℝ => Complex.exp (w * ((-v : ℝ) : ℂ)) * cx (smoothedWallLogProfile ℓ) (-v)) =
      fun v : ℝ => (ℓ : ℂ) *
        (Ioc (0 : ℝ) (1 / 8)).indicator
          (fun t => Complex.exp (-(w * (t : ℂ))) * (reflectedCusp t : ℂ)) v := by
    funext v
    dsimp only [cx]
    rw [smoothedWallLogProfile_eq_reflectedCusp, neg_neg, Complex.ofReal_mul, Complex.ofReal_neg,
      mul_neg]
    by_cases hv : v ∈ Ioc (0 : ℝ) (1 / 8)
    · rw [indicator_of_mem hv]; ring
    · rw [indicator_of_notMem hv]
      have hr0 : reflectedCusp v = 0 := by
        dsimp only [reflectedCusp]
        exact if_neg fun h => hv ⟨h.1, h.2.le⟩
      simp only [hr0, Complex.ofReal_zero, mul_zero]
  rw [show (∫ x : ℝ, Complex.exp (w * ((-x : ℝ) : ℂ)) * cx (smoothedWallLogProfile ℓ) (-x)) = _ from
      congrArg (fun f : ℝ → ℂ => ∫ x, f x) heq,
    integral_const_mul, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 8)]

private theorem hasDerivAt_cexp_neg_mul (w : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(w * (t : ℂ))))
      (-w * Complex.exp (-(w * (x : ℂ)))) x := by
  have hlin : HasDerivAt (fun t : ℝ => -(w * (t : ℂ))) (-w) x := by
    have h1 := ((hasDerivAt_id x).ofReal_comp.const_mul w).neg
    exact h1.congr_deriv (by simp)
  exact hlin.cexp.congr_deriv (mul_comm _ _)

private theorem ibp_cexp_neg_mul_real {a b : ℝ} (hab : a ≤ b) {g g' : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_deriv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg'_int : IntervalIntegrable g' volume a b) (w : ℂ) :
    w * (∫ x in a..b, Complex.exp (-(w * (x : ℂ))) * (g x : ℂ)) =
      Complex.exp (-(w * (a : ℂ))) * (g a : ℂ) -
        Complex.exp (-(w * (b : ℂ))) * (g b : ℂ) +
      ∫ x in a..b, Complex.exp (-(w * (x : ℂ))) * (g' x : ℂ) := by
  let u : ℝ → ℂ := fun x => (g x : ℂ)
  let u' : ℝ → ℂ := fun x => (g' x : ℂ)
  let v : ℝ → ℂ := fun x => Complex.exp (-(w * (x : ℂ)))
  let v' : ℝ → ℂ := fun x => -w * Complex.exp (-(w * (x : ℂ)))
  have hu : ContinuousOn u (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn hg_cont
  have hv : ContinuousOn v (uIcc a b) := (by fun_prop : Continuous v).continuousOn
  have hu' : IntervalIntegrable u' volume a b :=
    intervalIntegrable_ofReal hg'_int
  have hv' : IntervalIntegrable v' volume a b :=
    (by fun_prop : Continuous v').intervalIntegrable a b
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv
    (by rw [min_eq_left hab, max_eq_right hab]; exact fun x hx => (hg_deriv x hx).ofReal_comp)
    (fun x _ => hasDerivAt_cexp_neg_mul w x) hu' hv'
  have hLHS : (∫ x in a..b, u x * v' x) =
      -w * ∫ x in a..b, Complex.exp (-(w * (x : ℂ))) * (g x : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by dsimp only [u, v']; ring
  have hRHS : (∫ x in a..b, u' x * v x) =
      ∫ x in a..b, Complex.exp (-(w * (x : ℂ))) * (g' x : ℂ) :=
    intervalIntegral.integral_congr fun x _ => by dsimp only [u', v]; ring
  rw [hLHS, hRHS] at hibp
  dsimp only [u, v] at hibp
  linear_combination -hibp

private theorem mul_laplace_smoothedWallLogProfile_eq (ℓ : ℝ) (w : ℂ) :
    w * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w =
      (ℓ : ℂ) * ((∫ v in (0 : ℝ)..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) -
        ∫ v in (0 : ℝ)..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ)) := by
  have hab : (0 : ℝ) ≤ 1 / 8 := by norm_num
  have href_eq : EqOn reflectedCusp (fun v => (1 - 8 * v) ^ 2 * invWallRootLogZero v)
      (Icc 0 (1 / 8)) := fun v hv => by
    rcases eq_or_lt_of_le hv.1 with rfl | hv0
    · simp [reflectedCusp, invWallRootLogZero]
    · rcases eq_or_lt_of_le hv.2 with rfl | hv8
      · simp [reflectedCusp]
      · unfold reflectedCusp invWallRootLogZero
        rw [if_pos ⟨hv0, hv8⟩, if_neg (not_le.mpr hv0)]
  have hg_cont : ContinuousOn reflectedCusp (Icc 0 (1 / 8)) :=
    (((by fun_prop : Continuous fun v : ℝ => (1 - 8 * v) ^ 2).continuousOn).mul
      (continuousOn_invWallRootLogZero.mono (Icc_subset_Icc le_rfl (by norm_num)))).congr href_eq
  have hg_deriv : ∀ v ∈ Ioo (0 : ℝ) (1 / 8),
      HasDerivAt reflectedCusp (cuspMainDeriv v - cuspSubDeriv v) v := fun v hv => by
    have hd1 : HasDerivAt (fun t : ℝ => (1 - 8 * t) ^ 2) (-16 * (1 - 8 * v)) v := by
      have hlin : HasDerivAt (fun t : ℝ => 1 - 8 * t) (-8) v :=
        ((hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).const_mul (8 : ℝ))).congr_deriv
          (by ring)
      exact (hlin.pow 2).congr_deriv (by ring)
    have hd2 := hasDerivAt_inv_wallRootLog hv.1 (by linarith [hv.2])
    have hprod : HasDerivAt (fun t : ℝ => (1 - 8 * t) ^ 2 * (wallRootLog t)⁻¹)
        (cuspMainDeriv v - cuspSubDeriv v) v := (hd1.mul hd2).congr_deriv (by
      dsimp only [cuspMainDeriv, cuspSubDeriv, invWallRootLogZero]
      rw [if_neg (not_le.mpr hv.1)]
      ring)
    refine hprod.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with t ht
    rw [reflectedCusp, if_pos ⟨ht.1, ht.2⟩]
  have hmain_int : IntervalIntegrable cuspMainDeriv volume 0 (1 / 8) :=
    intervalIntegrable_cuspMainDeriv_zero (by norm_num) le_rfl
  have hsub_cont : ContinuousOn cuspSubDeriv (Icc 0 (1 / 8)) :=
    ((by fun_prop : Continuous fun v : ℝ => 16 * (1 - 8 * v)).continuousOn).mul
      (continuousOn_invWallRootLogZero.mono (Icc_subset_Icc le_rfl (by norm_num)))
  have hsub_int : IntervalIntegrable cuspSubDeriv volume 0 (1 / 8) :=
    hsub_cont.intervalIntegrable_of_Icc hab
  rw [laplace_smoothedWallLogProfile_eq_intervalIntegral, ← mul_assoc, mul_comm w (ℓ : ℂ), mul_assoc,
    ibp_cexp_neg_mul_real hab hg_cont hg_deriv (hmain_int.sub hsub_int) w]
  have hr0 : reflectedCusp 0 = 0 := by simp [reflectedCusp]
  have hr8 : reflectedCusp (1 / 8) = 0 := by simp [reflectedCusp]
  have hint_sub : (∫ v in (0 : ℝ)..(1 / 8),
      Complex.exp (-(w * (v : ℂ))) * ((cuspMainDeriv v - cuspSubDeriv v : ℝ) : ℂ)) =
      (∫ v in (0 : ℝ)..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) -
        ∫ v in (0 : ℝ)..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ) := by
    have hi1 : IntervalIntegrable
        (fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) volume 0 (1 / 8) :=
      (intervalIntegrable_ofReal hmain_int).continuousOn_mul
        (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(w * (v : ℂ)))).continuousOn
    have hi2 : IntervalIntegrable
        (fun v => Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ)) volume 0 (1 / 8) :=
      (intervalIntegrable_ofReal hsub_int).continuousOn_mul
        (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(w * (v : ℂ)))).continuousOn
    rw [← intervalIntegral.integral_sub hi1 hi2]
    exact intervalIntegral.integral_congr fun v _ => by push_cast; ring
  simp only [hr0, hr8, Complex.ofReal_zero, mul_zero, sub_zero, zero_add, hint_sub]

private theorem norm_cexp_neg_mul_le_three {w : ℂ} (hw : -5 ≤ w.re) {v : ℝ}
    (hv0 : 0 ≤ v) (hv8 : v ≤ 1 / 8) :
    ‖Complex.exp (-(w * (v : ℂ)))‖ ≤ 3 := by
  rw [Complex.norm_exp]
  have hre : (-(w * (v : ℂ))).re = -w.re * v := by simp [Complex.mul_re]
  rw [hre]
  have h1 : -w.re * v ≤ 1 := by nlinarith
  exact (Real.exp_le_exp.mpr h1).trans (Real.exp_one_lt_d9.le.trans (by norm_num))

private theorem norm_integral_cuspSubDeriv_le {w : ℂ} (hw : -5 ≤ w.re) (hne : w ≠ 0) :
    ‖∫ v in (0 : ℝ)..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ)‖ ≤
      96 / ‖w‖ := by
  have hab : (0 : ℝ) ≤ 1 / 8 := by norm_num
  let g' : ℝ → ℝ := fun v =>
    -128 * invWallRootLogZero v + 16 * (1 - 8 * v) * (2 * v * wallRootLog v ^ 3)⁻¹
  have hg_cont : ContinuousOn cuspSubDeriv (Icc 0 (1 / 8)) :=
    ((by fun_prop : Continuous fun v : ℝ => 16 * (1 - 8 * v)).continuousOn).mul
      (continuousOn_invWallRootLogZero.mono (Icc_subset_Icc le_rfl (by norm_num)))
  have hg_deriv : ∀ v ∈ Ioo (0 : ℝ) (1 / 8), HasDerivAt cuspSubDeriv (g' v) v := fun v hv => by
    have hd1 : HasDerivAt (fun t : ℝ => 16 * (1 - 8 * t)) (-128) v := by
      have hlin : HasDerivAt (fun t : ℝ => 1 - 8 * t) (-8) v :=
        ((hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).const_mul (8 : ℝ))).congr_deriv
          (by ring)
      exact (hlin.const_mul 16).congr_deriv (by ring)
    have hd2 := hasDerivAt_invWallRootLogZero hv.1 (by linarith [hv.2])
    exact hd1.mul hd2
  let B : ℝ → ℝ := fun v => 128 + 16 * (2 * v * wallRootLog v ^ 3)⁻¹
  have hB_int : IntervalIntegrable B volume 0 (1 / 8) :=
    (intervalIntegrable_const (c := (128 : ℝ))).add
      ((intervalIntegrable_inv_two_mul_wallRootLog_cube (b := 1 / 8) (by norm_num) (by norm_num)).const_mul 16)
  have hg'_bound : ∀ v ∈ Ioc (0 : ℝ) (1 / 8), ‖g' v‖ ≤ B v := fun v hv => by
    have hpos : 0 ≤ (2 * v * wallRootLog v ^ 3)⁻¹ :=
      inv_nonneg.mpr (mul_nonneg (mul_nonneg zero_le_two hv.1.le)
        (pow_nonneg (zero_le_one.trans (one_le_wallRootLog hv.1 (by linarith [hv.2]))) 3))
    have hw1 : |invWallRootLogZero v| ≤ 1 := by
      rw [invWallRootLogZero, if_neg (not_le.mpr hv.1),
        abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans (one_le_wallRootLog hv.1 (by linarith [hv.2]))))]
      exact inv_le_one_of_one_le₀ (one_le_wallRootLog hv.1 (by linarith [hv.2]))
    have h1m : |16 * (1 - 8 * v)| ≤ 16 := by
      rw [abs_of_nonneg (by linarith [hv.2])]; linarith [hv.1]
    dsimp only [g', B]
    calc ‖-128 * invWallRootLogZero v + 16 * (1 - 8 * v) * (2 * v * wallRootLog v ^ 3)⁻¹‖
        ≤ ‖-128 * invWallRootLogZero v‖ + ‖16 * (1 - 8 * v) * (2 * v * wallRootLog v ^ 3)⁻¹‖ :=
          norm_add_le _ _
      _ ≤ 128 + 16 * (2 * v * wallRootLog v ^ 3)⁻¹ := by
          rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 128),
            Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
          exact add_le_add ((mul_le_mul_of_nonneg_left hw1 (by norm_num)).trans_eq (mul_one _))
            (mul_le_mul_of_nonneg_right h1m hpos)
  have hg'_int : IntervalIntegrable g' volume 0 (1 / 8) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    have hm_g' : Measurable g' :=
      (measurable_const.mul measurable_invWallRootLogZero).add
        ((measurable_const.mul (measurable_const.sub (measurable_const.mul measurable_id))).mul
          (((measurable_const.mul measurable_id).mul (measurable_wallRootLog.pow_const 3)).inv))
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hB_int).mono'
      hm_g'.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono hg'_bound)
  have hibp := ibp_cexp_neg_mul_real hab hg_cont hg_deriv hg'_int w
  have hs0 : cuspSubDeriv 0 = 0 := by simp [cuspSubDeriv, invWallRootLogZero]
  have hs8 : cuspSubDeriv (1 / 8) = 0 := by simp [cuspSubDeriv]
  simp only [hs0, hs8, Complex.ofReal_zero, mul_zero, sub_zero, zero_add] at hibp
  have hnorm_prod : ‖w‖ * ‖∫ v in (0 : ℝ)..(1 / 8),
      Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ)‖ ≤ 96 := by
    rw [← norm_mul, hibp]
    have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le hab
      (f := fun v => Complex.exp (-(w * (v : ℂ))) * (g' v : ℂ))
      (g := fun v => 3 * B v)
      (Eventually.of_forall fun v hv => by
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul (norm_cexp_neg_mul_le_three hw hv.1.le hv.2)
          (hg'_bound v hv) (norm_nonneg _) (by norm_num))
      (hB_int.const_mul 3)
    have hB_val : (∫ v in (0 : ℝ)..(1 / 8), 3 * B v) ≤ 96 := by
      dsimp only [B]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (intervalIntegrable_const (c := (128 : ℝ)))
          ((intervalIntegrable_inv_two_mul_wallRootLog_cube (b := 1 / 8) (by norm_num) (by norm_num)).const_mul 16),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral_inv_two_mul_wallRootLog_cube (b := 1 / 8) (by norm_num) (by norm_num), smul_eq_mul]
      have hw8 : (wallRootLog (1 / 8))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_wallRootLog (by norm_num) (by norm_num))
      linarith
    exact hnorm_int.trans hB_val
  exact (le_div_iff₀' (norm_pos_iff.mpr hne)).mpr hnorm_prod

private theorem three_halves_lt_neg_log_of_le_eighth {v : ℝ} (hv0 : 0 < v) (hv8 : v ≤ 1 / 8) :
    3 / 2 < -Real.log v := by
  have h8 : Real.log (1 / 8) = -(3 * Real.log 2) := by
    rw [log_one_div_eq_neg_log, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hle : Real.log v ≤ Real.log (1 / 8) := Real.log_le_log hv0 hv8
  have hl2 := Real.log_two_gt_d9
  linarith

private theorem norm_tail_cuspMainDeriv_le {w : ℂ} (hw : -5 ≤ w.re) (hne : w ≠ 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ8 : δ ≤ 1 / 8) :
    ‖∫ v in δ..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖ ≤
      3 / (‖w‖ * δ * wallRootLog δ ^ 3) := by
  let D : ℝ → ℝ := fun v => 2 * v * wallRootLog v ^ 3
  let D' : ℝ → ℝ := fun v => wallRootLog v * (2 * (-Real.log v) - 3)
  let h' : ℝ → ℝ := fun v =>
    -16 * (1 - 8 * v) * (D v)⁻¹ - (1 - 8 * v) ^ 2 * (D' v / D v ^ 2)
  have hD_pos : ∀ v ∈ Icc δ (1 / 8), 0 < D v := fun v hv => by
    have hv_pos : 0 < v := lt_of_lt_of_le hδ0 hv.1
    have hw_pos : 0 < wallRootLog v :=
      lt_of_lt_of_le zero_lt_one (one_le_wallRootLog hv_pos (hv.2.trans (by norm_num)))
    dsimp only [D]; positivity
  have hD_deriv : ∀ v ∈ Icc δ (1 / 8), HasDerivAt D (D' v) v := fun v hv => by
    have hv_pos : 0 < v := lt_of_lt_of_le hδ0 hv.1
    have hv4 : v ≤ 1 / 4 := hv.2.trans (by norm_num)
    have hw_pos : 0 < wallRootLog v := lt_of_lt_of_le zero_lt_one (one_le_wallRootLog hv_pos hv4)
    have hd1 : HasDerivAt (fun t : ℝ => 2 * t) 2 v :=
      ((hasDerivAt_id v).const_mul (2 : ℝ)).congr_deriv (mul_one _)
    have hd2 : HasDerivAt (fun t : ℝ => wallRootLog t ^ 3)
        (3 * wallRootLog v ^ 2 * (-((wallRootLog v)⁻¹ / (2 * v)))) v :=
      ((hasDerivAt_wallRootLog hv_pos hv4).pow 3).congr_deriv (by ring)
    refine (hd1.mul hd2).congr_deriv ?_
    dsimp only [D']
    have hsq := wallRootLog_sq hv_pos hv4
    have hw_ne := hw_pos.ne'
    calc 2 * wallRootLog v ^ 3 + 2 * v * (3 * wallRootLog v ^ 2 * (-((wallRootLog v)⁻¹ / (2 * v))))
        = 2 * (wallRootLog v ^ 2 * wallRootLog v) -
            3 * (wallRootLog v * (wallRootLog v * (wallRootLog v)⁻¹)) * ((2 * v) / (2 * v)) := by
          ring
      _ = wallRootLog v * (2 * (-Real.log v) - 3) := by
          rw [hsq, mul_inv_cancel₀ hw_ne, div_self (mul_pos two_pos hv_pos).ne']
          ring
  have hh_deriv : ∀ v ∈ Icc δ (1 / 8), HasDerivAt cuspMainDeriv (h' v) v := fun v hv => by
    have hd1 : HasDerivAt (fun t : ℝ => (1 - 8 * t) ^ 2) (-16 * (1 - 8 * v)) v := by
      have hlin : HasDerivAt (fun t : ℝ => 1 - 8 * t) (-8) v :=
        ((hasDerivAt_const v (1 : ℝ)).sub ((hasDerivAt_id v).const_mul (8 : ℝ))).congr_deriv
          (by ring)
      exact (hlin.pow 2).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun t : ℝ => (D t)⁻¹) (-(D' v / D v ^ 2)) v :=
      ((hD_deriv v hv).inv (hD_pos v hv).ne').congr_deriv (by ring)
    exact (hd1.mul hd2).congr_deriv (by dsimp only [h', D]; ring)
  have hh'_nonpos : ∀ v ∈ Icc δ (1 / 8), h' v ≤ 0 := fun v hv => by
    have hv_pos : 0 < v := lt_of_lt_of_le hδ0 hv.1
    have hw_pos : 0 < wallRootLog v :=
      lt_of_lt_of_le zero_lt_one (one_le_wallRootLog hv_pos (hv.2.trans (by norm_num)))
    have hlog32 := three_halves_lt_neg_log_of_le_eighth hv_pos hv.2
    have hD'_pos : 0 < D' v := by dsimp only [D']; exact mul_pos hw_pos (by linarith)
    have h1m : 0 ≤ 1 - 8 * v := by linarith [hv.2]
    have hDp := hD_pos v hv
    dsimp only [h']
    have ht1 : 0 ≤ 16 * (1 - 8 * v) * (D v)⁻¹ := by positivity
    have ht2 : 0 ≤ (1 - 8 * v) ^ 2 * (D' v / D v ^ 2) := by positivity
    linarith
  have hh_cont : ContinuousOn cuspMainDeriv (Icc δ (1 / 8)) :=
    fun v hv => (hh_deriv v hv).continuousAt.continuousWithinAt
  have hh'_cont : ContinuousOn h' (Icc δ (1 / 8)) := by
    intro v hv
    have hv_pos : 0 < v := lt_of_lt_of_le hδ0 hv.1
    have hc_log : ContinuousAt Real.log v := Real.continuousAt_log hv_pos.ne'
    have hc_w : ContinuousAt wallRootLog v :=
      Real.continuous_sqrt.continuousAt.comp
        ((Real.continuousAt_log (one_div_pos.mpr hv_pos).ne').comp
          (continuousAt_const.div continuousAt_id hv_pos.ne'))
    have hc_D : ContinuousAt D v :=
      ((continuousAt_const.mul continuousAt_id).mul (hc_w.pow 3))
    have hc_D' : ContinuousAt D' v :=
      hc_w.mul ((continuousAt_const.mul hc_log.neg).sub continuousAt_const)
    exact ((((by fun_prop : Continuous fun t : ℝ => -16 * (1 - 8 * t)).continuousAt).mul
      (hc_D.inv₀ (hD_pos v hv).ne')).sub
      (((by fun_prop : Continuous fun t : ℝ => (1 - 8 * t) ^ 2).continuousAt).mul
        (hc_D'.div (hc_D.pow 2) (pow_ne_zero 2 (hD_pos v hv).ne')))).continuousWithinAt
  have hh'_int : IntervalIntegrable h' volume δ (1 / 8) :=
    hh'_cont.intervalIntegrable_of_Icc hδ8
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ8 hh_cont
    (fun v hv => hh_deriv v ⟨hv.1.le, hv.2.le⟩) hh'_int
  have hm8 : cuspMainDeriv (1 / 8) = 0 := by simp [cuspMainDeriv]
  rw [hm8, zero_sub] at hftc
  have hibp := ibp_cexp_neg_mul_real hδ8 hh_cont
    (fun v hv => hh_deriv v ⟨hv.1.le, hv.2.le⟩) hh'_int w
  rw [hm8, Complex.ofReal_zero, mul_zero, sub_zero] at hibp
  have hmδ_nn : 0 ≤ cuspMainDeriv δ := by
    dsimp only [cuspMainDeriv]
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (hD_pos δ ⟨le_rfl, hδ8⟩).le)
  have hnorm_prod : ‖w‖ * ‖∫ v in δ..(1 / 8),
      Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖ ≤ 6 * cuspMainDeriv δ := by
    rw [← norm_mul, hibp]
    have hb1 : ‖Complex.exp (-(w * (δ : ℂ))) * (cuspMainDeriv δ : ℂ)‖ ≤ 3 * cuspMainDeriv δ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmδ_nn]
      exact mul_le_mul_of_nonneg_right (norm_cexp_neg_mul_le_three hw hδ0.le hδ8) hmδ_nn
    have hb2 : ‖∫ v in δ..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (h' v : ℂ)‖ ≤
        3 * cuspMainDeriv δ := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le hδ8
        (f := fun v => Complex.exp (-(w * (v : ℂ))) * (h' v : ℂ))
        (g := fun v => 3 * (-h' v))
        (Eventually.of_forall fun v hv => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (hh'_nonpos v ⟨hv.1.le, hv.2⟩)]
          exact mul_le_mul_of_nonneg_right
            (norm_cexp_neg_mul_le_three hw (lt_trans hδ0 hv.1).le hv.2)
            (neg_nonneg.mpr (hh'_nonpos v ⟨hv.1.le, hv.2⟩)))
        (hh'_int.neg.const_mul 3)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hftc, neg_neg] at h1
      exact h1
    exact (norm_add_le _ _).trans (by linarith)
  have hmδ_le : 6 * cuspMainDeriv δ ≤ 3 / (δ * wallRootLog δ ^ 3) := by
    dsimp only [cuspMainDeriv]
    have h1 : (1 - 8 * δ) ^ 2 ≤ 1 := by nlinarith [hδ0, hδ8]
    have hpos : 0 < 2 * δ * wallRootLog δ ^ 3 := hD_pos δ ⟨le_rfl, hδ8⟩
    calc 6 * ((1 - 8 * δ) ^ 2 * (2 * δ * wallRootLog δ ^ 3)⁻¹)
        ≤ 6 * (1 * (2 * δ * wallRootLog δ ^ 3)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hpos.le))
            (by norm_num)
      _ = 3 / (δ * wallRootLog δ ^ 3) := by
          rw [one_mul, show 2 * δ * wallRootLog δ ^ 3 = 2 * (δ * wallRootLog δ ^ 3) by ring,
            mul_inv]
          ring
  have hcomb := hnorm_prod.trans hmδ_le
  have hw3_pos : 0 < wallRootLog δ ^ 3 :=
    pow_pos (lt_of_lt_of_le zero_lt_one (one_le_wallRootLog hδ0 (hδ8.trans (by norm_num)))) 3
  have hd_pos : 0 < δ * wallRootLog δ ^ 3 := mul_pos hδ0 hw3_pos
  have hmul := mul_le_mul_of_nonneg_right hcomb hd_pos.le
  rw [div_mul_cancel₀ _ hd_pos.ne'] at hmul
  rw [le_div_iff₀ (mul_pos (mul_pos (norm_pos_iff.mpr hne) hδ0) hw3_pos)]
  linarith [show ‖∫ v in δ..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖ *
      (‖w‖ * δ * wallRootLog δ ^ 3) =
    (‖w‖ * ‖∫ v in δ..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖) *
      (δ * wallRootLog δ ^ 3) by ring]

private theorem norm_rescaled_laplace_smoothedWallLogProfile_le_five :
    ∀ (ℓ : ℝ) (w : ℂ), -5 ≤ w.re →
      ‖(w + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ ≤
        500 * |ℓ| / Real.sqrt (Real.log (‖w‖ + 4)) := by
  intro ℓ w hw
  have hlog4_pos : 0 < Real.log (‖w‖ + 4) :=
    Real.log_pos (by linarith [norm_nonneg w])
  have hsqrt_pos : 0 < Real.sqrt (Real.log (‖w‖ + 4)) := Real.sqrt_pos.mpr hlog4_pos
  rcases lt_or_ge ‖w‖ 16 with hlt16 | hge16
  · have hraw : ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ ≤ (3 / 8) * |ℓ| := by
      rw [laplace_smoothedWallLogProfile_eq_intervalIntegral, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      have hint := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1 / 8)
        (f := fun v => Complex.exp (-(w * (v : ℂ))) * (reflectedCusp v : ℂ))
        (g := fun _ => (3 : ℝ))
        (Eventually.of_forall fun v hv => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hr1 : |reflectedCusp v| ≤ 1 := by
            dsimp only [reflectedCusp]
            split_ifs with hm
            · have h2 : (wallRootLog v)⁻¹ ≤ 1 :=
                inv_le_one_of_one_le₀ (one_le_wallRootLog hm.1 (by linarith [hm.2]))
              have hw_nn : 0 ≤ (wallRootLog v)⁻¹ :=
                inv_nonneg.mpr (zero_le_one.trans (one_le_wallRootLog hm.1 (by linarith [hm.2])))
              rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hw_nn)]
              have h1 : (1 - 8 * v) ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
              nlinarith
            · simp
          exact (mul_le_mul (norm_cexp_neg_mul_le_three hw hv.1.le hv.2) hr1
            (abs_nonneg _) (by norm_num)).trans_eq (mul_one _))
        intervalIntegrable_const
      rw [intervalIntegral.integral_const, smul_eq_mul] at hint
      have hm := mul_le_mul_of_nonneg_left hint (abs_nonneg ℓ)
      linarith
    have hwp5 : ‖w + 5‖ ≤ 21 := by
      have hn : ‖(5 : ℂ)‖ = 5 := by norm_num
      linarith [norm_add_le w 5]
    have hprod : ‖(w + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ ≤
        8 * |ℓ| := by
      rw [norm_mul]
      calc ‖w + 5‖ * ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖
          ≤ 21 * ((3 / 8) * |ℓ|) := mul_le_mul hwp5 hraw (norm_nonneg _) (by norm_num)
        _ ≤ 8 * |ℓ| := by linarith [abs_nonneg ℓ]
    have hsqrt_le5 : Real.sqrt (Real.log (‖w‖ + 4)) ≤ 5 := by
      have hl : Real.log (‖w‖ + 4) ≤ 25 := by
        have h1 := Real.log_le_sub_one_of_pos (by linarith [norm_nonneg w] : 0 < ‖w‖ + 4)
        linarith
      exact (Real.sqrt_le_sqrt hl).trans (by norm_num)
    refine hprod.trans ((le_div_iff₀ hsqrt_pos).mpr ?_)
    have hm := mul_le_mul_of_nonneg_left hsqrt_le5 (show (0 : ℝ) ≤ 8 * |ℓ| by positivity)
    linarith [abs_nonneg ℓ]
  · set r := ‖w‖
    have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num) hge16
    have hw_ne : w ≠ 0 := norm_pos_iff.mp hr_pos
    set δ := r⁻¹
    have hδ0 : 0 < δ := inv_pos.mpr hr_pos
    have hδ16 : δ ≤ 1 / 16 :=
      (one_div r).symm.trans_le (one_div_le_one_div_of_le (by norm_num) hge16)
    have hδ8 : δ ≤ 1 / 8 := by linarith
    have hδ4 : δ ≤ 1 / 4 := by linarith
    have hwδ_eq : wallRootLog δ = Real.sqrt (Real.log r) := by
      unfold wallRootLog; rw [div_inv_eq_mul, one_mul]
    have hroot1 : 1 ≤ Real.sqrt (Real.log r) := by
      rw [← hwδ_eq]; exact one_le_wallRootLog hδ0 hδ4
    have hmain_int_0δ : IntervalIntegrable
        (fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) volume 0 δ :=
      (intervalIntegrable_ofReal (intervalIntegrable_cuspMainDeriv_zero hδ0 hδ8)).continuousOn_mul
        (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(w * (v : ℂ)))).continuousOn
    have hmain_int_δ8 : IntervalIntegrable
        (fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) volume δ (1 / 8) := by
      have hc : ContinuousOn cuspMainDeriv (Icc δ (1 / 8)) := by
        intro v hv
        have hv_pos : 0 < v := lt_of_lt_of_le hδ0 hv.1
        have hc_w : ContinuousAt wallRootLog v :=
          Real.continuous_sqrt.continuousAt.comp
            ((Real.continuousAt_log (one_div_pos.mpr hv_pos).ne').comp
              (continuousAt_const.div continuousAt_id hv_pos.ne'))
        exact (((by fun_prop : Continuous fun t : ℝ => (1 - 8 * t) ^ 2).continuousAt).mul
          (((continuousAt_const.mul continuousAt_id).mul (hc_w.pow 3)).inv₀
            (mul_pos (mul_pos two_pos hv_pos)
              (pow_pos (lt_of_lt_of_le zero_lt_one
                (one_le_wallRootLog hv_pos (hv.2.trans (by norm_num)))) 3)).ne')).continuousWithinAt
      exact (intervalIntegrable_ofReal
        (hc.intervalIntegrable_of_Icc hδ8)).continuousOn_mul
        (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(w * (v : ℂ)))).continuousOn
    have hnear_le : ‖∫ v in (0 : ℝ)..δ,
        Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖ ≤
          3 / Real.sqrt (Real.log r) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le hδ0.le
        (f := fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ))
        (g := fun v => 3 * (2 * v * wallRootLog v ^ 3)⁻¹)
        (Eventually.of_forall fun v hv => by
          have hpos : 0 ≤ (2 * v * wallRootLog v ^ 3)⁻¹ :=
            inv_nonneg.mpr (mul_nonneg (mul_nonneg zero_le_two hv.1.le)
              (pow_nonneg (zero_le_one.trans (one_le_wallRootLog hv.1 (by linarith [hv.2]))) 3))
          dsimp only [cuspMainDeriv]
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hpos)]
          have hb : (1 - 8 * v) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2, hδ8]
          exact mul_le_mul (norm_cexp_neg_mul_le_three hw hv.1.le (hv.2.trans hδ8))
            ((mul_le_mul_of_nonneg_right hb hpos).trans_eq (one_mul _))
            (mul_nonneg (sq_nonneg _) hpos) (by norm_num))
        ((intervalIntegrable_inv_two_mul_wallRootLog_cube hδ0 hδ4).const_mul 3)
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_inv_two_mul_wallRootLog_cube hδ0 hδ4, hwδ_eq, ← div_eq_mul_inv] at h1
      exact h1
    have htail_le : ‖∫ v in δ..(1 / 8),
        Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖ ≤
          3 / Real.sqrt (Real.log r) := by
      have ht := norm_tail_cuspMainDeriv_le hw hw_ne hδ0 hδ8
      have hsimp : r * δ * wallRootLog δ ^ 3 = Real.sqrt (Real.log r) ^ 3 := by
        dsimp only [δ]
        rw [mul_inv_cancel₀ hr_pos.ne', one_mul, hwδ_eq]
      rw [show ‖w‖ * δ * wallRootLog δ ^ 3 = r * δ * wallRootLog δ ^ 3 from rfl, hsimp] at ht
      refine ht.trans (div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le zero_lt_one hroot1) ?_)
      have hsq : 1 ≤ Real.sqrt (Real.log r) ^ 2 := by nlinarith
      nlinarith
    have hsub_le : ‖∫ v in (0 : ℝ)..(1 / 8),
        Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ)‖ ≤
          96 / Real.sqrt (Real.log r) := by
      refine (norm_integral_cuspSubDeriv_le hw hw_ne).trans
        (div_le_div_of_nonneg_left (by norm_num) (lt_of_lt_of_le zero_lt_one hroot1) ?_)
      have h1 : Real.sqrt (Real.log r) ≤ Real.log r := by
        have hsq := Real.sq_sqrt (Real.log_nonneg (by linarith : (1 : ℝ) ≤ r))
        nlinarith [hroot1, hsq]
      have h2 : Real.log r ≤ r := by linarith [Real.log_le_sub_one_of_pos hr_pos]
      exact h1.trans h2
    have hwL_le : ‖w * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ ≤
        102 * |ℓ| / Real.sqrt (Real.log r) := by
      rw [mul_laplace_smoothedWallLogProfile_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        ← intervalIntegral.integral_add_adjacent_intervals hmain_int_0δ hmain_int_δ8]
      have htri1 := (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hnear_le htail_le)) hsub_le)
      have hm := mul_le_mul_of_nonneg_left htri1 (abs_nonneg ℓ)
      calc |ℓ| * _ ≤ |ℓ| * (3 / Real.sqrt (Real.log r) + 3 / Real.sqrt (Real.log r) +
            96 / Real.sqrt (Real.log r)) := hm
        _ = 102 * |ℓ| / Real.sqrt (Real.log r) := by ring
    have hwp5_le : ‖(w + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ ≤
        2 * ‖w * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ := by
      rw [norm_mul, norm_mul]
      have hn : ‖w + 5‖ ≤ 2 * r := by
        have h5 : ‖(5 : ℂ)‖ = 5 := by norm_num
        linarith [norm_add_le w 5, hge16]
      exact (mul_le_mul_of_nonneg_right hn (norm_nonneg _)).trans_eq (mul_assoc _ _ _)
    have hlog_comp : Real.sqrt (Real.log (r + 4)) ≤ 2 * Real.sqrt (Real.log r) := by
      have hr2 : r + 4 ≤ r ^ 2 := by nlinarith [hge16]
      have hl : Real.log (r + 4) ≤ 4 * Real.log r := by
        have h1 := Real.log_le_log (by positivity) hr2
        rw [Real.log_pow] at h1
        push_cast at h1
        have hl0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
        linarith
      calc Real.sqrt (Real.log (r + 4))
          ≤ Real.sqrt (4 * Real.log r) := Real.sqrt_le_sqrt hl
        _ = 2 * Real.sqrt (Real.log r) := by
            rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num]
    have htot := hwp5_le.trans ((mul_le_mul_of_nonneg_left hwL_le zero_le_two).trans_eq
      (show 2 * (102 * |ℓ| / Real.sqrt (Real.log r)) = 204 * |ℓ| / Real.sqrt (Real.log r) by ring))
    refine htot.trans ?_
    rw [div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one hroot1) hsqrt_pos]
    have hm := mul_le_mul_of_nonneg_left hlog_comp (show (0 : ℝ) ≤ 204 * |ℓ| by positivity)
    linarith [mul_nonneg (abs_nonneg ℓ) (lt_of_lt_of_le zero_lt_one hroot1).le]

/-- **Uniform `O(|ℓ| / √(log(‖w‖ + 4)))` half-plane decay.** On the entire closed confinement
half-plane `Re w ≥ -4`, `(w + 5) L F_ℓ(w)` has modulus `O(|ℓ| / √(log(‖w‖ + 4)))`. -/
theorem norm_rescaled_laplace_smoothedWallLogProfile_le :
    ∃ C > 0, ∀ (ℓ : ℝ) (w : ℂ), -4 ≤ w.re →
      ‖(w + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w‖ ≤
        C * |ℓ| / Real.sqrt (Real.log (‖w‖ + 4)) :=
  ⟨500, by norm_num, fun ℓ w hw =>
    norm_rescaled_laplace_smoothedWallLogProfile_le_five ℓ w (by linarith)⟩

/-- **Uniform Lipschitz continuity of the rescaled transform on the imaginary axis.** -/
theorem smoothedWallLogProfile_axis_lipschitz :
    ∃ K > 0, ∀ (ℓ x y : ℝ),
      ‖(((y : ℂ) * I + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I)) -
        (((x : ℂ) * I + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((x : ℂ) * I))‖ ≤
          K * |ℓ| * |y - x| := by
  refine ⟨500, by norm_num, fun ℓ x y => ?_⟩
  let H : ℂ → ℂ := fun z =>
    (z + 5) * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) z
  have hd : ∀ z : ℂ, -4 < z.re → DifferentiableAt ℂ H z := fun z hz =>
    (differentiableAt_id.add_const _).mul
      (differentiableAt_laplace (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ) hz)
  have hb : ∀ z : ℂ, -4 ≤ z.re → ‖H z‖ ≤ 500 * |ℓ| := fun z hz => by
    have h1 := norm_rescaled_laplace_smoothedWallLogProfile_le_five ℓ z (by linarith)
    have hsqrt1 : 1 ≤ Real.sqrt (Real.log (‖z‖ + 4)) := by
      rw [Real.one_le_sqrt]
      have h4 : (1 : ℝ) ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9
        norm_num at *
        linarith
      exact h4.trans (Real.log_le_log (by norm_num) (by linarith [norm_nonneg z]))
    exact h1.trans (div_le_self (by positivity) hsqrt1)
  have hder : ∀ t : ℝ, ‖deriv H ((t : ℂ) * I)‖ ≤ 500 * |ℓ| := fun t => by
    have hball : ∀ z ∈ Metric.closedBall ((t : ℂ) * I) 1, -4 < z.re := fun z hz => by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h := (Complex.abs_re_le_norm (z - (t : ℂ) * I)).trans hz
      simp only [sub_re, mul_I_re, ofReal_im, neg_zero, sub_zero] at h
      linarith [(abs_le.mp h).1]
    have hdiff : DifferentiableOn ℂ H (Metric.closedBall ((t : ℂ) * I) 1) :=
      fun z hz => (hd z (hball z hz)).differentiableWithinAt
    simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1) (hdiff.diffContOnCl_ball Subset.rfl)
      (fun z hz => hb z (hball z (Metric.sphere_subset_closedBall hz)).le)
  have ht : ∀ t : ℝ, HasDerivAt (fun s : ℝ => H ((s : ℂ) * I)) (deriv H ((t : ℂ) * I) * I) t :=
    fun t => by
      have h := ((hd ((t : ℂ) * I) (by simp)).hasDerivAt.comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).mul_const I)).comp_ofReal
      simpa only [id_eq, one_mul, Function.comp_def] using h
  exact (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (ht t).hasDerivWithinAt)
    (fun t _ => by simpa only [norm_mul, norm_I, mul_one] using hder t)
    (mem_univ x) (mem_univ y)

private theorem norm_cexp_neg_ofReal_mul_I_sub_one_le (t : ℝ) :
    ‖Complex.exp (-((t : ℂ) * I)) - 1‖ ≤ |t| := by
  let f : ℝ → ℂ := fun s => Complex.exp (-((s : ℂ) * I))
  have hd : ∀ s : ℝ, HasDerivAt f (-I * f s) s := fun s =>
    ((hasDerivAt_cexp_neg_mul I s).congr_of_eventuallyEq
      (Eventually.of_forall fun t => by simp [f, mul_comm])).congr_deriv (by simp [f, mul_comm])
  have hnorm : ∀ s : ℝ, ‖-I * f s‖ ≤ 1 := fun s => by
    dsimp only [f]
    rw [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_exp]
    simp
  have hm := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hnorm s) (mem_univ 0) (mem_univ t)
  simpa [f] using hm

/-- **Exact imaginary-axis asymptotic of `smoothedWallLogProfile ℓ`.** As `y → +∞`,
`y √(log y) L F_ℓ(iy) → -i ℓ`. -/
theorem tendsto_axis_laplace_smoothedWallLogProfile (ℓ : ℝ) :
    Tendsto (fun y : ℝ => (y : ℂ) * (Real.sqrt (Real.log y) : ℂ) *
      negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I))
      atTop (𝓝 (-I * (ℓ : ℂ))) := by
  suffices hmul : Tendsto (fun y : ℝ => (((y : ℂ) * I) *
      negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I)) *
        (Real.sqrt (Real.log y) : ℂ)) atTop (𝓝 (ℓ : ℂ)) by
    have hI := hmul.const_mul (-I)
    refine hI.congr' ?_
    filter_upwards with y
    calc (-I) * ((((y : ℂ) * I) *
          negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I)) *
            (Real.sqrt (Real.log y) : ℂ))
        = (-(I * I)) * ((y : ℂ) * (Real.sqrt (Real.log y) : ℂ) *
            negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I)) := by ring
      _ = (y : ℂ) * (Real.sqrt (Real.log y) : ℂ) *
            negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I) := by
          rw [Complex.I_mul_I, neg_neg, one_mul]
  let err : ℝ → ℝ := fun y =>
    |ℓ| * (7 / (2 * Real.log y) + 104 * Real.sqrt (Real.log y) / y)
  have herr_zero : Tendsto err atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 7 / (2 * Real.log y)) atTop (𝓝 0) := by
      have hz := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp Real.tendsto_log_atTop).const_mul
        (7 / 2 : ℝ)
      rw [mul_zero] at hz
      exact hz.congr fun y => by dsimp only [Function.comp_apply]; ring
    have h2 : Tendsto (fun y : ℝ => 104 * Real.sqrt (Real.log y) / y) atTop (𝓝 0) := by
      have hz : Tendsto (fun y : ℝ => 104 * (Real.sqrt y)⁻¹) atTop (𝓝 0) := by
        simpa only [mul_zero, Function.comp_def] using
          ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_sqrt_atTop).const_mul 104
      refine squeeze_zero' ?_ ?_ hz
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
        exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (by linarith)
      · filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
        have hly : Real.log y ≤ y := by linarith [Real.log_le_sub_one_of_pos (lt_trans zero_lt_one hy)]
        have hs : Real.sqrt (Real.log y) ≤ Real.sqrt y := Real.sqrt_le_sqrt hly
        have hy_pos : 0 < y := lt_trans zero_lt_one hy
        calc 104 * Real.sqrt (Real.log y) / y
            ≤ 104 * Real.sqrt y / y :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hy_pos.le
          _ = 104 * (Real.sqrt y)⁻¹ := by
              have hs0 : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy_pos).ne'
              field_simp [hy_pos.ne', hs0]
              exact (Real.sq_sqrt hy_pos.le).symm
    simpa [err] using (h1.add h2).const_mul |ℓ|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herr_zero
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with y hy16
  have hy_pos : 0 < y := lt_of_lt_of_le (by norm_num) hy16
  set w : ℂ := (y : ℂ) * I
  have hw_re : -5 ≤ w.re := by simp [w]
  have hw_norm : ‖w‖ = y := by simp [w, abs_of_pos hy_pos]
  have hw_ne : w ≠ 0 := by rw [← norm_pos_iff, hw_norm]; exact hy_pos
  set δ := y⁻¹
  have hδ0 : 0 < δ := inv_pos.mpr hy_pos
  have hδ8 : δ ≤ 1 / 8 :=
    (one_div y).symm.trans_le (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hδ4 : δ ≤ 1 / 4 := by linarith
  have hwδ_eq : wallRootLog δ = Real.sqrt (Real.log y) := by
    unfold wallRootLog; rw [div_inv_eq_mul, one_mul]
  have hlog_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hsqrt_pos : 0 < Real.sqrt (Real.log y) := Real.sqrt_pos.mpr hlog_pos
  have hroot1 : 1 ≤ wallRootLog δ := one_le_wallRootLog hδ0 hδ4
  -- Split `0 .. (1/8)` at `δ = 1/y` and compare the `0 .. δ` integral with `(wallRootLog δ)⁻¹`.
  have hmain_int_0δ : IntervalIntegrable
      (fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) volume 0 δ :=
    (intervalIntegrable_ofReal (intervalIntegrable_cuspMainDeriv_zero hδ0 hδ8)).continuousOn_mul
      (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(w * (v : ℂ)))).continuousOn
  have hmain_int_δ8 : IntervalIntegrable
      (fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) volume δ (1 / 8) := by
    have hc : ContinuousOn cuspMainDeriv (Icc δ (1 / 8)) := by
      intro v hv
      have hv_pos : 0 < v := lt_of_lt_of_le hδ0 hv.1
      have hc_w : ContinuousAt wallRootLog v :=
        Real.continuous_sqrt.continuousAt.comp
          ((Real.continuousAt_log (one_div_pos.mpr hv_pos).ne').comp
            (continuousAt_const.div continuousAt_id hv_pos.ne'))
      exact (((by fun_prop : Continuous fun t : ℝ => (1 - 8 * t) ^ 2).continuousAt).mul
        (((continuousAt_const.mul continuousAt_id).mul (hc_w.pow 3)).inv₀
          (mul_pos (mul_pos two_pos hv_pos)
            (pow_pos (lt_of_lt_of_le zero_lt_one
              (one_le_wallRootLog hv_pos (hv.2.trans (by norm_num)))) 3)).ne')).continuousWithinAt
    exact (intervalIntegrable_ofReal
      (hc.intervalIntegrable_of_Icc hδ8)).continuousOn_mul
      (by fun_prop : Continuous fun v : ℝ => Complex.exp (-(w * (v : ℂ)))).continuousOn
  have hbase_int : IntervalIntegrable
      (fun v : ℝ => (((2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ)) volume 0 δ :=
    intervalIntegrable_ofReal (intervalIntegrable_inv_two_mul_wallRootLog_cube hδ0 hδ4)
  have hbase_val : (∫ v in (0 : ℝ)..δ, (((2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ)) =
      ((Real.sqrt (Real.log y) : ℂ))⁻¹ := by
    have h1 := Complex.ofRealCLM.intervalIntegral_comp_comm
      (intervalIntegrable_inv_two_mul_wallRootLog_cube hδ0 hδ4)
    change (∫ v in (0 : ℝ)..δ, (((2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ)) =
      (((∫ v in (0 : ℝ)..δ, (2 * v * wallRootLog v ^ 3)⁻¹) : ℝ) : ℂ) at h1
    rw [h1, intervalIntegral_inv_two_mul_wallRootLog_cube hδ0 hδ4, hwδ_eq, Complex.ofReal_inv]
  have hnear_diff : ‖(∫ v in (0 : ℝ)..δ,
      Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) -
        ((Real.sqrt (Real.log y) : ℂ))⁻¹‖ ≤
      1 / (2 * Real.sqrt (Real.log y) ^ 3) + 8 / y := by
    rw [← hbase_val, ← intervalIntegral.integral_sub hmain_int_0δ hbase_int]
    have hnorm_le := intervalIntegral.norm_integral_le_of_norm_le hδ0.le
      (f := fun v => Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ) -
        (((2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ))
      (g := fun _ => y / (2 * wallRootLog δ ^ 3) + 8)
      (Eventually.of_forall fun v hv => by
        have hpos_v : 0 < v := hv.1
        have hphi_nn : 0 ≤ (2 * v * wallRootLog v ^ 3)⁻¹ :=
          inv_nonneg.mpr (mul_nonneg (mul_nonneg zero_le_two hpos_v.le)
            (pow_nonneg (zero_le_one.trans (one_le_wallRootLog hpos_v (by linarith [hv.2]))) 3))
        have hsplit_pt : Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ) -
            (((2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ) =
          (Complex.exp (-(((y * v : ℝ) : ℂ) * I)) - 1) * (cuspMainDeriv v : ℂ) +
            ((((1 - 8 * v) ^ 2 - 1) * (2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ) := by
          dsimp only [w, cuspMainDeriv]
          push_cast
          ring
        rw [hsplit_pt]
        have hp1 : ‖(Complex.exp (-(((y * v : ℝ) : ℂ) * I)) - 1) * (cuspMainDeriv v : ℂ)‖ ≤
            y / (2 * wallRootLog δ ^ 3) := by
          rw [norm_mul, Complex.norm_real]
          have he := norm_cexp_neg_ofReal_mul_I_sub_one_le (y * v)
          rw [abs_of_pos (mul_pos hy_pos hpos_v)] at he
          have hm_le : ‖cuspMainDeriv v‖ ≤ (2 * v * wallRootLog δ ^ 3)⁻¹ := by
            dsimp only [cuspMainDeriv]
            rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hphi_nn)]
            have hb1 : (1 - 8 * v) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2, hδ8]
            have hw_anti := wallRootLog_anti hpos_v hv.2
            have hpow_le : wallRootLog δ ^ 3 ≤ wallRootLog v ^ 3 :=
              pow_le_pow_left₀ (zero_le_one.trans hroot1) hw_anti 3
            have hinv_le : (2 * v * wallRootLog v ^ 3)⁻¹ ≤ (2 * v * wallRootLog δ ^ 3)⁻¹ :=
              inv_anti₀ (mul_pos (mul_pos two_pos hpos_v)
                (pow_pos (lt_of_lt_of_le zero_lt_one hroot1) 3))
                (mul_le_mul_of_nonneg_left hpow_le (by positivity))
            exact ((mul_le_mul_of_nonneg_right hb1 hphi_nn).trans_eq (one_mul _)).trans hinv_le
          calc ‖Complex.exp (-(((y * v : ℝ) : ℂ) * I)) - 1‖ * ‖cuspMainDeriv v‖
              ≤ (y * v) * (2 * v * wallRootLog δ ^ 3)⁻¹ :=
                mul_le_mul he hm_le (norm_nonneg _) (by positivity)
            _ = y / (2 * wallRootLog δ ^ 3) := by
                rw [show 2 * v * wallRootLog δ ^ 3 = v * (2 * wallRootLog δ ^ 3) by ring,
                  mul_inv, show (y * v) * (v⁻¹ * (2 * wallRootLog δ ^ 3)⁻¹) =
                    (y / (2 * wallRootLog δ ^ 3)) * (v * v⁻¹) by ring,
                  mul_inv_cancel₀ hpos_v.ne', mul_one]
        have hp2 : ‖((((1 - 8 * v) ^ 2 - 1) * (2 * v * wallRootLog v ^ 3)⁻¹ : ℝ) : ℂ)‖ ≤ 8 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hphi_nn]
          have habs1 : |(1 - 8 * v) ^ 2 - 1| ≤ 16 * v := by
            rw [show (1 - 8 * v) ^ 2 - 1 = -(16 * v * (1 - 4 * v)) by ring, abs_neg,
              abs_of_nonneg (mul_nonneg (by positivity) (by linarith [hv.2, hδ8]))]
            nlinarith [hv.1, hv.2, hδ8]
          have hw3 : 1 ≤ wallRootLog v ^ 3 :=
            one_le_pow₀ (one_le_wallRootLog hpos_v (by linarith [hv.2]))
          have hphi_le : (2 * v * wallRootLog v ^ 3)⁻¹ ≤ (2 * v)⁻¹ :=
            inv_anti₀ (mul_pos two_pos hpos_v)
              ((le_mul_of_one_le_right (mul_pos two_pos hpos_v).le hw3))
          calc |(1 - 8 * v) ^ 2 - 1| * (2 * v * wallRootLog v ^ 3)⁻¹
              ≤ (16 * v) * (2 * v)⁻¹ :=
                mul_le_mul habs1 hphi_le hphi_nn (by positivity)
            _ = 8 := by
                rw [mul_inv, show (16 * v) * (2⁻¹ * v⁻¹) = 8 * (v * v⁻¹) by ring,
                  mul_inv_cancel₀ hpos_v.ne', mul_one]
        exact (norm_add_le _ _).trans (add_le_add hp1 hp2))
      intervalIntegrable_const
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hwδ_eq] at hnorm_le
    refine hnorm_le.trans_eq ?_
    dsimp only [δ]
    rw [add_mul, show y⁻¹ * (y / (2 * Real.sqrt (Real.log y) ^ 3)) =
      (1 / (2 * Real.sqrt (Real.log y) ^ 3)) * (y⁻¹ * y) by ring,
      inv_mul_cancel₀ hy_pos.ne', mul_one,
      show y⁻¹ * 8 = 8 / y by ring]
  have htail_le : ‖∫ v in δ..(1 / 8),
      Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)‖ ≤
        3 / Real.sqrt (Real.log y) ^ 3 := by
    have ht := norm_tail_cuspMainDeriv_le hw_re hw_ne hδ0 hδ8
    rw [hw_norm, show y * δ * wallRootLog δ ^ 3 = Real.sqrt (Real.log y) ^ 3 by
      dsimp only [δ]; rw [mul_inv_cancel₀ hy_pos.ne', one_mul, hwδ_eq]] at ht
    exact ht
  have hsub_le : ‖∫ v in (0 : ℝ)..(1 / 8),
      Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ)‖ ≤ 96 / y := by
    simpa only [hw_norm] using norm_integral_cuspSubDeriv_le hw_re hw_ne
  -- Assemble `((iy) L F_ℓ (iy)) √(log y) - ℓ`.
  have hident : (w * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w) *
      (Real.sqrt (Real.log y) : ℂ) - (ℓ : ℂ) =
      (ℓ : ℂ) * (Real.sqrt (Real.log y) : ℂ) *
        (((∫ v in (0 : ℝ)..δ, Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) -
            ((Real.sqrt (Real.log y) : ℂ))⁻¹) +
          (∫ v in δ..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspMainDeriv v : ℂ)) -
          (∫ v in (0 : ℝ)..(1 / 8), Complex.exp (-(w * (v : ℂ))) * (cuspSubDeriv v : ℂ))) := by
    rw [mul_laplace_smoothedWallLogProfile_eq,
      ← intervalIntegral.integral_add_adjacent_intervals hmain_int_0δ hmain_int_δ8]
    have hinv_c : (Real.sqrt (Real.log y) : ℂ) * ((Real.sqrt (Real.log y) : ℂ))⁻¹ = 1 :=
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hsqrt_pos.ne')
    linear_combination (ℓ : ℂ) * hinv_c
  change ‖(w * negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) w) *
      (Real.sqrt (Real.log y) : ℂ) - (ℓ : ℂ)‖ ≤ err y
  rw [hident, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg hsqrt_pos.le]
  have htri := (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hnear_diff htail_le)) hsub_le)
  have hm := mul_le_mul_of_nonneg_left htri (mul_nonneg (abs_nonneg ℓ) hsqrt_pos.le)
  refine hm.trans_eq ?_
  dsimp only [err]
  have hsq_eq : Real.sqrt (Real.log y) ^ 2 = Real.log y := Real.sq_sqrt hlog_pos.le
  calc |ℓ| * Real.sqrt (Real.log y) *
        (1 / (2 * Real.sqrt (Real.log y) ^ 3) + 8 / y +
          3 / Real.sqrt (Real.log y) ^ 3 + 96 / y)
      = |ℓ| * ((7 / (2 * Real.sqrt (Real.log y) ^ 2)) *
          (Real.sqrt (Real.log y) * (Real.sqrt (Real.log y))⁻¹) +
          104 * Real.sqrt (Real.log y) / y) := by
        rw [show Real.sqrt (Real.log y) ^ 3 =
          Real.sqrt (Real.log y) ^ 2 * Real.sqrt (Real.log y) by ring]
        field_simp [hsqrt_pos.ne', hy_pos.ne']
        ring
    _ = |ℓ| * (7 / (2 * Real.log y) + 104 * Real.sqrt (Real.log y) / y) := by
        rw [hsq_eq, mul_inv_cancel₀ hsqrt_pos.ne', mul_one]

/-- **Squared-modulus imaginary-axis asymptotic.** As `y → +∞`,
`y² (log y) ‖L F_ℓ(iy)‖² → ℓ²`. -/
theorem tendsto_sq_axis_laplace_smoothedWallLogProfile (ℓ : ℝ) :
    Tendsto (fun y : ℝ => y ^ 2 * Real.log y *
      ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((y : ℂ) * I)‖ ^ 2)
      atTop (𝓝 (ℓ ^ 2)) := by
  have h := ((tendsto_axis_laplace_smoothedWallLogProfile ℓ).norm).pow 2
  have hlim_eq : ‖-I * (ℓ : ℂ)‖ ^ 2 = ℓ ^ 2 := by
    rw [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hlim_eq] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy1
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy0,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt hl0]

/-! ### Unconditional sample-sum & Poisson-row bounds and fixed-window crowding saturation -/

private theorem tsum_onLineCopies_lorentzMassTerm_le (y : ℝ) :
    (∑' q : onLineCopies, lorentzMassTerm y (q : XiZeroCopy)) ≤
      8 * (xiLineTwoLogDerivConstant + Real.log (|y| + 4)) := by
  have hnn : ∀ q : XiZeroCopy, 0 ≤ lorentzMassTerm y q := fun q => by
    unfold lorentzMassTerm; positivity
  have hsub := Summable.tsum_subtype_le (f := lorentzMassTerm y) onLineCopies hnn
    (summable_lorentzMassTerm y)
  exact hsub.trans (lorentzMass_le_log y)

private theorem zeroValueMass_smoothedWallLogProfile_le (ℓ : ℝ) (q : onLineCopies) :
    (25 + (centredZero q).im ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q ≤
      250000 * ℓ ^ 2 / Real.log (|(centredZero q).im| + 4) := by
  have hre : (centredZero q).re = 0 := q.property
  have hw_eq : (centredZero q : ℂ) = ((centredZero q).im : ℂ) * I := by
    apply Complex.ext
    · simp [hre]
    · simp
  have hb := norm_rescaled_laplace_smoothedWallLogProfile_le_five ℓ (centredZero q)
    (by linarith [hre])
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hnorm_w : ‖(centredZero q : ℂ)‖ = |(centredZero q).im| := by
    conv_lhs => rw [hw_eq]
    rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnorm_wp5 : ‖(centredZero q : ℂ) + 5‖ ^ 2 = 25 + (centredZero q).im ^ 2 := by
    rw [hw_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring
  rw [norm_mul, mul_pow, hnorm_wp5, hnorm_w, div_pow, mul_pow, sq_abs,
    Real.sq_sqrt (Real.log_nonneg (by linarith [abs_nonneg (centredZero q).im]))] at hsq
  simpa only [zeroValueMass, show (500 : ℝ) ^ 2 * ℓ ^ 2 = 250000 * ℓ ^ 2 by ring] using hsq

/-- **Unconditional unit-window sample-square bound on `onLineCopies` of `ζ`.** Without assuming
`FiniteOffLine` or `RH`, the rescaled unit-window squared sample sum of `smoothedWallLogProfile ℓ`
over all critical-line zero copies of `ζ` is uniformly bounded by `C ℓ²`. -/
theorem smoothedWallLogProfile_local_critical_line_mass :
    ∃ C > 0, ∀ (ℓ y : ℝ),
      (1 + y ^ 2) * (∑' q : onLineCopies,
        if |(centredZero q).im - y| ≤ 1 then
          zeroValueMass (smoothedWallLogProfile ℓ) q else 0) ≤ C * ℓ ^ 2 := by
  set C₀ : ℝ := 16000000 * (|xiLineTwoLogDerivConstant| + 2)
  have hC₀_pos : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀, hC₀_pos, fun ℓ y => ?_⟩
  have hlog3_ge1 : 1 ≤ Real.log (|y| + 3) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have := Real.exp_one_lt_d9
      exact (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith)
    exact h3.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg y]))
  have hlog4_le : Real.log (|y| + 4) ≤ 2 * Real.log (|y| + 3) := by
    have hsq : |y| + 4 ≤ (|y| + 3) ^ 2 := by nlinarith [abs_nonneg y]
    have hl := Real.log_le_log (by positivity) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at hl
  have hterm_le : ∀ q : onLineCopies,
      (1 + y ^ 2) * (if |(centredZero q).im - y| ≤ 1 then
        zeroValueMass (smoothedWallLogProfile ℓ) q else 0) ≤
      (1000000 * ℓ ^ 2 / Real.log (|y| + 3)) * lorentzMassTerm y (q : XiZeroCopy) := fun q => by
    have hl_nn : 0 ≤ lorentzMassTerm y (q : XiZeroCopy) := by unfold lorentzMassTerm; positivity
    split_ifs with hd
    · set γ := (centredZero q).im
      have hsq_d : (γ - y) ^ 2 ≤ 1 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hd 2; rwa [sq_abs, one_pow] at this
      have hy_le : 1 + y ^ 2 ≤ 2 * (25 + γ ^ 2) := by
        nlinarith only [hsq_d, sq_nonneg (γ + y)]
      have hγ_ge : |y| + 3 ≤ |γ| + 4 := by
        have htri := abs_sub_abs_le_abs_sub y γ
        rw [abs_sub_comm] at htri
        linarith
      have hlog_ge : Real.log (|y| + 3) ≤ Real.log (|γ| + 4) :=
        Real.log_le_log (by positivity) hγ_ge
      have hlor_ge : (1 / 2 : ℝ) ≤ lorentzMassTerm y (q : XiZeroCopy) := by
        have he : lorentzMassTerm y (q : XiZeroCopy) = (1 + (y - γ) ^ 2)⁻¹ := by
          dsimp only [γ]
          rw [im_centredZero, lorentzMassTerm, one_div]
        rw [he, one_div]
        exact inv_anti₀ (by positivity) (by nlinarith only [hsq_d])
      have hzv := zeroValueMass_smoothedWallLogProfile_le ℓ q
      have h1 : (1 + y ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q ≤
          500000 * ℓ ^ 2 / Real.log (|y| + 3) := by
        calc (1 + y ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q
            ≤ 2 * ((25 + γ ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q) := by
              nlinarith [zeroValueMass_nonneg (smoothedWallLogProfile ℓ) q]
          _ ≤ 2 * (250000 * ℓ ^ 2 / Real.log (|γ| + 4)) :=
              mul_le_mul_of_nonneg_left hzv zero_le_two
          _ = 500000 * ℓ ^ 2 / Real.log (|γ| + 4) := by ring
          _ ≤ 500000 * ℓ ^ 2 / Real.log (|y| + 3) :=
              div_le_div_of_nonneg_left (by positivity)
                (lt_of_lt_of_le zero_lt_one hlog3_ge1) hlog_ge
      calc (1 + y ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q
          ≤ (500000 * ℓ ^ 2 / Real.log (|y| + 3)) * (2 * lorentzMassTerm y (q : XiZeroCopy)) :=
            (le_mul_of_one_le_right (div_nonneg (by positivity) (zero_le_one.trans hlog3_ge1))
              (by linarith)).trans' h1
        _ = (1000000 * ℓ ^ 2 / Real.log (|y| + 3)) * lorentzMassTerm y (q : XiZeroCopy) := by ring
    · rw [mul_zero]
      exact mul_nonneg (div_nonneg (by positivity) (zero_le_one.trans hlog3_ge1)) hl_nn
  have hlor_sum : Summable (fun q : onLineCopies => lorentzMassTerm y (q : XiZeroCopy)) :=
    (summable_lorentzMassTerm y).comp_injective Subtype.val_injective
  have hsum_lhs : Summable (fun q : onLineCopies =>
      (1 + y ^ 2) * (if |(centredZero q).im - y| ≤ 1 then
        zeroValueMass (smoothedWallLogProfile ℓ) q else 0)) :=
    (hlor_sum.mul_left _).of_nonneg_of_le
      (fun q => mul_nonneg (by positivity)
        (by by_cases h : |(centredZero q).im - y| ≤ 1 <;>
          simp [h, zeroValueMass_nonneg]))
      hterm_le
  rw [← tsum_mul_left]
  have htsum := Summable.tsum_le_tsum hterm_le hsum_lhs (hlor_sum.mul_left _)
  have hts_r : (∑' q : onLineCopies,
      (1000000 * ℓ ^ 2 / Real.log (|y| + 3)) * lorentzMassTerm y (q : XiZeroCopy)) =
      (1000000 * ℓ ^ 2 / Real.log (|y| + 3)) *
        ∑' q : onLineCopies, lorentzMassTerm y (q : XiZeroCopy) := tsum_mul_left
  rw [hts_r] at htsum
  have hlor_bd := tsum_onLineCopies_lorentzMassTerm_le y
  have hm := htsum.trans (mul_le_mul_of_nonneg_left hlor_bd
    (div_nonneg (by positivity : (0 : ℝ) ≤ 1000000 * ℓ ^ 2) (zero_le_one.trans hlog3_ge1)))
  refine hm.trans ?_
  have hnum_le : xiLineTwoLogDerivConstant + Real.log (|y| + 4) ≤
      (|xiLineTwoLogDerivConstant| + 2) * Real.log (|y| + 3) := by
    have h1 := le_abs_self xiLineTwoLogDerivConstant
    have h2 : |xiLineTwoLogDerivConstant| ≤ |xiLineTwoLogDerivConstant| * Real.log (|y| + 3) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog3_ge1
    linarith
  calc (1000000 * ℓ ^ 2 / Real.log (|y| + 3)) *
        (8 * (xiLineTwoLogDerivConstant + Real.log (|y| + 4)))
      ≤ (1000000 * ℓ ^ 2 / Real.log (|y| + 3)) *
          (8 * ((|xiLineTwoLogDerivConstant| + 2) * Real.log (|y| + 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnum_le (by norm_num))
          (div_nonneg (by positivity) (zero_le_one.trans hlog3_ge1))
    _ = 8000000 * (|xiLineTwoLogDerivConstant| + 2) * ℓ ^ 2 *
          (Real.log (|y| + 3) * (Real.log (|y| + 3))⁻¹) := by ring
    _ ≤ C₀ * ℓ ^ 2 := by
        rw [mul_inv_cancel₀ (lt_of_lt_of_le zero_lt_one hlog3_ge1).ne', mul_one]
        dsimp only [C₀]
        nlinarith [sq_nonneg ℓ, abs_nonneg xiLineTwoLogDerivConstant]

/-- **Unconditional `σ = -4` Poisson-row bound on `onLineCopies` of `ζ`.** Without assuming
`FiniteOffLine` or `RH`, the rescaled critical-line Poisson row of `smoothedWallLogProfile ℓ`
is uniformly bounded by `C ℓ²` at all heights `y`. -/
theorem smoothedWallLogProfile_poisson_row_bound :
    ∃ C > 0, ∀ (ℓ y : ℝ),
      (1 + y ^ 2) * (∑' q : onLineCopies,
        zeroValueMass (smoothedWallLogProfile ℓ) q *
          (4 / (16 + (y - (centredZero q).im) ^ 2))) ≤ C * ℓ ^ 2 := by
  set C₀ : ℝ := 128000000 * (|xiLineTwoLogDerivConstant| + 4)
  have hC₀_pos : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀, hC₀_pos, fun ℓ y => ?_⟩
  have hlog_y2 : 1 ≤ Real.log (|y| / 2 + 4) := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9
      norm_num at *; linarith
    exact h4.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg y]))
  have hlog4_ge1 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    norm_num at *; linarith
  have hlor_y : Summable (fun q : onLineCopies => lorentzMassTerm y (q : XiZeroCopy)) :=
    (summable_lorentzMassTerm y).comp_injective Subtype.val_injective
  have hlor_0 : Summable (fun q : onLineCopies => lorentzMassTerm 0 (q : XiZeroCopy)) :=
    (summable_lorentzMassTerm 0).comp_injective Subtype.val_injective
  have hpt : ∀ q : onLineCopies,
      (1 + y ^ 2) * (zeroValueMass (smoothedWallLogProfile ℓ) q *
        (4 / (16 + (y - (centredZero q).im) ^ 2))) ≤
      (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) * lorentzMassTerm y (q : XiZeroCopy) +
        (4000000 * ℓ ^ 2) * lorentzMassTerm 0 (q : XiZeroCopy) := fun q => by
    set γ := (centredZero q).im
    have hl_y_nn : 0 ≤ lorentzMassTerm y (q : XiZeroCopy) := by unfold lorentzMassTerm; positivity
    have hl_0_nn : 0 ≤ lorentzMassTerm 0 (q : XiZeroCopy) := by unfold lorentzMassTerm; positivity
    have hzv := zeroValueMass_smoothedWallLogProfile_le ℓ q
    rcases le_or_gt |γ - y| (|y| / 2) with hnear | hfar
    · have hγ_abs : |y| / 2 ≤ |γ| := by
        have htri := abs_sub_abs_le_abs_sub y γ
        rw [abs_sub_comm] at htri
        linarith
      have hy_sq : 1 + y ^ 2 ≤ 4 * (25 + γ ^ 2) := by
        have hsq := pow_le_pow_left₀ (by positivity) hγ_abs 2
        rw [div_pow, sq_abs, sq_abs] at hsq
        linarith
      have hlog_ge : Real.log (|y| / 2 + 4) ≤ Real.log (|γ| + 4) :=
        Real.log_le_log (by positivity) (by linarith)
      have hker_le : 4 / (16 + (y - γ) ^ 2) ≤ 4 * lorentzMassTerm y (q : XiZeroCopy) := by
        have he : lorentzMassTerm y (q : XiZeroCopy) = (1 + (y - γ) ^ 2)⁻¹ := by
          dsimp only [γ]
          rw [im_centredZero, lorentzMassTerm, one_div]
        rw [he, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (by positivity) (by linarith [sq_nonneg (y - γ)])) (by norm_num)
      have h1 : (1 + y ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q ≤
          1000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4) := by
        calc (1 + y ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q
            ≤ 4 * ((25 + γ ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q) := by
              nlinarith [zeroValueMass_nonneg (smoothedWallLogProfile ℓ) q]
          _ ≤ 4 * (250000 * ℓ ^ 2 / Real.log (|γ| + 4)) :=
              mul_le_mul_of_nonneg_left hzv (by norm_num)
          _ = 1000000 * ℓ ^ 2 / Real.log (|γ| + 4) := by ring
          _ ≤ 1000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4) :=
              div_le_div_of_nonneg_left (by positivity)
                (lt_of_lt_of_le zero_lt_one hlog_y2) hlog_ge
      have hm := mul_le_mul h1 hker_le (by positivity)
        (div_nonneg (by positivity) (zero_le_one.trans hlog_y2))
      have h2 : (4000000 * ℓ ^ 2) * lorentzMassTerm 0 (q : XiZeroCopy) ≥ 0 := by positivity
      linarith [show (1 + y ^ 2) * (zeroValueMass (smoothedWallLogProfile ℓ) q *
          (4 / (16 + (y - γ) ^ 2))) =
        ((1 + y ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q) *
          (4 / (16 + (y - γ) ^ 2)) by ring,
        show (1000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) *
          (4 * lorentzMassTerm y (q : XiZeroCopy)) =
          (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) * lorentzMassTerm y (q : XiZeroCopy) by ring]
    · have hker_far : (1 + y ^ 2) * (4 / (16 + (y - γ) ^ 2)) ≤ 16 := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        have hsq := pow_le_pow_left₀ (by positivity) hfar.le 2
        rw [div_pow, sq_abs, abs_sub_comm, sq_abs] at hsq
        linarith
      have hzv_lor0 : zeroValueMass (smoothedWallLogProfile ℓ) q ≤
          250000 * ℓ ^ 2 * lorentzMassTerm 0 (q : XiZeroCopy) := by
        have he : lorentzMassTerm 0 (q : XiZeroCopy) = (1 + γ ^ 2)⁻¹ := by
          dsimp only [γ]
          rw [im_centredZero, lorentzMassTerm, zero_sub, neg_sq, one_div]
        have hlog_ge : 1 ≤ Real.log (|γ| + 4) :=
          hlog4_ge1.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg γ]))
        have h1 : (1 + γ ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q ≤ 250000 * ℓ ^ 2 := by
          calc (1 + γ ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q
              ≤ (25 + γ ^ 2) * zeroValueMass (smoothedWallLogProfile ℓ) q :=
                mul_le_mul_of_nonneg_right (by linarith)
                  (zeroValueMass_nonneg (smoothedWallLogProfile ℓ) q)
            _ ≤ 250000 * ℓ ^ 2 / Real.log (|γ| + 4) := hzv
            _ ≤ 250000 * ℓ ^ 2 := div_le_self (by positivity) hlog_ge
        rw [he]
        exact ((le_div_iff₀' (by positivity)).mpr h1).trans_eq (div_eq_mul_inv _ _)
      have hm := mul_le_mul hker_far hzv_lor0 (zeroValueMass_nonneg _ _) (by norm_num)
      have h1_nn : 0 ≤ (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) *
          lorentzMassTerm y (q : XiZeroCopy) :=
        mul_nonneg (div_nonneg (by positivity) (zero_le_one.trans hlog_y2)) hl_y_nn
      linarith [show (1 + y ^ 2) * (zeroValueMass (smoothedWallLogProfile ℓ) q *
          (4 / (16 + (y - γ) ^ 2))) =
        ((1 + y ^ 2) * (4 / (16 + (y - γ) ^ 2))) *
          zeroValueMass (smoothedWallLogProfile ℓ) q by ring,
        show 16 * (250000 * ℓ ^ 2 * lorentzMassTerm 0 (q : XiZeroCopy)) =
          (4000000 * ℓ ^ 2) * lorentzMassTerm 0 (q : XiZeroCopy) by ring]
  have hsum_rhs := (hlor_y.mul_left (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4))).add
    (hlor_0.mul_left (4000000 * ℓ ^ 2))
  have hsum_lhs : Summable (fun q : onLineCopies =>
      (1 + y ^ 2) * (zeroValueMass (smoothedWallLogProfile ℓ) q *
        (4 / (16 + (y - (centredZero q).im) ^ 2)))) :=
    hsum_rhs.of_nonneg_of_le
      (fun q => mul_nonneg (by positivity)
        (mul_nonneg (zeroValueMass_nonneg _ _) (by positivity)))
      hpt
  rw [← tsum_mul_left]
  have htsum := Summable.tsum_le_tsum hpt hsum_lhs hsum_rhs
  have hts1 : (∑' b : onLineCopies,
      (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) * lorentzMassTerm y (b : XiZeroCopy)) =
      (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) *
        ∑' b : onLineCopies, lorentzMassTerm y (b : XiZeroCopy) := tsum_mul_left
  have hts2 : (∑' b : onLineCopies,
      (4000000 * ℓ ^ 2) * lorentzMassTerm 0 (b : XiZeroCopy)) =
      (4000000 * ℓ ^ 2) *
        ∑' b : onLineCopies, lorentzMassTerm 0 (b : XiZeroCopy) := tsum_mul_left
  rw [Summable.tsum_add (hlor_y.mul_left _) (hlor_0.mul_left _), hts1, hts2] at htsum
  have hbd_y := tsum_onLineCopies_lorentzMassTerm_le y
  have hbd_0 := tsum_onLineCopies_lorentzMassTerm_le 0
  have hlog_comp : Real.log (|y| + 4) ≤ 2 * Real.log (|y| / 2 + 4) := by
    have hsq : |y| + 4 ≤ (|y| / 2 + 4) ^ 2 := by nlinarith [abs_nonneg y]
    have hl := Real.log_le_log (by positivity) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at hl
  have hnum_y : xiLineTwoLogDerivConstant + Real.log (|y| + 4) ≤
      (|xiLineTwoLogDerivConstant| + 2) * Real.log (|y| / 2 + 4) := by
    have h1 := le_abs_self xiLineTwoLogDerivConstant
    have h2 : |xiLineTwoLogDerivConstant| ≤
        |xiLineTwoLogDerivConstant| * Real.log (|y| / 2 + 4) :=
      le_mul_of_one_le_right (abs_nonneg _) hlog_y2
    linarith
  have hnum_0 : xiLineTwoLogDerivConstant + Real.log (|(0 : ℝ)| + 4) ≤
      (|xiLineTwoLogDerivConstant| + 4) := by
    rw [abs_zero, zero_add]
    have h1 := le_abs_self xiLineTwoLogDerivConstant
    have h2 : Real.log 4 ≤ 4 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hp1 : (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) *
      (∑' q : onLineCopies, lorentzMassTerm y (q : XiZeroCopy)) ≤
      32000000 * (|xiLineTwoLogDerivConstant| + 2) * ℓ ^ 2 := by
    calc (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) * _
        ≤ (4000000 * ℓ ^ 2 / Real.log (|y| / 2 + 4)) *
            (8 * ((|xiLineTwoLogDerivConstant| + 2) * Real.log (|y| / 2 + 4))) :=
          mul_le_mul_of_nonneg_left
            (hbd_y.trans (mul_le_mul_of_nonneg_left hnum_y (by norm_num)))
            (div_nonneg (by positivity) (zero_le_one.trans hlog_y2))
      _ = 32000000 * (|xiLineTwoLogDerivConstant| + 2) * ℓ ^ 2 *
            (Real.log (|y| / 2 + 4) * (Real.log (|y| / 2 + 4))⁻¹) := by ring
      _ = 32000000 * (|xiLineTwoLogDerivConstant| + 2) * ℓ ^ 2 := by
          rw [mul_inv_cancel₀ (lt_of_lt_of_le zero_lt_one hlog_y2).ne', mul_one]
  have hp2 : (4000000 * ℓ ^ 2) *
      (∑' q : onLineCopies, lorentzMassTerm 0 (q : XiZeroCopy)) ≤
      32000000 * (|xiLineTwoLogDerivConstant| + 4) * ℓ ^ 2 := by
    calc (4000000 * ℓ ^ 2) * _
        ≤ (4000000 * ℓ ^ 2) * (8 * (|xiLineTwoLogDerivConstant| + 4)) :=
          mul_le_mul_of_nonneg_left
            (hbd_0.trans (mul_le_mul_of_nonneg_left hnum_0 (by norm_num))) (by positivity)
      _ = 32000000 * (|xiLineTwoLogDerivConstant| + 4) * ℓ ^ 2 := by ring
  refine htsum.trans ((add_le_add hp1 hp2).trans ?_)
  dsimp only [C₀]
  nlinarith [sq_nonneg ℓ, abs_nonneg xiLineTwoLogDerivConstant]

/-- **Fixed-window crowding saturation.** For any multiplicity-indexed ordinate family `γ : ι → ℝ`,
any window half-width `h > 0`, and any crowding constant `c > 0`, logarithmic crowding
`c log y ≤ #S` in `[y - h, y + h]` forces `smoothedWallLogProfile ℓ` to capture at least
`(c / 2) ℓ²` of rescaled squared mass in that window. The dependence on `c` (window width) and
on multiplicity copies in `S` is exact and linear. -/
theorem smoothedWallLogProfile_window_crowding_lower_bound {ι : Type*} {γ : ι → ℝ}
    {h c : ℝ} (_ : 0 < h) (hc : 0 < c)
    (hcrowd : ∀ᶠ y : ℝ in atTop, ∃ S : Finset ι,
      c * Real.log y ≤ S.card ∧ ∀ q ∈ S, |γ q - y| ≤ h)
    (ℓ : ℝ) :
    ∀ᶠ y : ℝ in atTop, ∃ S : Finset ι, (∀ q ∈ S, |γ q - y| ≤ h) ∧
      (c / 2) * ℓ ^ 2 ≤ y ^ 2 * ∑ q ∈ S,
        ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 := by
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · filter_upwards [hcrowd] with y ⟨S, _, hS⟩
    refine ⟨S, hS, ?_⟩
    rw [zero_pow two_ne_zero, mul_zero]
    exact mul_nonneg (sq_nonneg y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · have hℓ2 : 0 < ℓ ^ 2 := sq_pos_of_ne_zero hℓ
    obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp
      (tendsto_sq_axis_laplace_smoothedWallLogProfile ℓ) (ℓ ^ 2 / 4) (by positivity)
    filter_upwards [hcrowd,
      eventually_ge_atTop (max (T₀ + h) (max (8 * h) 256))] with y ⟨S, hcard, hS⟩ hy_big
    have hyT : T₀ + h ≤ y := (le_max_left _ _).trans hy_big
    have hy8h : 8 * h ≤ y := ((le_max_left _ _).trans (le_max_right _ _)).trans hy_big
    have hy256 : 256 ≤ y := ((le_max_right _ _).trans (le_max_right _ _)).trans hy_big
    have hy_pos : 0 < y := by linarith
    have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith)
    refine ⟨S, hS, ?_⟩
    have hpt : ∀ q ∈ S,
        (ℓ ^ 2 / (2 * Real.log y)) ≤ y ^ 2 *
          ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 := by
      intro q hq
      set t := γ q
      have hty := abs_le.mp (hS q hq)
      have ht_ge_T₀ : T₀ ≤ t := by linarith [hty.1]
      have ht_pos : 0 < t := by linarith [hty.1, hy8h]
      have ht_le : t ≤ (9 / 8) * y := by linarith [hty.2, hy8h]
      have hd := hT₀ t ht_ge_T₀
      rw [Real.dist_eq] at hd
      have hlb_t : (3 / 4) * ℓ ^ 2 ≤ t ^ 2 * Real.log t *
          ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((t : ℂ) * I)‖ ^ 2 := by
        linarith [(abs_lt.mp hd).1]
      have hsq_rel : t ^ 2 ≤ (81 / 64) * y ^ 2 := by
        have hs := pow_le_pow_left₀ ht_pos.le ht_le 2
        linarith [show ((9 / 8) * y) ^ 2 = (81 / 64) * y ^ 2 by ring]
      have hlog_rel : Real.log t ≤ (9 / 8) * Real.log y := by
        have ht_le_2y : t ≤ 2 * y := by linarith
        have hl1 : Real.log t ≤ Real.log y + Real.log 2 := by
          have := Real.log_le_log ht_pos ht_le_2y
          rwa [Real.log_mul two_pos.ne' hy_pos.ne', add_comm] at this
        have hl8 : 8 * Real.log 2 ≤ Real.log y := by
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 8)
            (by norm_num at hy256 ⊢; exact hy256)
          rwa [Real.log_pow, Nat.cast_ofNat] at this
        linarith
      have hlogt_nn : 0 ≤ Real.log t := Real.log_nonneg (by linarith [hty.1, hy8h, hy256])
      have hmul_rel : t ^ 2 * Real.log t ≤ (729 / 512) * (y ^ 2 * Real.log y) := by
        have hm := mul_le_mul hsq_rel hlog_rel hlogt_nn (by positivity)
        linarith [show ((81 / 64) * y ^ 2) * ((9 / 8) * Real.log y) =
          (729 / 512) * (y ^ 2 * Real.log y) by ring]
      set Z := ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((t : ℂ) * I)‖ ^ 2
      have hZ_nn : 0 ≤ Z := sq_nonneg _
      have hub_y : (3 / 4) * ℓ ^ 2 ≤ (729 / 512) * (y ^ 2 * Real.log y * Z) := by
        have hm := mul_le_mul_of_nonneg_right hmul_rel hZ_nn
        linarith [hlb_t, show (729 / 512) * (y ^ 2 * Real.log y) * Z =
          (729 / 512) * (y ^ 2 * Real.log y * Z) by ring]
      have hhalf : ℓ ^ 2 / 2 ≤ y ^ 2 * Real.log y * Z := by linarith
      rw [div_le_iff₀ (mul_pos two_pos hlogy_pos)]
      linarith [show (y ^ 2 * Z) * (2 * Real.log y) = 2 * (y ^ 2 * Real.log y * Z) by ring]
    rw [Finset.mul_sum]
    calc (c / 2) * ℓ ^ 2
        = (c * Real.log y) * (ℓ ^ 2 / (2 * Real.log y)) := by
          field_simp [hlogy_pos.ne']
      _ ≤ (S.card : ℝ) * (ℓ ^ 2 / (2 * Real.log y)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ _ ∈ S, (ℓ ^ 2 / (2 * Real.log y)) := by simp
      _ ≤ ∑ q ∈ S, y ^ 2 *
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 :=
          Finset.sum_le_sum hpt

/-- **Saturation of critical-line windows and the `σ = -4` Poisson row on `ζ` under
`FiniteOffLine`.** Under `BacklundConverse.FiniteOffLine`, for every window half-width `h > 0`
there exists `c_h > 0` such that `smoothedWallLogProfile ℓ` captures at least `(c_h / 2) ℓ²` in
every high `[y - h, y + h]` window on `onLineCopies` and at least `(2 c_h / (16 + h²)) ℓ²` in the
rescaled `σ = -4` Poisson row. -/
theorem smoothedWallLogProfile_saturates_criticalLine_under_finiteOffLine
    (hf : BacklundConverse.FiniteOffLine) {h : ℝ} (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ ∀ ℓ : ℝ,
      (∀ᶠ y : ℝ in atTop,
        (c / 2) * ℓ ^ 2 ≤ y ^ 2 * ∑' q : onLineCopies,
          if |(centredZero q).im - y| ≤ h then
            zeroValueMass (smoothedWallLogProfile ℓ) q else 0) ∧
      (∀ᶠ y : ℝ in atTop,
        (2 * c / (16 + h ^ 2)) * ℓ ^ 2 ≤ y ^ 2 * ∑' q : onLineCopies,
          zeroValueMass (smoothedWallLogProfile ℓ) q *
            (4 / (16 + (y - (centredZero q).im) ^ 2))) := by
  obtain ⟨c, hc, hcr0⟩ := SquareRootThreshold.critical_line_crowding_of_finiteOffLine hf hh
  have hcrowd : ∀ᶠ y : ℝ in atTop, ∃ S : Finset onLineCopies,
      c * Real.log y ≤ S.card ∧ ∀ q ∈ S, |(centredZero q).im - y| ≤ h := by
    filter_upwards [hcr0] with y ⟨s, hs, hq⟩
    have hon : ∀ q ∈ s, q ∈ onLineCopies := fun q hm => by
      change (centredZero q).re = 0
      simp [centredZero, (hq q hm).1]
    let e : {q // q ∈ s} ↪ onLineCopies :=
      ⟨fun q => ⟨q.val, hon q.val q.property⟩,
        fun _ _ he => Subtype.ext (congrArg (fun q : onLineCopies => q.val) he)⟩
    refine ⟨s.attach.map e, by simpa only [Finset.card_map, Finset.card_attach] using hs, ?_⟩
    intro q hm
    obtain ⟨r, _, rfl⟩ := Finset.mem_map.mp hm
    simpa [e, centredZero] using (hq r.val r.property).2
  refine ⟨c, hc, fun ℓ => ?_⟩
  have hm_sum : Summable (fun q : onLineCopies => zeroValueMass (smoothedWallLogProfile ℓ) q) :=
    (domain_zeroParseval_of_finiteOffLine
      (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ) hf).1
  have hsat := smoothedWallLogProfile_window_crowding_lower_bound hh hc hcrowd ℓ
  have hzv_eq : ∀ q : onLineCopies,
      ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) (((centredZero q).im : ℂ) * I)‖ ^ 2 =
        zeroValueMass (smoothedWallLogProfile ℓ) q := fun q => by
    have hre : (centredZero q).re = 0 := q.property
    have heq : (((centredZero q).im : ℂ) * I) = centredZero q := by
      apply Complex.ext
      · simp [hre]
      · simp
    rw [heq]; rfl
  constructor
  · filter_upwards [hsat] with y ⟨S, hS, hlb⟩
    have hwin_sum : Summable (fun q : onLineCopies =>
        if |(centredZero q).im - y| ≤ h then
          zeroValueMass (smoothedWallLogProfile ℓ) q else 0) :=
      hm_sum.of_nonneg_of_le
        (fun q => by by_cases hp : |(centredZero q).im - y| ≤ h <;>
          simp [hp, zeroValueMass_nonneg])
        (fun q => by by_cases hp : |(centredZero q).im - y| ≤ h <;>
          simp [hp, zeroValueMass_nonneg])
    have hfin_le := hwin_sum.sum_le_tsum S fun q _ => by
      by_cases hp : |(centredZero q).im - y| ≤ h <;> simp [hp, zeroValueMass_nonneg]
    have hfin_eq : (∑ q ∈ S,
        ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) (((centredZero q).im : ℂ) * I)‖ ^ 2) =
        ∑ q ∈ S, if |(centredZero q).im - y| ≤ h then
          zeroValueMass (smoothedWallLogProfile ℓ) q else 0 :=
      Finset.sum_congr rfl fun q hq => by rw [hzv_eq q, if_pos (hS q hq)]
    exact hlb.trans (mul_le_mul_of_nonneg_left (hfin_eq ▸ hfin_le) (sq_nonneg y))
  · filter_upwards [hsat] with y ⟨S, hS, hlb⟩
    have hpois_sum : Summable (fun q : onLineCopies =>
        zeroValueMass (smoothedWallLogProfile ℓ) q *
          (4 / (16 + (y - (centredZero q).im) ^ 2))) :=
      hm_sum.of_nonneg_of_le
        (fun q => mul_nonneg (zeroValueMass_nonneg _ _) (by positivity))
        (fun q => mul_le_of_le_one_right (zeroValueMass_nonneg _ _)
          ((div_le_one (by positivity)).mpr (by linarith [sq_nonneg (y - (centredZero q).im)])))
    have hfin_le := hpois_sum.sum_le_tsum S
      (fun q _ => mul_nonneg (zeroValueMass_nonneg _ _) (by positivity))
    have hker_lb : ∀ q ∈ S,
        (4 / (16 + h ^ 2)) *
          ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
            (((centredZero q).im : ℂ) * I)‖ ^ 2 ≤
        zeroValueMass (smoothedWallLogProfile ℓ) q *
          (4 / (16 + (y - (centredZero q).im) ^ 2)) := fun q hq => by
      rw [hzv_eq q, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (zeroValueMass_nonneg _ _)
      have hsq : (y - (centredZero q).im) ^ 2 ≤ h ^ 2 := by
        have hs := pow_le_pow_left₀ (abs_nonneg _) (hS q hq) 2
        rwa [abs_sub_comm, sq_abs] at hs
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have hsum_ker := Finset.sum_le_sum hker_lb
    rw [← Finset.mul_sum] at hsum_ker
    have hm1 := mul_le_mul_of_nonneg_left (hsum_ker.trans hfin_le) (sq_nonneg y)
    have hm2 := mul_le_mul_of_nonneg_left hlb (show (0 : ℝ) ≤ 4 / (16 + h ^ 2) by positivity)
    calc (2 * c / (16 + h ^ 2)) * ℓ ^ 2
        = (4 / (16 + h ^ 2)) * ((c / 2) * ℓ ^ 2) := by ring
      _ ≤ (4 / (16 + h ^ 2)) * (y ^ 2 * ∑ q ∈ S,
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
              (((centredZero q).im : ℂ) * I)‖ ^ 2) := hm2
      _ = y ^ 2 * ((4 / (16 + h ^ 2)) * ∑ q ∈ S,
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
              (((centredZero q).im : ℂ) * I)‖ ^ 2) := by ring
      _ ≤ y ^ 2 * ∑' q : onLineCopies,
            zeroValueMass (smoothedWallLogProfile ℓ) q *
              (4 / (16 + (y - (centredZero q).im) ^ 2)) := hm1

/-! ### Unconditional Riemann–von Mangoldt ordinate model and variational half-line ground state -/

/-- Explicit deterministic Riemann–von Mangoldt index set: on each unit interval `[m + 3, m + 4)`
(`m : ℕ`), place `⌈log(m + 3)⌉₊` uniformly spaced ordinates. -/
def RvmCopy : Type := Σ m : ℕ, Fin (⌈Real.log ((m : ℝ) + 3)⌉₊)

/-- Ordinate of a `RvmCopy` sample: `m + 3 + j / ⌈log(m + 3)⌉₊ ∈ [m + 3, m + 4)`. -/
def rvmOrdinate (q : RvmCopy) : ℝ :=
  (q.1 : ℝ) + 3 + (q.2.1 : ℝ) / (⌈Real.log ((q.1 : ℝ) + 3)⌉₊ : ℝ)

private theorem rvmOrdinate_bounds (q : RvmCopy) :
    (q.1 : ℝ) + 3 ≤ rvmOrdinate q ∧ rvmOrdinate q < (q.1 : ℝ) + 4 := by
  dsimp only [rvmOrdinate]
  have hlog_pos : 0 < Real.log ((q.1 : ℝ) + 3) :=
    Real.log_pos (by linarith [(Nat.cast_nonneg q.1 : (0 : ℝ) ≤ q.1)])
  have hceil_pos : (0 : ℝ) < (⌈Real.log ((q.1 : ℝ) + 3)⌉₊ : ℝ) :=
    lt_of_lt_of_le hlog_pos (Nat.le_ceil _)
  constructor
  · have : 0 ≤ (q.2.1 : ℝ) / (⌈Real.log ((q.1 : ℝ) + 3)⌉₊ : ℝ) := by positivity
    linarith
  · have hlt : (q.2.1 : ℝ) < (⌈Real.log ((q.1 : ℝ) + 3)⌉₊ : ℝ) := by exact_mod_cast q.2.2
    have hdiv : (q.2.1 : ℝ) / (⌈Real.log ((q.1 : ℝ) + 3)⌉₊ : ℝ) < 1 :=
      (div_lt_one hceil_pos).mpr hlt
    linarith

/-- Every `RvmCopy` family satisfies the exact logarithmic crowding law in every window `[y - h, y + h]`. -/
theorem rvmOrdinate_crowding {h : ℝ} (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ y : ℝ in atTop, ∃ S : Finset RvmCopy,
      c * Real.log y ≤ S.card ∧ ∀ q ∈ S, |rvmOrdinate q - y| ≤ h := by
  set h₀ := min h (1 / 2)
  have hh₀_pos : 0 < h₀ := lt_min hh (by norm_num)
  have hh₀_half : h₀ ≤ 1 / 2 := min_le_right _ _
  have hh₀_le_h : h₀ ≤ h := min_le_left _ _
  refine ⟨h₀ / 8, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 8 (Real.exp (8 / h₀)))] with y hy_big
  have hy8 : 8 ≤ y := (le_max_left _ _).trans hy_big
  have hy_exp : Real.exp (8 / h₀) ≤ y := (le_max_right _ _).trans hy_big
  have hy_pos : 0 < y := by linarith
  have hlogy_big : 8 / h₀ ≤ Real.log y := (Real.le_log_iff_exp_le hy_pos).mpr hy_exp
  have hlogy_pos : 0 < Real.log y := lt_of_lt_of_le (by positivity) hlogy_big
  set n : ℕ := ⌊y⌋₊
  have hn_ge3 : 3 ≤ n := Nat.le_floor (by norm_num; linarith : ((3 : ℕ) : ℝ) ≤ y)
  set m : ℕ := n - 3
  have hm_eq : (m : ℝ) + 3 = (n : ℝ) := by
    have : m + 3 = n := Nat.sub_add_cancel hn_ge3
    exact_mod_cast this
  set B : ℝ := (m : ℝ) + 3
  have hB_le_y : B ≤ y := by rw [hm_eq]; exact Nat.floor_le hy_pos.le
  have hy_lt_B1 : y < B + 1 := by rw [hm_eq]; exact Nat.lt_floor_add_one y
  have hB_ge_half : y / 2 ≤ B := by linarith
  set N : ℕ := ⌈Real.log B⌉₊
  have hN_ge_half_log : (1 / 2) * Real.log y ≤ (N : ℝ) := by
    have hlB : Real.log (y / 2) ≤ Real.log B := Real.log_le_log (by positivity) hB_ge_half
    rw [Real.log_div hy_pos.ne' two_pos.ne'] at hlB
    have hl2 : 2 * Real.log 2 ≤ Real.log y := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 2) (by linarith : (2 : ℝ) ^ 2 ≤ y)
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    exact (by linarith : (1 / 2) * Real.log y ≤ Real.log B).trans (Nat.le_ceil _)
  have hN_pos_real : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hN_ge_half_log
  have hh₀N_ge4 : 4 ≤ h₀ * (N : ℝ) := by
    have hm1 := mul_le_mul_of_nonneg_left hN_ge_half_log hh₀_pos.le
    have hm2 : 8 ≤ h₀ * Real.log y := by
      have := (div_le_iff₀ hh₀_pos).mp hlogy_big
      linarith
    linarith
  -- Choose `[a, a + h₀] ⊆ [B, B + 1] ∩ [y - h₀, y + h₀]`.
  obtain ⟨a, haB, ha1, hay_lo, hay_hi⟩ :
      ∃ a : ℝ, B ≤ a ∧ a + h₀ ≤ B + 1 ∧ y - h₀ ≤ a ∧ a + h₀ ≤ y + h₀ := by
    rcases le_or_gt (y - B) (1 / 2) with hleft | hright
    · exact ⟨y, hB_le_y, by linarith, by linarith, by linarith⟩
    · exact ⟨y - h₀, by linarith, by linarith, le_rfl, by linarith⟩
  set j₀ : ℕ := ⌈(a - B) * (N : ℝ)⌉₊
  set K : ℕ := ⌊(h₀ / 2) * (N : ℝ)⌋₊
  have hj_lt_N : ∀ j ∈ Finset.Ico j₀ (j₀ + K), j < N := by
    intro j hj
    have hj_ub : (j : ℝ) < ((a - B) * (N : ℝ) + 1) + (h₀ / 2) * (N : ℝ) := by
      have hlt_nat : j < j₀ + K := (Finset.mem_Ico.mp hj).2
      have hlt_real : (j : ℝ) ≤ (j₀ : ℝ) + (K : ℝ) - 1 := by
        have h1 : j + 1 ≤ j₀ + K := hlt_nat
        have h2 : (j : ℝ) + 1 ≤ (j₀ : ℝ) + (K : ℝ) := by exact_mod_cast h1
        linarith
      have hj₀_ub : (j₀ : ℝ) < (a - B) * (N : ℝ) + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg (sub_nonneg.mpr haB) hN_pos_real.le)
      have hK_ub : (K : ℝ) ≤ (h₀ / 2) * (N : ℝ) := Nat.floor_le (by positivity)
      linarith
    have hub2 : ((a - B) * (N : ℝ) + 1) + (h₀ / 2) * (N : ℝ) ≤ (N : ℝ) := by
      have h1 : a - B + h₀ ≤ 1 := by linarith
      have hm := mul_le_mul_of_nonneg_right h1 hN_pos_real.le
      nlinarith [hh₀N_ge4]
    exact_mod_cast lt_of_lt_of_le hj_ub hub2
  let emb : {j // j ∈ Finset.Ico j₀ (j₀ + K)} ↪ RvmCopy :=
    ⟨fun j => ⟨m, ⟨j.1, hj_lt_N j.1 j.2⟩⟩,
      fun x y hxy => by
        have h2 := (Sigma.mk.inj_iff.mp hxy).2
        have hval : x.1 = y.1 := congrArg Fin.val (heq_iff_eq.mp h2)
        exact Subtype.ext hval⟩
  refine ⟨(Finset.Ico j₀ (j₀ + K)).attach.map emb, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_attach, Nat.card_Ico, add_tsub_cancel_left]
    have hK_lb : (h₀ / 2) * (N : ℝ) - 1 ≤ (K : ℝ) := by
      linarith [Nat.lt_floor_add_one ((h₀ / 2) * (N : ℝ))]
    nlinarith [hh₀N_ge4, mul_le_mul_of_nonneg_left hN_ge_half_log hh₀_pos.le]
  · intro q hq
    obtain ⟨⟨j, hj⟩, _, rfl⟩ := Finset.mem_map.mp hq
    have hj_ge : j₀ ≤ j := (Finset.mem_Ico.mp hj).1
    have hj_lt : j < j₀ + K := (Finset.mem_Ico.mp hj).2
    have hord_lo : a ≤ rvmOrdinate ⟨m, ⟨j, hj_lt_N j hj⟩⟩ := by
      dsimp only [rvmOrdinate]
      change a ≤ B + (j : ℝ) / (N : ℝ)
      have h1 : (a - B) * (N : ℝ) ≤ (j : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hj_ge)
      have h2 : a - B ≤ (j : ℝ) / (N : ℝ) := (le_div_iff₀ hN_pos_real).mpr h1
      linarith
    have hord_hi : rvmOrdinate ⟨m, ⟨j, hj_lt_N j hj⟩⟩ ≤ a + h₀ := by
      dsimp only [rvmOrdinate]
      change B + (j : ℝ) / (N : ℝ) ≤ a + h₀
      have hlt_real : (j : ℝ) ≤ (j₀ : ℝ) + (K : ℝ) - 1 := by
        have h1 : j + 1 ≤ j₀ + K := hj_lt
        have h2 : (j : ℝ) + 1 ≤ (j₀ : ℝ) + (K : ℝ) := by exact_mod_cast h1
        linarith
      have hj₀_ub : (j₀ : ℝ) < (a - B) * (N : ℝ) + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg (sub_nonneg.mpr haB) hN_pos_real.le)
      have hK_ub : (K : ℝ) ≤ (h₀ / 2) * (N : ℝ) := Nat.floor_le (by positivity)
      have h1 : (j : ℝ) ≤ (a - B + h₀) * (N : ℝ) := by nlinarith [hh₀N_ge4]
      have h2 : (j : ℝ) / (N : ℝ) ≤ a - B + h₀ := (div_le_iff₀ hN_pos_real).mpr h1
      linarith
    have hemb : emb ⟨j, hj⟩ = ⟨m, ⟨j, hj_lt_N j hj⟩⟩ := rfl
    rw [hemb]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans hh₀_le_h

/-- Every `RvmCopy` family satisfies the uniform rescaled unit-window sample-square bound
assumed in `decay_from_crowding`. -/
theorem smoothedWallLogProfile_rvmOrdinate_unit_window_bound :
    ∃ C > 0, ∀ (ℓ y : ℝ) (S : Finset RvmCopy),
      (∀ q ∈ S, |rvmOrdinate q - y| ≤ 1) →
        ∑ q ∈ S, ‖(((rvmOrdinate q : ℂ) * I) + 5) *
          negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
            ((rvmOrdinate q : ℂ) * I)‖ ^ 2 ≤ C * ℓ ^ 2 := by
  refine ⟨6000000, by norm_num, fun ℓ y S hS => ?_⟩
  by_cases hemp : S = ∅
  · rw [hemp, Finset.sum_empty]
    positivity
  · obtain ⟨q₀, hq₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    have hy_ge1 : 1 ≤ y := by
      have h0 := (rvmOrdinate_bounds q₀).1
      have h1 := (abs_le.mp (hS q₀ hq₀)).2
      linarith [(Nat.cast_nonneg q₀.1 : (0 : ℝ) ≤ q₀.1)]
    have hlog_pos : 0 < Real.log (y + 2) := Real.log_pos (by linarith)
    -- Every `q ∈ S` has `y - 2 < q.1 + 3 ≤ y + 1`, so `q.1` lies in `Finset.Icc (⌊y⌋₊ - 4) (⌊y⌋₊ + 1)`.
    let M_lo : ℕ := ⌊y⌋₊ - 4
    let M_hi : ℕ := ⌊y⌋₊ + 1
    let N_cap : ℕ := ⌈Real.log (y + 5)⌉₊
    have hN_cap_pos : 0 < N_cap := Nat.ceil_pos.mpr (Real.log_pos (by linarith))
    have hm_range : ∀ q ∈ S, q.1 ∈ Finset.Icc M_lo M_hi ∧ q.2.1 < N_cap := by
      intro q hq
      have hb := rvmOrdinate_bounds q
      have hd := abs_le.mp (hS q hq)
      have hq_hi : (q.1 : ℝ) + 3 ≤ y + 1 := by linarith [hb.1, hd.2]
      have hq_lo : y - 2 < (q.1 : ℝ) + 3 := by linarith [hb.2, hd.1]
      have hm_le : q.1 ≤ M_hi := by
        have hfl : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
        have hlt : (q.1 : ℝ) < (⌊y⌋₊ : ℝ) + 2 := by linarith
        have hnat : q.1 < ⌊y⌋₊ + 2 := by exact_mod_cast hlt
        exact Nat.le_of_lt_succ hnat
      have hm_ge : M_lo ≤ q.1 := by
        by_cases h4 : ⌊y⌋₊ ≤ 4
        · have : M_lo = 0 := Nat.sub_eq_zero_of_le h4
          rw [this]; exact Nat.zero_le _
        · have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
          have hsub_cast : (M_lo : ℝ) = (⌊y⌋₊ : ℝ) - 4 :=
            Nat.cast_sub (not_le.mp h4).le
          have hlt : (M_lo : ℝ) < (q.1 : ℝ) + 1 := by linarith
          have hnat : M_lo < q.1 + 1 := by exact_mod_cast hlt
          exact Nat.le_of_lt_succ hnat
      have hj_lt : q.2.1 < N_cap := by
        refine lt_of_lt_of_le q.2.2 (Nat.ceil_mono ?_)
        exact Real.log_le_log (by linarith [(Nat.cast_nonneg q.1 : (0 : ℝ) ≤ q.1)]) (by linarith)
      exact ⟨Finset.mem_Icc.mpr ⟨hm_ge, hm_le⟩, hj_lt⟩
    have hcard_le : S.card ≤ 6 * N_cap := by
      let f : {q // q ∈ S} → ↥(Finset.Icc M_lo M_hi) × Fin N_cap :=
        fun q => (⟨q.1.1, (hm_range q.1 q.2).1⟩, ⟨q.1.2.1, (hm_range q.1 q.2).2⟩)
      have hfinj : Function.Injective f := by
        intro a b hab
        have h1 : a.1.1 = b.1.1 := congrArg Subtype.val (Prod.mk.inj hab).1
        have h2 : a.1.2.1 = b.1.2.1 := congrArg Fin.val (Prod.mk.inj hab).2
        apply Subtype.ext
        rcases a with ⟨⟨ma, ja⟩, ha⟩
        rcases b with ⟨⟨mb, jb⟩, hb⟩
        dsimp only at h1 h2
        subst h1
        exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))
      have hc1 := Fintype.card_le_of_injective f hfinj
      simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin] at hc1
      have hIcc_le : (Finset.Icc M_lo M_hi).card ≤ 6 := by
        rw [Nat.card_Icc]
        dsimp only [M_lo, M_hi]
        omega
      exact hc1.trans (Nat.mul_le_mul_right N_cap hIcc_le)
    have hpt : ∀ q ∈ S,
        ‖(((rvmOrdinate q : ℂ) * I) + 5) *
          negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
            ((rvmOrdinate q : ℂ) * I)‖ ^ 2 ≤
          250000 * ℓ ^ 2 / Real.log (y + 2) := fun q hq => by
      have hb := norm_rescaled_laplace_smoothedWallLogProfile_le_five ℓ
        ((rvmOrdinate q : ℂ) * I) (by simp)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hnorm : ‖((rvmOrdinate q : ℂ) * I)‖ = rvmOrdinate q := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [(rvmOrdinate_bounds q).1, (Nat.cast_nonneg q.1 : (0 : ℝ) ≤ q.1)])]
      rw [hnorm, div_pow, mul_pow, sq_abs,
        Real.sq_sqrt (Real.log_nonneg (by linarith [(rvmOrdinate_bounds q).1,
          (Nat.cast_nonneg q.1 : (0 : ℝ) ≤ q.1)]))] at hsq
      have hord_ge : y + 2 ≤ rvmOrdinate q + 4 := by linarith [(abs_le.mp (hS q hq)).1]
      have hlog_ge : Real.log (y + 2) ≤ Real.log (rvmOrdinate q + 4) :=
        Real.log_le_log (by linarith) hord_ge
      calc ‖(((rvmOrdinate q : ℂ) * I) + 5) *
            negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
              ((rvmOrdinate q : ℂ) * I)‖ ^ 2
          ≤ 500 ^ 2 * ℓ ^ 2 / Real.log (rvmOrdinate q + 4) := hsq
        _ = 250000 * ℓ ^ 2 / Real.log (rvmOrdinate q + 4) := by ring
        _ ≤ 250000 * ℓ ^ 2 / Real.log (y + 2) :=
            div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_ge
    have hsum_le : ∑ q ∈ S,
        ‖(((rvmOrdinate q : ℂ) * I) + 5) *
          negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ))
            ((rvmOrdinate q : ℂ) * I)‖ ^ 2 ≤
          (6 * (N_cap : ℝ)) * (250000 * ℓ ^ 2 / Real.log (y + 2)) := by
      calc ∑ q ∈ S, _
          ≤ ∑ _ ∈ S, (250000 * ℓ ^ 2 / Real.log (y + 2)) := Finset.sum_le_sum hpt
        _ = (S.card : ℝ) * (250000 * ℓ ^ 2 / Real.log (y + 2)) := by simp
        _ ≤ (6 * (N_cap : ℝ)) * (250000 * ℓ ^ 2 / Real.log (y + 2)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
    refine hsum_le.trans ?_
    have hlog3 : (1 : ℝ) ≤ Real.log (y + 2) := by
      have h3 : (1 : ℝ) ≤ Real.log 3 :=
        (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
      exact h3.trans (Real.log_le_log (by norm_num) (by linarith))
    have hN_le : (N_cap : ℝ) ≤ 4 * Real.log (y + 2) := by
      have hc_lt : (N_cap : ℝ) ≤ Real.log (y + 5) + 1 :=
        (Nat.ceil_lt_add_one (Real.log_nonneg (by linarith))).le
      have hsq : y + 5 ≤ (y + 2) ^ 2 := by nlinarith
      have hl2 : Real.log (y + 5) ≤ 2 * Real.log (y + 2) := by
        have := Real.log_le_log (by linarith) hsq
        rwa [Real.log_pow, Nat.cast_ofNat] at this
      linarith
    calc (6 * (N_cap : ℝ)) * (250000 * ℓ ^ 2 / Real.log (y + 2))
        ≤ (6 * (4 * Real.log (y + 2))) * (250000 * ℓ ^ 2 / Real.log (y + 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN_le (by norm_num)) (by positivity)
      _ = 6000000 * ℓ ^ 2 * (Real.log (y + 2) * (Real.log (y + 2))⁻¹) := by ring
      _ = 6000000 * ℓ ^ 2 := by rw [mul_inv_cancel₀ hlog_pos.ne', mul_one]

/-- **Divergence of the first ordinate moment under window crowding.** On any ordinate family
`γ : ι → ℝ` with logarithmic crowding in `[y - 1/4, y + 1/4]`, the first absolute ordinate moment
of `smoothedWallLogProfile ℓ` (`ℓ ≠ 0`) diverges. -/
theorem smoothedWallLogProfile_crowding_firstMoment_not_summable {ι : Type*} {γ : ι → ℝ}
    {c : ℝ} (hc : 0 < c)
    (hcrowd : ∀ᶠ y : ℝ in atTop, ∃ S : Finset ι,
      c * Real.log y ≤ S.card ∧ ∀ q ∈ S, |γ q - y| ≤ 1 / 4)
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    ¬ Summable (fun q : ι =>
      |γ q| *
        ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2) := by
  classical
  let g : ι → ℝ := fun q =>
    |γ q| * ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2
  intro hsum
  have hℓ2 : 0 < ℓ ^ 2 := sq_pos_of_ne_zero hℓ
  have hsat := smoothedWallLogProfile_window_crowding_lower_bound (h := 1 / 4)
    (by norm_num) hc hcrowd ℓ
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hsat
  let N₀ : ℕ := max ⌈Y₀⌉₊ 2
  have hex_n : ∀ n : ℕ, ∃ S : Finset ι, N₀ ≤ n →
      (∀ q ∈ S, |γ q - (n : ℝ)| ≤ 1 / 4) ∧
      (c * ℓ ^ 2) / (4 * (n : ℝ)) ≤ ∑ q ∈ S, g q := by
    intro n
    by_cases hn : N₀ ≤ n
    · have hnY : Y₀ ≤ (n : ℝ) :=
        (Nat.le_ceil Y₀).trans (by exact_mod_cast (le_max_left ⌈Y₀⌉₊ 2).trans hn)
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right ⌈Y₀⌉₊ 2).trans hn
      obtain ⟨S, hS_win, hS_lb⟩ := hY₀ (n : ℝ) hnY
      refine ⟨S, fun _ => ⟨hS_win, ?_⟩⟩
      have hle_sum : (n : ℝ) ^ 2 * (∑ q ∈ S,
          ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2) ≤
          (2 * (n : ℝ)) * ∑ q ∈ S, g q := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun q hq => ?_
        have hd := (abs_le.mp (hS_win q hq)).1
        have hγ_ge : (n : ℝ) / 2 ≤ |γ q| := (by linarith : (n : ℝ) / 2 ≤ γ q).trans (le_abs_self _)
        have hm := mul_le_mul_of_nonneg_left hγ_ge (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))
        have hZ_nn : 0 ≤
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 :=
          sq_nonneg _
        dsimp only [g]
        have hm2 := mul_le_mul_of_nonneg_right hm hZ_nn
        linarith [show 2 * (n : ℝ) * ((n : ℝ) / 2) *
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 =
          (n : ℝ) ^ 2 *
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 by ring,
          show 2 * (n : ℝ) * |γ q| *
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2 =
          2 * (n : ℝ) * (|γ q| *
            ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((γ q : ℂ) * I)‖ ^ 2) by ring]
      rw [div_le_iff₀ (by linarith)]
      linarith [hS_lb.trans hle_sum,
        show (∑ q ∈ S, g q) * (4 * (n : ℝ)) = 2 * ((2 * (n : ℝ)) * ∑ q ∈ S, g q) by ring]
    · exact ⟨∅, fun h => absurd h hn⟩
  choose S_nat hS_nat using hex_n
  let ε : ℝ := c * ℓ ^ 2 / 16
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hsum.hasSum ε hε)
  let B : ℕ := max N₀ ((∑ q ∈ S₀, (⌈|γ q|⌉₊ + 2)) + 2)
  have hB_ge_N₀ : N₀ ≤ B := le_max_left _ _
  have hB_ge2 : 2 ≤ B := (le_max_right ⌈Y₀⌉₊ 2).trans hB_ge_N₀
  have hB_pos : 0 < (B : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hB_ge2)
  have hS₀_lt : ∀ q ∈ S₀, |γ q| + 1 < (B : ℝ) := fun q hq => by
    have h1 : ⌈|γ q|⌉₊ + 2 ≤ ∑ r ∈ S₀, (⌈|γ r|⌉₊ + 2) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq
    have h2 : (⌈|γ q|⌉₊ : ℝ) + 2 + 2 ≤ (B : ℝ) := by
      have : (⌈|γ q|⌉₊ + 2) + 2 ≤ B := (Nat.add_le_add_right h1 2).trans (le_max_right _ _)
      exact_mod_cast this
    linarith [Nat.le_ceil |γ q|]
  let I_B : Finset ℕ := Finset.Ico B (2 * B)
  let T : Finset ι := I_B.biUnion S_nat
  have hdisj : Disjoint S₀ T := by
    rw [Finset.disjoint_left]
    intro q hq₀ hqT
    obtain ⟨n, hnI, hqn⟩ := Finset.mem_biUnion.mp hqT
    have hn_ge_B : B ≤ n := (Finset.mem_Ico.mp hnI).1
    have hn_real : (B : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_B
    have hd := (abs_le.mp ((hS_nat n (hB_ge_N₀.trans hn_ge_B)).1 q hqn)).1
    have hlt := hS₀_lt q hq₀
    linarith [le_abs_self (γ q)]
  have hpair : (I_B : Set ℕ).PairwiseDisjoint S_nat := by
    intro n₁ hn₁ n₂ hn₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq₁ hq₂
    have hn₁_ge : N₀ ≤ n₁ := hB_ge_N₀.trans (Finset.mem_Ico.mp (Finset.mem_coe.mp hn₁)).1
    have hn₂_ge : N₀ ≤ n₂ := hB_ge_N₀.trans (Finset.mem_Ico.mp (Finset.mem_coe.mp hn₂)).1
    have hd₁ := abs_le.mp ((hS_nat n₁ hn₁_ge).1 q hq₁)
    have hd₂ := abs_le.mp ((hS_nat n₂ hn₂_ge).1 q hq₂)
    have hclose : |(n₁ : ℝ) - (n₂ : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hge1 : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      linarith [(abs_le.mp hclose).1]
    · have hge1 : (n₂ : ℝ) + 1 ≤ (n₁ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      linarith [(abs_le.mp hclose).2]
  have hd0 := hS₀ S₀ le_rfl
  have hd1 := hS₀ (S₀ ∪ T) Finset.subset_union_left
  rw [Real.dist_eq] at hd0 hd1
  change |∑ q ∈ S₀, g q - _| < ε at hd0
  change |∑ q ∈ S₀ ∪ T, g q - _| < ε at hd1
  rw [Finset.sum_union hdisj] at hd1
  have hub_T : ∑ q ∈ T, g q < 2 * ε := by
    linarith [(abs_lt.mp hd0).1, (abs_lt.mp hd0).2, (abs_lt.mp hd1).1, (abs_lt.mp hd1).2]
  have hlb_T : c * ℓ ^ 2 / 8 ≤ ∑ q ∈ T, g q := by
    rw [Finset.sum_biUnion hpair]
    have hterm : ∀ n ∈ I_B, (c * ℓ ^ 2) / (8 * (B : ℝ)) ≤ ∑ q ∈ S_nat n, g q := fun n hn => by
      have hn_ge : N₀ ≤ n := hB_ge_N₀.trans (Finset.mem_Ico.mp hn).1
      have hn_lt : (n : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp hn).2.le
      exact (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)).trans
        (hS_nat n hn_ge).2
    have hsum_le := Finset.sum_le_sum hterm
    have hcard : I_B.card = B := by dsimp only [I_B]; rw [Nat.card_Ico]; omega
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum_le
    refine le_trans ?_ hsum_le
    field_simp [hB_pos.ne']
  dsimp only [ε] at hub_T
  linarith

/-- Divergence of the first ordinate moment of `smoothedWallLogProfile ℓ` (`ℓ ≠ 0`) on `RvmCopy`. -/
theorem smoothedWallLogProfile_rvmOrdinate_firstMoment_not_summable {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    ¬ Summable (fun q : RvmCopy =>
      |rvmOrdinate q| *
        ‖negativeHalfLineLaplace (cx (smoothedWallLogProfile ℓ)) ((rvmOrdinate q : ℂ) * I)‖ ^ 2) := by
  obtain ⟨c, hc, hcr⟩ := rvmOrdinate_crowding (by norm_num : (0 : ℝ) < 1 / 4)
  exact smoothedWallLogProfile_crowding_firstMoment_not_summable hc hcr hℓ

/-- **Every positive half-line confinement ratio `R > 0` admits a variational ground state
sustaining the logarithmic wall cusp.** -/
theorem exists_halfLineMinimizer_sustaining_wallCusp {R : ℝ} (hR : 0 < R) :
    ∃ F : ℝ → ℝ, IsHalfLineEnergyMinimizer R F ∧
      0 < 8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) ∧
      Tendsto (fun h : ℝ => Real.log (1 / h) / h * ∫ u in Ioo (-h) 0, F u ^ 2)
        (𝓝[>] 0) (𝓝 (8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) ∧
      Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0, F u ^ 2) / h) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (x * Real.log x) *
        ∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖ ^ 2)
        atTop (𝓝 (8 * Real.pi * criticalAliasCoefficient R *
          (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) := by
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  have ha := criticalAliasCoefficient_positive hR
  have hM_eq : (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) = criticalHalfLineExponentialPair F F := by
    unfold criticalHalfLineExponentialPair
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have hM_pos : 0 < ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
    hM_eq ▸ exponentialPair_self_pos hF.1 (by rw [hF.2.1]; exact one_ne_zero)
  exact ⟨F, hF, by positivity,
    halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq hR hF,
    halfLineEnergyMinimizer_mean_square_wall_trace_zero hR hF,
    halfLineEnergyMinimizer_tendsto_mul_log_vertical_laplace_sq hR hF⟩

#print axioms criticalHalfLineEnergyDomain_smoothedWallLogProfile
#print axioms smoothedWallLogProfile_tendsto_terminal_sq
#print axioms smoothedWallLogProfile_no_vanishing_cusp_subsequence
#print axioms smoothedWallLogProfile_tendsto_mul_log_dampedMass
#print axioms smoothedWallLogProfile_tendsto_mul_log_vertical_laplace_sq
#print axioms smoothedWallLogProfile_mean_square_wall_trace_zero
#print axioms smoothedWallLogProfile_weighted_sq_increment_div_zero
#print axioms norm_rescaled_laplace_smoothedWallLogProfile_le
#print axioms smoothedWallLogProfile_axis_lipschitz
#print axioms tendsto_axis_laplace_smoothedWallLogProfile
#print axioms tendsto_sq_axis_laplace_smoothedWallLogProfile
#print axioms smoothedWallLogProfile_local_critical_line_mass
#print axioms smoothedWallLogProfile_poisson_row_bound
#print axioms smoothedWallLogProfile_window_crowding_lower_bound
#print axioms smoothedWallLogProfile_saturates_criticalLine_under_finiteOffLine
#print axioms rvmOrdinate_crowding
#print axioms smoothedWallLogProfile_rvmOrdinate_unit_window_bound
#print axioms smoothedWallLogProfile_crowding_firstMoment_not_summable
#print axioms smoothedWallLogProfile_rvmOrdinate_firstMoment_not_summable
#print axioms exists_halfLineMinimizer_sustaining_wallCusp

end GaloisForLFunctions.ExclusionOfTheCriticalState
