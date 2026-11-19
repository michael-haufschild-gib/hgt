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
open MeasureTheory Set Filter Complex Topology intervalIntegral Zeta23
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
    rw [log_one_div_eq_neg_log]
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
      have hl3 : Real.log (1 / η) < η * Real.log (1 / h) := (div_lt_iff₀ hη0).mp hlogh_big
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
  have hlo : Tendsto (fun h : ℝ => ℓ ^ 2 * (1 - 8 * h) ^ 4 * J h) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
    have hc : Tendsto (fun h : ℝ => ℓ ^ 2 * (1 - 8 * h) ^ 4) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
      have hcont : Continuous fun h : ℝ => ℓ ^ 2 * (1 - 8 * h) ^ 4 := by fun_prop
      simpa using hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hc.mul hJ
  have hhi : Tendsto (fun h : ℝ => ℓ ^ 2 * J h) (𝓝[>] 0) (𝓝 (ℓ ^ 2)) := by
    simpa using hJ.const_mul (ℓ ^ 2)
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
      rw [wallLogProfile_of_mem (by linarith [hu.1]) hu.2, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1])]
    have hF2i : IntegrableOn (fun u => smoothedWallLogProfile ℓ u ^ 2) (Ioo (-h) 0) :=
      (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ).sq.integrableOn
    have hle_int : (ℓ ^ 2 * (1 - 8 * h) ^ 4) * (∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹) ≤
        ∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2 := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hfi.const_mul _) hF2i measurableSet_Ioo fun u hu => ?_
      rw [smoothedWallLogProfile_of_mem (by linarith [hu.1]) hu.2, mul_pow, mul_pow, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1]), ← mul_assoc]
      have hpow : (1 - 8 * h) ^ 4 ≤ (1 + 8 * u) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith [hu.1]) 4
      rw [show ((1 + 8 * u) ^ 2) ^ 2 = (1 + 8 * u) ^ 4 by ring]
      have hinv_nn : 0 ≤ (-Real.log (-u))⁻¹ :=
        inv_nonneg.mpr (by linarith [one_le_neg_log (by linarith [hu.2] : 0 < -u) (by linarith [hu.1])])
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
      rw [wallLogProfile_of_mem (by linarith [hu.1]) hu.2, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1])]
    have hF2i : IntegrableOn (fun u => smoothedWallLogProfile ℓ u ^ 2) (Ioo (-h) 0) :=
      (criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ).sq.integrableOn
    have hle_int : ∫ u in Ioo (-h) 0, smoothedWallLogProfile ℓ u ^ 2 ≤
        ℓ ^ 2 * ∫ u in Ioo (-h) 0, (-Real.log (-u))⁻¹ := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hF2i (hfi.const_mul _) measurableSet_Ioo fun u hu => ?_
      rw [smoothedWallLogProfile_of_mem (by linarith [hu.1]) hu.2, mul_pow, mul_pow, inv_pow,
        wallRootLog_sq (by linarith [hu.2]) (by linarith [hu.1])]
      have h1 : ((1 + 8 * u) ^ 2) ^ 2 ≤ 1 := by
        have hb : 0 ≤ 1 + 8 * u := by linarith [hu.1]
        have hu1 : 1 + 8 * u ≤ 1 := by linarith [hu.2]
        have hsq : (1 + 8 * u) ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg ((1 + 8 * u) ^ 2)]
      have hinv_nn : 0 ≤ (-Real.log (-u))⁻¹ :=
        inv_nonneg.mpr (by linarith [one_le_neg_log (by linarith [hu.2] : 0 < -u) (by linarith [hu.1])])
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
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h0 (Eventually.of_forall hpos)
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
  field_simp [hlog, hh0'.ne']

/-- Vanishing weighted `L²` increment quotient `h⁻¹ ∫ (F_ℓ(u) - F_ℓ(u + h))² e^{-8u} du → 0`,
matching `criticalState_tendsto_weighted_sq_increment_div`. -/
theorem smoothedWallLogProfile_weighted_sq_increment_div_zero (ℓ : ℝ) :
    Tendsto (fun h : ℝ => (∫ u : ℝ,
      (smoothedWallLogProfile ℓ u - smoothedWallLogProfile ℓ (u + h)) ^ 2 *
        Real.exp (-(8 * u))) / h) (𝓝[>] 0) (𝓝 0) := by
  have hd_full := criticalHalfLineEnergyDomain_smoothedWallLogProfile ℓ
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set K₀ := 64 * Real.exp 1 * (ℓ ^ 2 + 1)
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
  -- Smoothly partition at `-δ/2` and `-δ/4`: `χ = 0` on `(-∞, -δ/2]`, `χ = 1` on `[-δ/4, ∞)`.
  let χ : ℝ → ℝ := fun u => min (max (2 + 4 / δ * u) 0) 1
  have hχ0 : ∀ u, 0 ≤ χ u := fun _ => le_min (le_max_right _ _) zero_le_one
  have hχ1 : ∀ u, χ u ≤ 1 := fun _ => min_le_right _ _
  have hχ_left : ∀ u, u ≤ -(δ / 2) → χ u = 0 := fun u hu => by
    dsimp only [χ]
    have hm : 4 / δ * u ≤ -2 := by
      have h1 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 4 / δ)
      have he : 4 / δ * -(δ / 2) = -2 := by field_simp [hδ0.ne']; ring
      linarith
    rw [max_eq_right (by linarith), min_eq_left zero_le_one]
  have hχ_right : ∀ u, -(δ / 4) ≤ u → χ u = 1 := fun u hu => by
    dsimp only [χ]
    have hm : -1 ≤ 4 / δ * u := by
      have h1 := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 4 / δ)
      have he : 4 / δ * -(δ / 4) = -1 := by field_simp [hδ0.ne']; ring
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
      · rw [wallLogProfile_of_nonneg h0, wallLogProfile_of_nonneg h0, mul_zero, mul_zero, mul_zero]
      · rw [wallLogProfile_of_mem (by linarith) h0, wallLogProfile_of_mem (by linarith) h0]
        ring
  -- Truncated inverse root-logarithm on `[δ/4, 1/8]` is globally `(2/δ)`-Lipschitz on `ℝ`.
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
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
            field_simp [hδ0.ne']; ring
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
            rw [abs_of_nonneg (sub_nonneg.mpr hge)]
            field_simp [hδ0.ne']; ring
        _ ≤ (2 / δ) * |u - v| := mul_le_mul_of_nonneg_left (hcl_lip u v) (by positivity)
  let ψ_far : ℝ → ℝ := fun u => ℓ * ((1 - χ u) * collarSmoothCutoff u)
  have hfar_eq : ∀ u, F_far u = ψ_far u * w_tr u := fun u => by
    dsimp only [F_far, ψ_far, smoothedWallLogProfile, w_tr, cl]
    rcases le_or_gt u (-(1 / 8)) with hle | hgt
    · have hcut0 : collarSmoothCutoff u = 0 := by
        unfold collarSmoothCutoff
        rw [max_eq_right (by linarith), min_eq_left zero_le_one]
        norm_num
      rw [hcut0, zero_mul, mul_zero, mul_zero, mul_zero, mul_zero]
    · rcases le_or_gt (-(δ / 4)) u with hge | hlt
      · rw [hχ_right u hge, sub_self, zero_mul, zero_mul, zero_mul, zero_mul]
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
  -- Combine the `O((wallRootLog δ)⁻² · h)` jump bound of `wallLogProfile δ` with the `O(h²)`
  -- Lipschitz bounds on `(-1/8 - h, 0)`, where `e^{-8u} ≤ e` for `0 < h < 1/16`.
  set C_quad : ℝ := Real.exp 1 * (4 * Λ_near ^ 2 + 2 * Λ_far ^ 2)
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
  have hind_int : Integrable ((S_supp).indicator fun _ : ℝ => C_quad * h ^ 2) :=
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
      (4 * Real.exp 1 * ℓ ^ 2) * (wallLogProfile δ u - wallLogProfile δ (u + h)) ^ 2 +
        S_supp.indicator (fun _ => C_quad * h ^ 2) u := fun u => by
    by_cases hu_mem : u ∈ S_supp
    · rw [indicator_of_mem hu_mem]
      have hexp_le : Real.exp (-(8 * u)) ≤ Real.exp 1 := by
        have : -(8 * u) ≤ 2 := by linarith [hu_mem.1]
        -- Wait: on `Icc (-1/8 - h) 0` (`h < 1/16`), `-(8 * u) ≤ 8 * (3/16) = 3/2`! Let's check:
        rcases le_or_gt u (-(1 / 8) - h) with hout | hin
        · exfalso
          -- Actually we handle `u ≤ -(1/8) - h` before `hu_mem` so `-(8 * u) ≤ 8 * (3/16)`!
          linarith [hout, hin]
        · linarith
    · -- Let's check support `Icc (-(1/8) - h) 0` directly!
      sorry
  sorry
