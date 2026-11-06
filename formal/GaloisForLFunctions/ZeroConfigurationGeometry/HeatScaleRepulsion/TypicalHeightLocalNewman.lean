import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TypicalHeightUniformReality
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TypicalZetaWindowBounds
import GaloisForLFunctions.RHTower.Heat.TheLocalDeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.DeBruijnStripThreshold
import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver

/-!
# The local Newman constant on typical unit windows

Typical-height saddle control covers the small-heat interval. Its upper
end overlaps the unconditional large-height reality horizon. Together
with the global eighth-time bound, this controls every later heat time,
as required by the definition of the local Newman constant.
-/

open Complex Filter Topology Set MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The typical-height saddle and the global horizon cover every later heat time. -/
theorem eventually_riemannHeat_zeros_real_of_zetaPolylogTypical {η : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, zetaTypicalHeight η (zetaPolylogLevel T) T t →
      ∀ X : ℝ, |X - t| ≤ η → ∀ τ : ℝ, 0 < τ →
      8 * η ≤ τ * (horizontalSlope X).re →
      ∀ z : ℂ, z.re = X → riemannHeat τ z = 0 → z.im = 0 := by
  obtain ⟨X₀, hglobal⟩ := riemannHeat_zeros_real_twoThirds (ε := 1 / 3) (by norm_num)
  filter_upwards [eventually_riemannHeat_ne_zero_of_zetaPolylogTypical hη hη8,
    eventually_ge_atTop (|X₀| + 202)] with T hsmall hT
  intro t h X hXt τ hτ hprod z hre hz
  have hXt' := (abs_le.mp hXt).1
  have hXbig : |X₀| + 200 ≤ X := by linarith only [hT, h.1.1, hXt', hη8]
  have hX : 0 < X := by linarith only [hXbig, abs_nonneg X₀]
  have hzabs : |z.re| = X := by rw [hre, abs_of_pos hX]
  rcases le_or_gt (1 / 8) τ with h8 | h8
  · exact ((mem_realRootedTimes_iff hτ.le).mpr (newmanConstant_lt_eighth.le.trans h8)).2 z hz
  by_cases hc2 : 2 * τ * (horizontalSlope X).re ≤ 2
  · by_contra him
    have hne := hsmall t h X hXt τ hτ h8.le (by linarith only [hprod]) hc2
      z.im him (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hτ.le hz)
    have hrepr : (X : ℂ) + I * z.im = z := by
      apply Complex.ext <;> simp [← hre]
    exact hne (by rw [hrepr]; exact hz)
  · apply hglobal τ hτ h8.le z hz
    · rw [hzabs]
      linarith only [hXbig, le_abs_self X₀]
    · have hexp : (2 / 3 + 1 / 3 : ℝ) / τ ≤ 2 * (horizontalSlope X).re := by
        rw [div_le_iff₀ hτ]
        nlinarith only [not_le.mp hc2]
      calc
        _ ≤ 2 * Real.pi * Real.exp (2 * (horizontalSlope X).re) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
        _ = X := (height_eq hX).symm
        _ = |z.re| := hzabs.symm

/-- A typical unit window has an all-future-time Newman bound with arbitrary small coefficient. -/
theorem eventually_localNewmanConstant_le_of_zetaPolylogTypicalWindow {η : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ X ∈ Icc T (2 * T), zetaPolylogTypicalWindow η T X →
      localNewmanConstant X ≤ 16 * η / Real.log ((X - 1) / (2 * Real.pi)) := by
  filter_upwards [eventually_riemannHeat_zeros_real_of_zetaPolylogTypical hη hη8,
    eventually_ge_atTop (2 * Real.pi * Real.exp 1 + 2)] with T hfuture hT
  intro X hXT hwindow
  let L := Real.log ((X - 1) / (2 * Real.pi))
  let s := 16 * η / L
  have hπ : 0 < 2 * Real.pi := by positivity
  have hratio : Real.exp 1 ≤ (X - 1) / (2 * Real.pi) := by
    rw [le_div_iff₀ hπ]
    linarith only [hT, hXT.1]
  have hratio0 : 0 < (X - 1) / (2 * Real.pi) := (Real.exp_pos 1).trans_le hratio
  have hL1 : 1 ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using hh
  have hL : 0 < L := by linarith only [hL1]
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsL : s * L = 16 * η := by dsimp only [s]; rw [div_mul_cancel₀ _ hL.ne']
  apply localNewmanConstant_le
  refine ⟨hs.le, ?_⟩
  intro τ hsτ z hz hzx
  obtain ⟨t, htyp, hnear⟩ := hwindow z.re hzx
  have hY : X - 1 ≤ z.re := by linarith only [(abs_le.mp hzx).1]
  have hα : L ≤ 2 * (horizontalSlope z.re).re := by
    have hh := Real.log_le_log hratio0 (div_le_div_of_nonneg_right hY hπ.le)
    rw [horizontalSlope_re]
    dsimp only [L] at hh ⊢
    linarith only [hh]
  have hα0 : 0 ≤ (horizontalSlope z.re).re := by linarith only [hα, hL1]
  have hstart : 8 * η ≤ s * (horizontalSlope z.re).re := by
    have hh := mul_le_mul_of_nonneg_left hα hs.le
    nlinarith only [hh, hsL]
  have hprod : 8 * η ≤ τ * (horizontalSlope z.re).re :=
    hstart.trans (mul_le_mul_of_nonneg_right hsτ hα0)
  exact hfuture t htyp z.re hnear τ (hs.trans_le hsτ) hprod z rfl hz

private theorem eventually_log_le_twice_window_log :
    ∀ᶠ X : ℝ in atTop, 0 < Real.log ((X - 1) / (2 * Real.pi)) ∧
      Real.log X ≤ 2 * Real.log ((X - 1) / (2 * Real.pi)) := by
  filter_upwards [eventually_ge_atTop (Real.exp (2 * Real.log (4 * Real.pi))),
    eventually_ge_atTop (2 : ℝ)] with X he hX
  have hX0 : 0 < X := by linarith only [hX]
  have hπ : 0 < 2 * Real.pi := by positivity
  have h4π : 0 < 4 * Real.pi := by positivity
  have hlogπ : 0 < Real.log (4 * Real.pi) := Real.log_pos (by linarith only [Real.pi_gt_three])
  have hlogX : 2 * Real.log (4 * Real.pi) ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hdiv : X / (4 * Real.pi) ≤ (X - 1) / (2 * Real.pi) := by
    rw [div_le_div_iff₀ h4π hπ]
    nlinarith only [mul_le_mul_of_nonneg_right hX Real.pi_pos.le]
  have hlower : Real.log X - Real.log (4 * Real.pi) ≤
      Real.log ((X - 1) / (2 * Real.pi)) := by
    rw [← Real.log_div hX0.ne' h4π.ne']
    exact Real.log_le_log (by positivity) hdiv
  exact ⟨by linarith only [hlogπ, hlogX, hlower], by linarith only [hlogX, hlower]⟩

/-- The normalized local Newman constant is arbitrarily small on typical unit windows. -/
theorem eventually_localNewman_scaled_le_of_zetaPolylogTypicalWindow {η : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, ∀ X ∈ Icc T (2 * T), zetaPolylogTypicalWindow η T X →
      localNewmanConstant X * Real.log X ≤ 32 * η := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp eventually_log_le_twice_window_log
  filter_upwards [eventually_localNewmanConstant_le_of_zetaPolylogTypicalWindow hη hη8,
    eventually_ge_atTop X₀, eventually_ge_atTop (8 : ℝ)] with T hbound hT₀ hT
  intro X hXT hwindow
  obtain ⟨hL, hlog⟩ := hX₀ X (hT₀.trans hXT.1)
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith only [hT, hXT.1])
  calc
    _ ≤ (16 * η / Real.log ((X - 1) / (2 * Real.pi))) * Real.log X :=
      mul_le_mul_of_nonneg_right (hbound X hXT hwindow) hlog0
    _ = 16 * η * Real.log X / Real.log ((X - 1) / (2 * Real.pi)) := by ring
    _ ≤ 32 * η := by
      rw [div_le_iff₀ hL]
      nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * η by positivity)]

/-- Above every fixed positive normalized level, exceptional unit windows have vanishing dyadic density. -/
theorem eventually_volume_localNewman_scaled_gt_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ε < localNewmanConstant X * Real.log X} ≤
        ENNReal.ofReal (δ * T) := by
  let η := min (ε / 64) (1 / 16)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη8 : η ≤ 1 / 8 := (min_le_right _ _).trans (by norm_num)
  have hηε : 32 * η ≤ ε := by
    have hh : η ≤ ε / 64 := min_le_left _ _
    linarith only [hh, hε]
  filter_upwards [eventually_localNewman_scaled_le_of_zetaPolylogTypicalWindow hη hη8,
    eventually_volume_not_zetaPolylogTypicalWindow_le hη hδ] with T hbound hbad
  refine (measure_mono ?_).trans hbad
  rintro X ⟨hXT, hlarge⟩
  refine ⟨hXT, fun hwindow => ?_⟩
  exact (not_lt_of_ge ((hbound X hXT hwindow).trans hηε)) hlarge

/-- The actual local Newman constant, normalized by `log X`, tends to zero in density. -/
theorem eventually_volume_localNewman_scaled_gt_inter_Icc_le {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ H : ℝ in atTop,
      volume ({X | ε < localNewmanConstant X * Real.log X} ∩ Icc 0 H) ≤
        ENNReal.ofReal (δ * H) := by
  apply eventually_volume_inter_Icc_le_of_window (γ := 0) ?_ hδ
  intro κ hκ
  have hhalf : Tendsto (fun V : ℝ => V / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  filter_upwards [hhalf.eventually (eventually_volume_localNewman_scaled_gt_le hε hκ),
    eventually_ge_atTop (0 : ℝ)] with V hv hV
  have hset : {X | ε < localNewmanConstant X * Real.log X} ∩ Icc ((V - 0) / 2) V =
      {X | X ∈ Icc (V / 2) (2 * (V / 2)) ∧ ε < localNewmanConstant X * Real.log X} := by
    ext X
    simp only [mem_inter_iff, mem_setOf_eq, sub_zero, show 2 * (V / 2) = V by ring, and_comm]
  rw [hset]
  refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith only [mul_nonneg hκ.le hV]

#print axioms eventually_localNewmanConstant_le_of_zetaPolylogTypicalWindow
#print axioms eventually_volume_localNewman_scaled_gt_inter_Icc_le

end

end GaloisForLFunctions.ZeroConfigurationGeometry
