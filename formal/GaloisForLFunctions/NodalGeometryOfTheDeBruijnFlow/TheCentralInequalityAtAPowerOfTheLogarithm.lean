import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheCentralInequalityOnAlmostAllHeights
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheEnvelopesAtAPowerOfTheLogarithm
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensityLong
import GaloisForLFunctions.RHTower.ZetaTypicalScaleBounds

/-!
# The central inequality down to a power of the logarithm

The density-one statements hold with an explicit rate. Put `L = 1 + log 4T` and `η_T = L^{−1/5}`. Outside a set of `X ∈ [T, 2T]` of measure `≪ T η_T¹⁴ = T L^{−14/5}`:

* for `17 η_T ≤ t log(x/2π) ≤ 1` the real zeros in the unit window are `≫ 1/log x` apart (`exists_central_inequality_at_power_of_log`);
* the local Newman constant satisfies `Λ_X log X ≤ 32 η_T`
  (`exists_volume_localNewman_gt_power_of_log_le`).

So the part of the time axis on which the central inequality is open at a typical height shrinks from `t log X ≍ 1` to `t log X ≪ (log X)^{−1/5}`, that is `τ = t log² X ≪ (log X)^{4/5}`.

The exceptional set has two sources. Large values of `ζ` near the height cost `T/L³`. A zero of `ζ` at depth `η_T/4` costs far less: Selberg's exponential density gives `T e^{−c L^{4/5}}` (`exists_volume_zetaZeroShadow_at_box_le`). The net over the unit window costs the factor `1/η_T`.

The exponent `1/5` is what the envelope `b ≍ log L/η²` of the logarithmic derivative on a box permits: the Gaussian width `1/√L` must not feel it, so `η ≫ L^{−1/4}` up to a logarithm.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The scale -/

/-- The logarithmic scale `L = 1 + log 4T` of a dyadic block. -/
def scaleLog (T : ℝ) : ℝ := 1 + Real.log (4 * T)

/-- The root `u = L^{1/20}`. -/
def scaleRoot (T : ℝ) : ℝ := scaleLog T ^ ((1 : ℝ) / 20)

/-- The size `η_T = 1/u⁴ = L^{−1/5}` of the zero-free box. -/
def boxSize (T : ℝ) : ℝ := 1 / scaleRoot T ^ 4

theorem tendsto_scaleLog : Tendsto scaleLog atTop atTop :=
  tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num)))

theorem scaleRoot_pow {T : ℝ} (h : 0 ≤ scaleLog T) : scaleRoot T ^ 20 = scaleLog T := by
  unfold scaleRoot
  rw [← Real.rpow_natCast, ← Real.rpow_mul h]
  norm_num

theorem boxSize_eq {T : ℝ} (h : 0 < scaleLog T) : boxSize T = scaleLog T ^ (-(1 / 5) : ℝ) := by
  unfold boxSize scaleRoot
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.le, Real.rpow_neg h.le, one_div]
  norm_num

/-- The largeness of the scale, for all large `T`. -/
theorem eventually_scale :
    ∀ᶠ T : ℝ in atTop, 1002 ≤ T ∧ (10 : ℝ) ^ 9 ≤ scaleRoot T ∧ scaleRoot T ^ 20 = scaleLog T ∧
      scaleLog T ^ 5 ≤ T := by
  have hdec := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp tendsto_scaleLog
  have hsmall : 0 < Real.exp (-1) / 4 := by positivity
  filter_upwards [eventually_ge_atTop (1002 : ℝ), tendsto_scaleLog.eventually_ge_atTop (((10 : ℝ) ^ 9) ^ 20),
    hdec.eventually (eventually_le_nhds hsmall)] with T hT hL hd
  have hL0 : 0 ≤ scaleLog T := le_trans (by positivity) hL
  have hpow := scaleRoot_pow hL0
  refine ⟨hT, ?_, hpow, ?_⟩
  · rw [← hpow] at hL
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hL0 _) (by norm_num)).mp hL
  · simp only [Function.comp] at hd
    have hT0 : 0 < T := by linarith only [hT]
    have he : Real.exp (-scaleLog T) = Real.exp (-1) / (4 * T) := by
      unfold scaleLog
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity)]
      rfl
    rw [he] at hd
    have h2 : scaleLog T ^ 5 * (Real.exp (-1) / (4 * T)) = (scaleLog T ^ 5 / T) * (Real.exp (-1) / 4) := by
      field_simp
    rw [h2] at hd
    have h3 : scaleLog T ^ 5 / T ≤ 1 := by
      have h4 : (scaleLog T ^ 5 / T) * (Real.exp (-1) / 4) ≤ 1 * (Real.exp (-1) / 4) := by
        rw [one_mul]
        exact hd
      exact le_of_mul_le_mul_right h4 hsmall
    rwa [div_le_one hT0] at h3

/-- The slope at a height of the block is comparable to the scale. -/
theorem slope_bounds {T x : ℝ} (hT : 1002 ≤ T) (hL : 100 ≤ scaleLog T) (hx1 : T - 1 ≤ x) (hx2 : x ≤ 2 * T + 1) :
    scaleLog T / 8 ≤ (horizontalSlope x).re ∧ (horizontalSlope x).re ≤ (scaleLog T - 1) / 2 := by
  rw [horizontalSlope_re]
  have hx0 : 0 < x := by linarith only [hT, hx1]
  have hT0 : 0 < T := by linarith only [hT]
  have hpi := Real.pi_pos
  have hπ : 0 < 2 * Real.pi := by positivity
  constructor
  · have h1 : 4 * T / (16 * Real.pi) ≤ x / (2 * Real.pi) := by
      rw [div_le_div_iff₀ (by positivity) hπ]
      have h4 : T / 2 ≤ x := by linarith only [hx1, hT]
      nlinarith only [mul_le_mul_of_nonneg_right h4 hpi.le]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (by positivity) (by positivity)] at h2
    have h3 : Real.log (16 * Real.pi) ≤ 63 :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only [Real.pi_lt_four])
    unfold scaleLog at hL ⊢
    linarith only [h2, h3, hL]
  · have h1 : x / (2 * Real.pi) ≤ 4 * T := by
      refine (div_le_self hx0.le (by nlinarith only [Real.pi_gt_three])).trans ?_
      linarith only [hx2, hT]
    have h2 := Real.log_le_log (by positivity) h1
    unfold scaleLog
    linarith only [h2]

/-- The elementary comparisons between the powers of `u`. -/
theorem scale_powers {u : ℝ} (hu : (10 : ℝ) ^ 9 ≤ u) :
    0 < u ∧ (0 : ℝ) < 1 / u ^ 4 ∧ (1 : ℝ) / u ^ 4 ≤ 1 / 8 ∧ (808 : ℝ) ≤ u ^ 20 ∧ u ^ 4 + 4 ≤ u ^ 20 / 8 ∧
      2 * u ^ 4 ≤ u ^ 20 := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by norm_num) hu
  have h16 : (1000 : ℝ) ≤ u ^ 16 := le_trans (le_trans (by norm_num) hu) (le_self_pow₀ hu1 (by norm_num))
  have h4 : u ≤ u ^ 4 := le_self_pow₀ hu1 (by norm_num)
  have h41 : (1000 : ℝ) ≤ u ^ 4 := le_trans (le_trans (by norm_num) hu) h4
  have h20 : u ^ 20 = u ^ 4 * u ^ 16 := by ring
  have h5 := mul_le_mul_of_nonneg_left h16 (by positivity : 0 ≤ u ^ 4)
  refine ⟨hu0, by positivity, one_div_le_one_div_of_le (by norm_num) (by linarith only [h41]), ?_, ?_, ?_⟩
  · nlinarith only [h20, h5, h41]
  · nlinarith only [h20, h5, h41]
  · nlinarith only [h20, h5, h41]

/-! ## The gap and the reality of the zeros at the scale -/

/-- **The gap at the scale.** On a typical unit window at the size `η_T`, for `17 η_T ≤ 2τα ≤ 1`, real zeros are `≫ 1/α` apart. -/
theorem eventually_gap_ge_at_power_of_log :
    ∀ᶠ T : ℝ in atTop, ∀ X ∈ Icc T (2 * T), zetaPolylogTypicalWindow (boxSize T) T X →
      ∀ τ x x' : ℝ, 0 < τ → |x - X| ≤ 1 / 2 → 17 * boxSize T ≤ 2 * τ * (horizontalSlope x).re →
        2 * τ * (horizontalSlope x).re ≤ 1 → x < x' →
        riemannHeat τ (x : ℂ) = 0 → riemannHeat τ (x' : ℂ) = 0 →
        1 / (20 * Real.exp 7) / (horizontalSlope x).re ≤ x' - x := by
  filter_upwards [eventually_scale] with T hscale
  obtain ⟨hT, hu, hL, hL5⟩ := hscale
  intro X hXT hwin τ x x' hτ hxX hc1 hc2 hxx' hx0 hx'0
  have hηdef : boxSize T = 1 / scaleRoot T ^ 4 := rfl
  set u := scaleRoot T with hudef
  obtain ⟨hu0, hη0, hη8, h808, hu4, h2u4⟩ := scale_powers hu
  have hL808 : 808 ≤ scaleLog T := by rw [← hL]; exact h808
  have h3 := abs_le.mp hxX
  have hxlo : T - 1 / 2 ≤ x := by linarith only [hXT.1, h3.1]
  have hxhi : x ≤ 2 * T + 1 := by linarith only [hXT.2, h3.2]
  obtain ⟨hα1, hα2⟩ := slope_bounds hT (by linarith only [hL808]) (by linarith only [hxlo]) hxhi
  have hT8 : 8 ≤ T := by linarith only [hT]
  have hL1 : 1 ≤ scaleLog T := by linarith only [hL808]
  have hLT : scaleLog T ≤ scaleLog T ^ 5 := le_self_pow₀ hL1 (by norm_num)
  have hα101 : 101 ≤ (horizontalSlope x).re := by linarith only [hα1, hL808]
  rw [hηdef] at hc1
  have hη1 : 1 / (1 / u ^ 4) = u ^ 4 := one_div_one_div _
  refine gap_ge_of_typical_data (η := 1 / u ^ 4) hη0 hη8 hT ?_ hxlo hα101 ?_ ?_ ?_ hτ hc1 hc2 hxx' hx0 hx'0
  · rw [div_eq_mul_one_div, hη1]
    linarith only [h2u4, hL, hLT, hL5]
  · rw [hη1]
    linarith only [hu4, hL, hα1]
  · intro β hβ1 hβ2 hs h16 h2
    have hs' : u ^ 20 / 8 ≤ β := by
      unfold scaleLog at hL
      rw [hL]
      linarith only [hs]
    have hβL : β ≤ u ^ 20 := by linarith only [hβ2, hα2, hL, hL808]
    have hβ8 : 8 ≤ β := by linarith only [hs', h808]
    obtain ⟨hE, hS, -, hB⟩ := typical_errors_at_power_of_log hu hT8 (by rw [hL]; rfl) hs' hβL hτ
      (by nlinarith only [h2, hβ8, hτ]) h16 h2
    exact ⟨hE, hS, hB⟩
  · intro ξ hξ
    have hwin' : zetaPolylogTypicalWindow (1 / u ^ 4) T X := hwin
    refine hwin' ξ ?_
    have h1 : 2 * (1 / (horizontalSlope x).re) ≤ 1 / 2 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 101) hα101
      linarith only [this]
    have h2 := abs_le.mp hξ
    rw [abs_le]
    constructor <;> linarith only [h1, h2.1, h2.2, h3.1, h3.2]

/-- **Reality at the scale.** Near a typical height at the size `η_T`, every zero is real for all `τ` with `8 η_T ≤ τ α`. -/
theorem eventually_zeros_real_at_power_of_log :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, zetaTypicalHeight (boxSize T) (zetaPolylogLevel T) T t →
      ∀ X : ℝ, |X - t| ≤ boxSize T → ∀ τ : ℝ, 0 < τ → 8 * boxSize T ≤ τ * (horizontalSlope X).re →
      ∀ z : ℂ, z.re = X → riemannHeat τ z = 0 → z.im = 0 := by
  obtain ⟨X₀, hglobal⟩ := riemannHeat_zeros_real_twoThirds (ε := 1 / 3) (by norm_num)
  filter_upwards [eventually_scale, eventually_ge_atTop (|X₀| + 202)] with T hscale hTX₀
  obtain ⟨hT, hu, hL, hL5⟩ := hscale
  intro t h X hXt τ hτ hprod z hre hz
  have hηdef : boxSize T = 1 / scaleRoot T ^ 4 := rfl
  rw [hηdef] at h hXt hprod
  set u := scaleRoot T with hudef
  obtain ⟨hu0, hη0, hη8, h808, hu4, h2u4⟩ := scale_powers hu
  have hL808 : 808 ≤ scaleLog T := by rw [← hL]; exact h808
  have hXt' := abs_le.mp hXt
  have hXlo : T - 1 ≤ X := by linarith only [h.1.1, hXt'.1, hη8]
  have hXhi : X ≤ 2 * T + 1 := by linarith only [h.1.2, hXt'.2, hη8]
  have hXbig : |X₀| + 200 ≤ X := by linarith only [hTX₀, hXlo]
  have hX : 200 ≤ X := by linarith only [hXbig, abs_nonneg X₀]
  have hX0 : 0 < X := by linarith only [hX]
  have hzabs : |z.re| = X := by rw [hre, abs_of_pos hX0]
  obtain ⟨hα1, hα2⟩ := slope_bounds hT (by linarith only [hL808]) hXlo hXhi
  rcases le_or_gt (1 / 8) τ with h8 | h8
  · exact ((mem_realRootedTimes_iff hτ.le).mpr (newmanConstant_lt_eighth.le.trans h8)).2 z hz
  by_cases hc2 : 2 * τ * (horizontalSlope X).re ≤ 2
  · by_contra him
    have hs' : u ^ 20 / 8 ≤ (horizontalSlope X).re := by rw [hL]; exact hα1
    have hαL : (horizontalSlope X).re ≤ u ^ 20 := by linarith only [hα2, hL, hL808]
    have hα8 : 8 ≤ (horizontalSlope X).re := by linarith only [hs', h808]
    have hc : 16 * (1 / u ^ 4) ≤ 2 * τ * (horizontalSlope X).re := by linarith only [hprod]
    obtain ⟨hE, hS, hO, -⟩ := typical_errors_at_power_of_log hu (by linarith only [hT]) (by rw [hL]; rfl) hs' hαL hτ
      h8.le hc hc2
    have hne := riemannHeat_ne_zero_of_typical_errors h hη0 hη8 (by linarith only [hT]) hX hXt hτ h8.le
      (by linarith only [hα8]) hc hc2 him (abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hτ.le hz)
      (window_fits h8.le hτ hX0 (by linarith only [hα8])) hE (by linarith only [hS, hα8]) hO
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
        _ = X := (height_eq hX0).symm
        _ = |z.re| := hzabs.symm

/-- **The local Newman constant at the scale.** On a typical unit window at the size `η_T`, `Λ_X log X ≤ 32 η_T`. -/
theorem eventually_localNewman_at_power_of_log :
    ∀ᶠ T : ℝ in atTop, ∀ X ∈ Icc T (2 * T), zetaPolylogTypicalWindow (boxSize T) T X →
      localNewmanConstant X * Real.log X ≤ 32 * boxSize T := by
  filter_upwards [eventually_zeros_real_at_power_of_log, eventually_scale] with T hfuture hscale
  obtain ⟨hT, hu, -, -⟩ := hscale
  intro X hXT hwindow
  have hηdef : boxSize T = 1 / scaleRoot T ^ 4 := rfl
  obtain ⟨-, hη0', hη8', -, -, -⟩ := scale_powers hu
  rw [← hηdef] at hη0' hη8'
  set η := boxSize T with hη
  have hπ : 0 < 2 * Real.pi := by positivity
  have hpi4 := Real.pi_lt_four
  have hX1000 : 1002 ≤ X := hT.trans hXT.1
  set W := Real.log ((X - 1) / (2 * Real.pi)) with hW
  have hratio : Real.exp 1 ≤ (X - 1) / (2 * Real.pi) := by
    rw [le_div_iff₀ hπ]
    have he := Real.exp_one_lt_d9
    nlinarith only [he, hX1000, hpi4, Real.pi_pos, mul_pos (Real.exp_pos 1) Real.pi_pos,
      mul_lt_mul_of_pos_right hpi4 (Real.exp_pos 1)]
  have hratio0 : 0 < (X - 1) / (2 * Real.pi) := (Real.exp_pos 1).trans_le hratio
  have hW1 : 1 ≤ W := by
    have hh := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using hh
  have hW0 : 0 < W := by linarith only [hW1]
  set s := 16 * η / W with hs
  have hspos : 0 < s := by positivity
  have hsW : s * W = 16 * η := by rw [hs, div_mul_cancel₀ _ hW0.ne']
  have hmem : localNewmanConstant X ≤ s := by
    apply localNewmanConstant_le
    refine ⟨hspos.le, ?_⟩
    intro τ hsτ z hz hzx
    obtain ⟨t, htyp, hnear⟩ := hwindow z.re hzx
    have hY : X - 1 ≤ z.re := by linarith only [(abs_le.mp hzx).1]
    have hα : W ≤ 2 * (horizontalSlope z.re).re := by
      have hh := Real.log_le_log hratio0 (div_le_div_of_nonneg_right hY hπ.le)
      rw [horizontalSlope_re]
      linarith only [hh, hW]
    have hα0 : 0 ≤ (horizontalSlope z.re).re := by linarith only [hα, hW1]
    have hstart : 8 * η ≤ s * (horizontalSlope z.re).re := by
      have hh := mul_le_mul_of_nonneg_left hα hspos.le
      nlinarith only [hh, hsW]
    have hprod : 8 * η ≤ τ * (horizontalSlope z.re).re :=
      hstart.trans (mul_le_mul_of_nonneg_right hsτ hα0)
    exact hfuture t htyp z.re hnear τ (hspos.trans_le hsτ) hprod z rfl hz
  have hX0 : 0 < X := by linarith only [hX1000]
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith only [hX1000])
  -- `log X ≤ 2W`
  have hlog : Real.log X ≤ 2 * W := by
    have h1 : X / (4 * Real.pi) ≤ (X - 1) / (2 * Real.pi) := by
      rw [div_le_div_iff₀ (by positivity) hπ]
      nlinarith only [mul_nonneg Real.pi_pos.le (by linarith only [hX1000] : 0 ≤ 2 * X - 4)]
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div hX0.ne' (by positivity)] at h2
    have h3 : Real.log ((4 * Real.pi) ^ 2) ≤ Real.log X := by
      refine Real.log_le_log (by positivity) ?_
      have h4 : (4 * Real.pi) ^ 2 ≤ 16 ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hpi4]) 2
      linarith only [h4, hX1000]
    rw [Real.log_pow] at h3
    norm_num at h3
    linarith only [h2, h3]
  calc localNewmanConstant X * Real.log X ≤ s * Real.log X := mul_le_mul_of_nonneg_right hmem hlogX0
    _ ≤ s * (2 * W) := mul_le_mul_of_nonneg_left hlog hspos.le
    _ = 32 * η := by rw [show s * (2 * W) = 2 * (s * W) by ring, hsW]; ring

/-! ## The exceptional set -/

/-- The zeros of `ζ` at depth `2a/log U` over the middle of a dyadic block, with Selberg's exponential saving. -/
theorem exists_volume_zetaZeroShadow_block_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop, ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U →
      volume (zetaZeroShadow (1 / 2 + 2 * a / Real.log U) 2 ∩ Icc (U / 4 + 3) (U / 2 - 3)) ≤
        ENNReal.ofReal (4 * (Real.log U / a) * (U / 4 * (A * Real.exp (-(a / 14))) + K * Real.log U)) := by
  classical
  obtain ⟨A, K, hA, hK, hsel⟩ := exists_selberg_exponential_nearLine_zeroDensity_long
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hsel, eventually_ge_atTop (100 : ℝ)] with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  intro a ha1 ha2
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith only [hU100])
  have ha0 : 0 < a := by linarith only [ha1]
  have hT₁20 : 20 ≤ T₁ := by linarith only [hT₁.1, hU100]
  have hT12 : T₁ < T₂ := by linarith only [hT₁.2, hT₂.1, hU100]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zc := Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re) with hZc
  have hdepth : 0 < 2 * a / Real.log U := by positivity
  have hsub : zetaZeroShadow (1 / 2 + 2 * a / Real.log U) 2 ∩ Icc (U / 4 + 3) (U / 2 - 3) ⊆
      ⋃ w ∈ Zc, Icc (w.im - 2) (w.im + 2) := by
    rintro t ⟨⟨w, hw0, hwa, hwt⟩, ht⟩
    have hw1 : w.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hw0
    have hwt' := abs_le.mp hwt
    have hZw : w ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith only [hwa, hdepth], by linarith only [hw1]⟩,
        ⟨by linarith only [ht.1, hT₁.2, hwt'.1], by linarith only [ht.2, hT₂.1, hwt'.2]⟩⟩, hw0⟩
    exact mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hZw, hwa⟩, ⟨by linarith only [hwt'.2], by linarith only [hwt'.1]⟩⟩
  have hcard : (Zc.card : ℝ) ≤ ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith only [hwbox.2.1, hT₁20]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  have hsum0 : 0 ≤ ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hmass := hc a ha1 ha2 Z hZ
  set S := ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) with hS
  have hexp0 : 0 ≤ A * Real.exp (-(a / 14)) := by positivity
  have hTT : T₂ - T₁ ≤ U / 4 := by linarith only [hT₁.1, hT₂.2]
  have hS2 : a / Real.log U * S ≤ U / 4 * (A * Real.exp (-(a / 14))) + K * Real.log U := by
    have h1 : a / Real.log U * S ≤ 2 * Real.pi * (a / Real.log U * S) := by
      have h2 : 0 ≤ a / Real.log U * S := by positivity
      nlinarith only [h2, Real.pi_gt_three]
    have h3 := mul_le_mul_of_nonneg_right hTT hexp0
    linarith only [h1, hmass, h3]
  have hS3 : S ≤ Real.log U / a * (U / 4 * (A * Real.exp (-(a / 14))) + K * Real.log U) := by
    have hratio : 0 < Real.log U / a := by positivity
    have h1 := mul_le_mul_of_nonneg_left hS2 hratio.le
    have h2 : Real.log U / a * (a / Real.log U * S) = S := by
      field_simp
    linarith only [h1, h2]
  calc volume (zetaZeroShadow (1 / 2 + 2 * a / Real.log U) 2 ∩ Icc (U / 4 + 3) (U / 2 - 3))
      ≤ volume (⋃ w ∈ Zc, Icc (w.im - 2) (w.im + 2)) := measure_mono hsub
    _ ≤ ∑ w ∈ Zc, volume (Icc (w.im - 2) (w.im + 2)) := measure_biUnion_finset_le _ _
    _ = ∑ w ∈ Zc, ENNReal.ofReal 4 := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ = ENNReal.ofReal (4 * Zc.card) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), mul_comm]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hcard.trans hS3
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4)
        linarith only [h2]

/-- `u⁶⁴ ≤ e^y` once `y ≥ u¹⁶/224`. -/
theorem pow_le_exp_of_le {u y : ℝ} (hu : 1120 ≤ u) (hy : u ^ 16 / 224 ≤ y) : u ^ 64 ≤ Real.exp y := by
  have hu0 : 0 < u := by linarith only [hu]
  have hu1 : (1 : ℝ) ≤ u := by linarith only [hu]
  have h1 : u ^ 15 ≤ y / 5 := by
    have h2 : u ^ 15 * 1120 ≤ u ^ 15 * u := mul_le_mul_of_nonneg_left hu (by positivity)
    have h3 : u ^ 15 * u = u ^ 16 := by ring
    linarith only [h2, h3, hy]
  have h2 : y / 5 ≤ Real.exp (y / 5) := by
    have := Real.add_one_le_exp (y / 5)
    linarith only [this]
  have h3 : Real.exp y = Real.exp (y / 5) ^ 5 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3]
  calc u ^ 64 ≤ u ^ 75 := pow_le_pow_right₀ hu1 (by norm_num)
    _ = (u ^ 15) ^ 5 := by ring
    _ ≤ Real.exp (y / 5) ^ 5 := pow_le_pow_left₀ (by positivity) (h1.trans h2) 5

/-- The value of the block bound at the depth `η/4`. -/
theorem block_value_le {A K u T U : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hu : (10 : ℝ) ^ 9 ≤ u) (hu84 : u ^ 84 ≤ T)
    (hU : U / 4 ≤ 2 * T) (hlog1 : u ^ 20 / 2 ≤ Real.log U) (hlog2 : Real.log U ≤ u ^ 20) :
    4 * (Real.log U / (1 / u ^ 4 * Real.log U / 8)) *
        (U / 4 * (A * Real.exp (-((1 / u ^ 4 * Real.log U / 8) / 14))) + K * Real.log U) ≤
      (64 * A + 32 * K) * T / u ^ 60 := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hlog0 : 0 < Real.log U := lt_of_lt_of_le (by positivity) hlog1
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hu84
  have hratio : Real.log U / (1 / u ^ 4 * Real.log U / 8) = 8 * u ^ 4 := by
    field_simp
  rw [hratio]
  set a := 1 / u ^ 4 * Real.log U / 8 with ha
  have hexp : Real.exp (-(a / 14)) ≤ 1 / u ^ 64 := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (by positivity) (pow_le_exp_of_le (le_trans (by norm_num) hu) ?_)
    have h1 : u ^ 16 / 224 = 1 / u ^ 4 * (u ^ 20 / 2) / 8 / 14 := by
      field_simp
      ring
    rw [h1, ha]
    have h2 := mul_le_mul_of_nonneg_left hlog1 (by positivity : 0 ≤ 1 / u ^ 4)
    linarith only [h2]
  have hUnn : U / 4 * (A * Real.exp (-(a / 14))) ≤ 2 * T * (A * (1 / u ^ 64)) := by
    refine mul_le_mul hU (mul_le_mul_of_nonneg_left hexp hA.le) (by positivity) (by positivity)
  have hK2 : K * Real.log U ≤ K * u ^ 20 := mul_le_mul_of_nonneg_left hlog2 hK
  have h3 : 4 * (8 * u ^ 4) * (U / 4 * (A * Real.exp (-(a / 14))) + K * Real.log U) ≤
      4 * (8 * u ^ 4) * (2 * T * (A * (1 / u ^ 64)) + K * u ^ 20) :=
    mul_le_mul_of_nonneg_left (add_le_add hUnn hK2) (by positivity)
  refine h3.trans ?_
  have h4 : 4 * (8 * u ^ 4) * (2 * T * (A * (1 / u ^ 64)) + K * u ^ 20) =
      64 * A * T / u ^ 60 + 32 * K * u ^ 24 := by
    field_simp
    ring
  have h5 : 32 * K * u ^ 24 ≤ 32 * K * T / u ^ 60 := by
    rw [le_div_iff₀ (by positivity)]
    have h6 := mul_le_mul_of_nonneg_left hu84 (by positivity : 0 ≤ 32 * K)
    calc 32 * K * u ^ 24 * u ^ 60 = 32 * K * u ^ 84 := by ring
      _ ≤ 32 * K * T := h6
  rw [h4, add_mul, add_div]
  exact add_le_add le_rfl h5

/-- **Zeros of `ζ` at the depth of the box.** Their shadow costs at most `≪ T/L³`. -/
theorem exists_volume_zetaZeroShadow_at_box_le :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ T : ℝ in atTop,
      volume (zetaZeroShadow (1 / 2 + boxSize T / 4) 2 ∩ Icc T (2 * T)) ≤
        ENNReal.ofReal (B * T / scaleRoot T ^ 60) := by
  obtain ⟨A, K, hA, hK, hblock⟩ := exists_volume_zetaZeroShadow_block_le
  refine ⟨2 * (64 * A + 32 * K), by positivity, ?_⟩
  have ht1 : Tendsto (fun T : ℝ => 4 * T - 12) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))
  have ht2 : Tendsto (fun T : ℝ => 4 * T + 6) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [ht1.eventually hblock, ht2.eventually hblock, eventually_scale] with T h1 h2 hscale
  obtain ⟨hT, hu, hL, hL5⟩ := hscale
  have hηdef : boxSize T = 1 / scaleRoot T ^ 4 := rfl
  rw [hηdef]
  set u := scaleRoot T with hudef
  obtain ⟨hu0, hη0, hη8, h808, hu4, h2u4⟩ := scale_powers hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by norm_num) hu
  have hLbig : (808 : ℝ) ≤ scaleLog T := by rw [← hL]; exact h808
  have hT0 : 0 < T := by linarith only [hT]
  have hu84 : u ^ 84 ≤ T := by
    have h3 : u ^ 84 ≤ (u ^ 20) ^ 5 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hu1 (by norm_num)
    rw [hL] at h3
    exact h3.trans hL5
  -- the data of a block whose top height is comparable to `4T`
  have hblockT (U : ℝ) (hU1 : 2 * T ≤ U) (hU2 : U ≤ 8 * T)
      (hbound : ∀ a : ℝ, 1 ≤ a → 2 * a + 2 ≤ Real.log U →
        volume (zetaZeroShadow (1 / 2 + 2 * a / Real.log U) 2 ∩ Icc (U / 4 + 3) (U / 2 - 3)) ≤
          ENNReal.ofReal (4 * (Real.log U / a) * (U / 4 * (A * Real.exp (-(a / 14))) + K * Real.log U))) :
      volume (zetaZeroShadow (1 / 2 + 1 / u ^ 4 / 4) 2 ∩ Icc (U / 4 + 3) (U / 2 - 3)) ≤
        ENNReal.ofReal ((64 * A + 32 * K) * T / u ^ 60) := by
    have hU0 : 0 < U := by linarith only [hU1, hT0]
    have hlogupper : Real.log U ≤ u ^ 20 := by
      have h3 : Real.log U ≤ Real.log (4 * T * 2) := Real.log_le_log hU0 (by linarith only [hU2])
      rw [Real.log_mul (by positivity) (by norm_num)] at h3
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith only [this]
      rw [hL]
      unfold scaleLog
      linarith only [h3, h4]
    have hloglower : u ^ 20 / 2 ≤ Real.log U := by
      have h3 : Real.log (4 * T / 2) ≤ Real.log U := Real.log_le_log (by positivity) (by linarith only [hU1])
      rw [Real.log_div (by positivity) (by norm_num)] at h3
      have h4 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith only [this]
      rw [hL]
      unfold scaleLog
      unfold scaleLog at hLbig
      linarith only [h3, h4, hLbig]
    have hlog0 : 0 < Real.log U := by linarith only [hloglower, h808]
    set a := 1 / u ^ 4 * Real.log U / 8 with ha
    have hdepth : 2 * a / Real.log U = 1 / u ^ 4 / 4 := by
      rw [ha]
      field_simp
      ring
    have ha1 : 1 ≤ a := by
      have h3 : 1 / u ^ 4 * (u ^ 20 / 2) ≤ 1 / u ^ 4 * Real.log U :=
        mul_le_mul_of_nonneg_left hloglower hη0.le
      have h4 : 1 / u ^ 4 * (u ^ 20 / 2) = u ^ 16 / 2 := by
        field_simp
      have h5 : (1000 : ℝ) ≤ u ^ 16 := le_trans (le_trans (by norm_num) hu) (le_self_pow₀ hu1 (by norm_num))
      rw [ha]
      linarith only [h3, h4, h5]
    have ha2 : 2 * a + 2 ≤ Real.log U := by
      have h3 : 1 / u ^ 4 * Real.log U ≤ 1 / 8 * Real.log U := mul_le_mul_of_nonneg_right hη8 hlog0.le
      rw [ha]
      linarith only [h3, hloglower, h808]
    have hb := hbound a ha1 ha2
    rw [hdepth] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    exact block_value_le hA hK hu hu84 (by linarith only [hU2]) hloglower hlogupper
  have hb1 := hblockT (4 * T - 12) (by linarith only [hT]) (by linarith only [hT]) h1
  have hb2 := hblockT (4 * T + 6) (by linarith only [hT]) (by linarith only [hT]) h2
  have hcover : zetaZeroShadow (1 / 2 + 1 / u ^ 4 / 4) 2 ∩ Icc T (2 * T) ⊆
      (zetaZeroShadow (1 / 2 + 1 / u ^ 4 / 4) 2 ∩ Icc ((4 * T - 12) / 4 + 3) ((4 * T - 12) / 2 - 3)) ∪
      (zetaZeroShadow (1 / 2 + 1 / u ^ 4 / 4) 2 ∩ Icc ((4 * T + 6) / 4 + 3) ((4 * T + 6) / 2 - 3)) := by
    rintro t ⟨hs, ht⟩
    rcases le_total t (2 * T - 9) with h | h
    · exact Or.inl ⟨hs, by linarith only [ht.1], by linarith only [h]⟩
    · exact Or.inr ⟨hs, by linarith only [h, hT], by linarith only [ht.2]⟩
  refine (measure_mono hcover).trans ((measure_union_le _ _).trans ((add_le_add hb1 hb2).trans ?_))
  have hval : 0 ≤ (64 * A + 32 * K) * T / u ^ 60 := by positivity
  rw [← ENNReal.ofReal_add hval hval]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- **The non-typical heights.** Their measure is `≪ T/L³`. -/
theorem exists_volume_not_typical_at_box_le :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ T : ℝ in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight (boxSize T) (zetaPolylogLevel T) T t} ≤
        ENNReal.ofReal (B * T / scaleRoot T ^ 60) := by
  obtain ⟨B₁, hB₁, hshadow⟩ := exists_volume_zetaZeroShadow_at_box_le
  obtain ⟨B₂, hB₂, hlarge⟩ := exists_volume_zetaLargeNear_polylog_le
  refine ⟨B₁ + B₂, by positivity, ?_⟩
  filter_upwards [hshadow, eventually_scale] with T hs hscale
  obtain ⟨hT, hu, hL, hL5⟩ := hscale
  have hT1 : 1 < T := by linarith only [hT]
  have hL808 : (808 : ℝ) ≤ scaleRoot T ^ 20 := (scale_powers hu).2.2.2.1
  rw [hL] at hL808
  have hl3 : 3 ≤ Real.log (4 * T) := by
    unfold scaleLog at hL808
    linarith only [hL808]
  have hlarge' := hlarge T (by linarith only [hT]) hl3
  have hcover : {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight (boxSize T) (zetaPolylogLevel T) T t} ⊆
      (zetaZeroShadow (1 / 2 + boxSize T / 4) 2 ∩ Icc T (2 * T)) ∪
        zetaLargeNear T ((1 + Real.log (4 * T)) ^ (4 : ℕ)) := by
    rintro t ⟨ht, hnot⟩
    by_contra hcon
    rw [mem_union, not_or] at hcon
    refine hnot ⟨ht, fun h => hcon.1 ⟨h, ht⟩, ?_⟩
    rw [rpow_zetaPolylogLevel hT1]
    exact hcon.2
  refine (measure_mono hcover).trans ((measure_union_le _ _).trans ((add_le_add hs hlarge').trans ?_))
  have hu0 : 0 < scaleRoot T := (scale_powers hu).1
  have hT0 : 0 < T := by linarith only [hT]
  have h3 : (1 + Real.log (4 * T)) ^ (3 : ℕ) = scaleRoot T ^ 60 := by
    change scaleLog T ^ 3 = _
    rw [← hL]
    ring
  rw [h3, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- The net: a height with a non-typical unit window has a non-typical point in a fixed finite family of translates. -/
theorem volume_not_window_le {η T w : ℝ} (hη : 0 < η) (hw : 0 ≤ w)
    (hbad : volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η (zetaPolylogLevel T) T t} ≤ ENNReal.ofReal w) :
    volume {X | X ∈ Icc T (2 * T) ∧ ¬ zetaPolylogTypicalWindow η T X} ≤
      ENNReal.ofReal ((2 / η + 1) * (w + 2)) := by
  classical
  set N := {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η (zetaPolylogLevel T) T t} with hN
  set S : Set ℝ := N ∪ (Icc (T - 1) T ∪ Icc (2 * T) (2 * T + 1)) with hS
  have hSvol : volume S ≤ ENNReal.ofReal (w + 2) := by
    refine (measure_union_le _ _).trans ?_
    have h1 : volume (Icc (T - 1) T ∪ Icc (2 * T) (2 * T + 1)) ≤ ENNReal.ofReal 2 := by
      refine (measure_union_le _ _).trans ?_
      rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith only) (by linarith only)]
      exact ENNReal.ofReal_le_ofReal (by linarith only)
    refine (add_le_add hbad h1).trans ?_
    rw [← ENNReal.ofReal_add hw (by norm_num)]
  set n := ⌊2 / η⌋₊ + 1 with hn
  have hcover : {X | X ∈ Icc T (2 * T) ∧ ¬ zetaPolylogTypicalWindow η T X} ⊆
      ⋃ m ∈ Finset.range n, (fun X : ℝ => X + ((m : ℝ) * η - 1)) ⁻¹' S := by
    rintro X ⟨hX, hnot⟩
    unfold zetaPolylogTypicalWindow at hnot
    push Not at hnot
    obtain ⟨Y, hYX, hfar⟩ := hnot
    have hYX' := abs_le.mp hYX
    set q := (Y - X + 1) / η with hq
    have hq0 : 0 ≤ q := div_nonneg (by linarith only [hYX'.1]) hη.le
    have hq2 : q ≤ 2 / η := div_le_div_of_nonneg_right (by linarith only [hYX'.2]) hη.le
    set m := ⌊q⌋₊ with hm
    have hm1 : (m : ℝ) ≤ q := Nat.floor_le hq0
    have hm2 : q < (m : ℝ) + 1 := Nat.lt_floor_add_one q
    have hqη : q * η = Y - X + 1 := by
      rw [hq]
      field_simp
    have hmη1 : (m : ℝ) * η ≤ Y - X + 1 := by
      rw [← hqη]
      exact mul_le_mul_of_nonneg_right hm1 hη.le
    have hmη2 : Y - X + 1 < ((m : ℝ) + 1) * η := by
      rw [← hqη]
      exact mul_lt_mul_of_pos_right hm2 hη
    have hmrange : m ∈ Finset.range n := by
      rw [Finset.mem_range, hn]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor hq2)
    refine mem_iUnion₂.mpr ⟨m, hmrange, ?_⟩
    change X + ((m : ℝ) * η - 1) ∈ S
    set t := X + ((m : ℝ) * η - 1) with ht
    have hmη0 : 0 ≤ (m : ℝ) * η := by positivity
    have hdist : |Y - t| ≤ η := by
      rw [abs_le, ht]
      constructor
      · linarith only [hmη1, hη]
      · have h1 : ((m : ℝ) + 1) * η = (m : ℝ) * η + η := by ring
        linarith only [hmη2, h1]
    have hnt : ¬ zetaTypicalHeight η (zetaPolylogLevel T) T t := fun h =>
      absurd hdist (not_le.mpr (hfar t h))
    rw [hS]
    rcases lt_or_ge t T with hlt | hge
    · exact Or.inr (Or.inl ⟨by rw [ht]; linarith only [hX.1, hmη0], hlt.le⟩)
    rcases lt_or_ge (2 * T) t with hgt | hle
    · refine Or.inr (Or.inr ⟨hgt.le, ?_⟩)
      have h2 : (m : ℝ) * η ≤ 2 := by
        have h3 : (m : ℝ) * η ≤ q * η := mul_le_mul_of_nonneg_right hm1 hη.le
        linarith only [h3, hqη, hYX'.2]
      rw [ht]
      linarith only [hX.2, h2]
    · exact Or.inl ⟨⟨hge, hle⟩, hnt⟩
  refine (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hcard : (n : ℝ) ≤ 2 / η + 1 := by
    rw [hn]
    push_cast
    have := Nat.floor_le (by positivity : 0 ≤ 2 / η)
    linarith only [this]
  have hterm (m : ℕ) : volume ((fun X : ℝ => X + ((m : ℝ) * η - 1)) ⁻¹' S) ≤ ENNReal.ofReal (w + 2) := by
    rw [measure_preimage_add_right]
    exact hSvol
  calc ∑ m ∈ Finset.range n, volume ((fun X : ℝ => X + ((m : ℝ) * η - 1)) ⁻¹' S)
      ≤ ∑ _m ∈ Finset.range n, ENNReal.ofReal (w + 2) := Finset.sum_le_sum fun m _ => hterm m
    _ = ENNReal.ofReal ((n : ℝ) * (w + 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- **The exceptional set at the scale.** The heights whose unit window fails to be typical at the size `η_T` have measure at most `≪ T η_T¹⁴`. -/
theorem exists_volume_not_window_at_box_le :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ zetaPolylogTypicalWindow (boxSize T) T X} ≤
        ENNReal.ofReal (B * T * boxSize T ^ 14) := by
  obtain ⟨B, hB, hbad⟩ := exists_volume_not_typical_at_box_le
  refine ⟨3 * B + 9, by positivity, ?_⟩
  filter_upwards [hbad, eventually_scale] with T h1 hscale
  obtain ⟨hT, hu, hL, hL5⟩ := hscale
  have hηdef : boxSize T = 1 / scaleRoot T ^ 4 := rfl
  set u := scaleRoot T with hudef
  obtain ⟨hu0, hη0, hη8, h808, hu4, h2u4⟩ := scale_powers hu
  have hu1 : (1 : ℝ) ≤ u := le_trans (by norm_num) hu
  have hT0 : 0 < T := by linarith only [hT]
  have hw0 : 0 ≤ B * T / u ^ 60 := by positivity
  rw [← hηdef] at hη0
  refine (volume_not_window_le hη0 hw0 h1).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hηdef]
  have h2 : 2 / (1 / u ^ 4) + 1 ≤ 3 * u ^ 4 := by
    have h3 : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ hu1
    rw [div_div_eq_mul_div, div_one]
    linarith only [h3]
  have hu60 : u ^ 60 ≤ T := by
    have h3 : u ^ 60 ≤ (u ^ 20) ^ 5 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hu1 (by norm_num)
    rw [hL] at h3
    exact h3.trans hL5
  have h3 : (2 : ℝ) ≤ 3 * T / u ^ 60 := by
    rw [le_div_iff₀ (by positivity)]
    have h4 : (0 : ℝ) < u ^ 60 := by positivity
    linarith only [hu60, h4, hT0]
  have h5 : (2 / (1 / u ^ 4) + 1) * (B * T / u ^ 60 + 2) ≤ 3 * u ^ 4 * (B * T / u ^ 60 + 3 * T / u ^ 60) :=
    mul_le_mul h2 (by linarith only [h3]) (by positivity) (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp
  ring

/-! ## The theorems -/

/-- **The central inequality down to a power of the logarithm.** There are absolute `c, A > 0` such that for large `T`, outside a set of measure at most `A T η_T¹⁴`, `η_T = (1 + log 4T)^{−1/5}`: for `17 η_T ≤ t log(x/2π) ≤ 1`, any two real zeros `x < x'` of `H_t` in the unit window satisfy `(x' − x)² ≥ c min(t, 1/log²(2 + |x|))`. -/
theorem exists_central_inequality_at_power_of_log :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ ¬ ∀ t x x' : ℝ, 0 < t → |x - X| ≤ 1 / 2 →
          17 * boxSize T ≤ t * Real.log (x / (2 * Real.pi)) → t * Real.log (x / (2 * Real.pi)) ≤ 1 → x < x' →
          riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
          c * min t (1 / Real.log (2 + |x|) ^ 2) ≤ (x' - x) ^ 2} ≤ ENNReal.ofReal (A * T * boxSize T ^ 14) := by
  set c₀ := 1 / (20 * Real.exp 7) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  obtain ⟨B, hB, hbad⟩ := exists_volume_not_window_at_box_le
  refine ⟨4 * c₀ ^ 2, B, by positivity, hB, ?_⟩
  filter_upwards [eventually_gap_ge_at_power_of_log, hbad, eventually_ge_atTop (1000 : ℝ), eventually_scale]
    with T hgap hbad hT hscale
  refine (measure_mono ?_).trans hbad
  rintro X ⟨hXT, hprop⟩
  refine ⟨hXT, fun hwin => hprop ?_⟩
  intro t x x' ht hx hκt ht1 hxx' h0 h0'
  have hxlo : T - 1 / 2 ≤ x := by linarith only [hXT.1, (abs_le.mp hx).1]
  have hxpos : 0 < x := by linarith only [hxlo, hT]
  have hslope : 2 * t * (horizontalSlope x).re = t * Real.log (x / (2 * Real.pi)) := by
    rw [horizontalSlope_re]
    ring
  have hg := hgap X hXT hwin t x x' ht hx (by rw [hslope]; exact hκt) (by rw [hslope]; exact ht1) hxx' h0 h0'
  have hη0 : 0 < boxSize T := (scale_powers hscale.2.1).2.1
  have hαL : 2 * (horizontalSlope x).re ≤ Real.log x := by
    rw [horizontalSlope_re]
    have h1 : x / (2 * Real.pi) ≤ x := div_le_self hxpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hαpos : 0 < (horizontalSlope x).re := by
    by_contra hn
    have h1 := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * t) (not_lt.mp hn)
    rw [hslope] at h1
    linarith only [h1, hκt, hη0]
  have hL2 : Real.log x ≤ Real.log (2 + |x|) := by
    apply Real.log_le_log hxpos
    have := le_abs_self x
    linarith only [this]
  have hLpos : 0 < Real.log (2 + |x|) := by linarith only [hαL, hαpos, hL2]
  have hg2 : 2 * c₀ / Real.log (2 + |x|) ≤ x' - x := by
    refine le_trans ?_ hg
    rw [div_le_div_iff₀ hLpos hαpos]
    have := mul_le_mul_of_nonneg_left (hαL.trans hL2) hc₀pos.le
    linarith only [this]
  have hsq : (2 * c₀ / Real.log (2 + |x|)) ^ 2 ≤ (x' - x) ^ 2 := pow_le_pow_left₀ (by positivity) hg2 2
  refine le_trans ?_ hsq
  have hmin : min t (1 / Real.log (2 + |x|) ^ 2) ≤ 1 / Real.log (2 + |x|) ^ 2 := min_le_right _ _
  refine (mul_le_mul_of_nonneg_left hmin (by positivity)).trans (le_of_eq ?_)
  field_simp
  norm_num

/-- **The rate of `Λ_X log X → 0` in density.** There is an absolute `A > 0` such that for large `T`, outside a set of measure at most `A T η_T¹⁴`, `Λ_X log X ≤ 32 η_T`, `η_T = (1 + log 4T)^{−1/5}`. -/
theorem exists_volume_localNewman_gt_power_of_log_le :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop,
      volume {X | X ∈ Icc T (2 * T) ∧ 32 * boxSize T < localNewmanConstant X * Real.log X} ≤
        ENNReal.ofReal (A * T * boxSize T ^ 14) := by
  obtain ⟨B, hB, hbad⟩ := exists_volume_not_window_at_box_le
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_localNewman_at_power_of_log, hbad] with T hbound hbad
  refine (measure_mono ?_).trans hbad
  rintro X ⟨hXT, hlarge⟩
  exact ⟨hXT, fun hwin => not_lt_of_ge (hbound X hXT hwin) hlarge⟩

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
