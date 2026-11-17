import GaloisForLFunctions.ExclusionOfTheCriticalState.TheAveragedStateDecaysAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateIsTheCauchyTransformOfItsZeroValues

/-!
# The heated profile beyond the wall grows at the rate of the zeros

For the critical state `F` and heat time `ε > 0` the heated profile beyond the wall is its zero modes
plus the heated confined state (`criticalState_hasSum_heated_zeroSeries`):

  `a F⁺_ε(T) = Σ_z L F(z) e^{εz² − zT} + a (e^{−8u} F)_ε(T)`.

The zero series converges absolutely (`criticalState_summable_norm_heatedZeroModes`): the Gaussian
factor `|e^{εz²}| ≤ e^{ε/4} e^{−ε(Im z)²}` is `O(1/|1 + z|)`, and `(L F(z))_z` is square-summable. For
`T ≥ 0` the heated confined state is bounded (`abs_heatedState_le_of_nonneg`). Hence
(`criticalState_norm_heatedBeyondWall_le`): if every centred zero has `Re z ≥ −κ`, `κ ≥ 0`, then

  `‖F⁺_ε(T)‖ ≤ C e^{κT}`,  `T ≥ 0`:

the averaged prime side grows at most at the rate of the zeros, mode by mode. The zero set is symmetric
under `z ↦ −z`, so the zero-free half-plane `Re s > 20999/24000` gives `Re z ≥ −8999/24000`
(`neg_seed_le_re_centredZero`) and `e^{−δT} F⁺_ε(T) → 0` for every `δ > 8999/24000`
(`criticalState_tendsto_damped_heatedBeyondWall`): a heated sub-strip Hardy wave below the width `½`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-! ### The Gaussian weights at the zeros -/

/-- `e^{−εy²} ≤ (3/2 + 1/(4ε))/(3/2 + |y|)`. -/
theorem exp_neg_mul_sq_le {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    Real.exp (-(ε * y ^ 2)) ≤ (3 / 2 + 1 / (4 * ε)) / (3 / 2 + |y|) := by
  have h1 : 1 + ε * y ^ 2 ≤ Real.exp (ε * y ^ 2) := by
    have := Real.add_one_le_exp (ε * y ^ 2); linarith
  have hy : |y| ≤ ε * y ^ 2 + 1 / (4 * ε) := by
    have h := sq_nonneg (2 * ε * |y| - 1)
    have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
    rw [show ε * y ^ 2 + 1 / (4 * ε) = (4 * ε ^ 2 * y ^ 2 + 1) / (4 * ε) by field_simp,
      le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : 3 / 2 + |y| ≤ (3 / 2 + 1 / (4 * ε)) * (1 + ε * y ^ 2) := by
    have : 0 ≤ 1 / (4 * ε) * (ε * y ^ 2) := by positivity
    nlinarith [sq_nonneg y]
  have hpos : 0 < 3 / 2 + |y| := by positivity
  rw [Real.exp_neg, le_div_iff₀ hpos]
  calc (Real.exp (ε * y ^ 2))⁻¹ * (3 / 2 + |y|)
      ≤ (Real.exp (ε * y ^ 2))⁻¹ * ((3 / 2 + 1 / (4 * ε)) * (1 + ε * y ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (Real.exp_pos _).le)
    _ ≤ (Real.exp (ε * y ^ 2))⁻¹ * ((3 / 2 + 1 / (4 * ε)) * Real.exp (ε * y ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity))
          (inv_nonneg.mpr (Real.exp_pos _).le)
    _ = 3 / 2 + 1 / (4 * ε) := by field_simp

/-- **The heat symbol at a centred zero.** `|e^{εz² − zT}| ≤ e^{ε/4} (3/2 + 1/(4ε)) |1 + z|⁻¹ e^{−T Re z}`. -/
theorem norm_stateHeatSymbol_centredZero_le {ε : ℝ} (hε : 0 < ε) (T : ℝ) (q : XiZeroCopy) :
    ‖stateHeatSymbol ε T (centredZero q)‖ ≤
      Real.exp (ε / 4) * (3 / 2 + 1 / (4 * ε)) * ‖((-1 : ℂ) - centredZero q)⁻¹‖ *
        Real.exp (-((centredZero q).re * T)) := by
  set z := centredZero q
  have hx := abs_lt.mp (abs_re_centredZero_lt q)
  have hre : ((ε : ℂ) * z ^ 2 - z * (T : ℂ)).re = ε * (z.re ^ 2 - z.im ^ 2) - z.re * T := by
    simp [sq, Complex.mul_re]
  have hx2 : z.re ^ 2 ≤ 1 / 4 := by nlinarith
  have hn : ‖(-1 : ℂ) - z‖ ≤ 3 / 2 + |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((-1 : ℂ) - z)
    have e1 : ((-1 : ℂ) - z).re = -1 - z.re := by simp
    have e2 : |((-1 : ℂ) - z).im| = |z.im| := by simp
    rw [e1, e2, abs_of_neg (by linarith)] at h
    linarith
  have hn0 : 0 < ‖(-1 : ℂ) - z‖ := by
    have h := Complex.abs_re_le_norm ((-1 : ℂ) - z)
    have e1 : ((-1 : ℂ) - z).re = -1 - z.re := by simp
    rw [e1, abs_of_neg (by linarith)] at h
    linarith
  have hy := exp_neg_mul_sq_le hε z.im
  have hy' : Real.exp (-(ε * z.im ^ 2)) ≤ (3 / 2 + 1 / (4 * ε)) * ‖((-1 : ℂ) - z)⁻¹‖ := by
    rw [norm_inv]
    refine hy.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hn0 hn) (by positivity)
  unfold stateHeatSymbol
  rw [Complex.norm_exp, hre]
  have e : ε * (z.re ^ 2 - z.im ^ 2) - z.re * T =
      ε * z.re ^ 2 + -(ε * z.im ^ 2) + -(z.re * T) := by ring
  rw [e, Real.exp_add, Real.exp_add]
  have h4 : Real.exp (ε * z.re ^ 2) ≤ Real.exp (ε / 4) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc Real.exp (ε * z.re ^ 2) * Real.exp (-(ε * z.im ^ 2)) * Real.exp (-(z.re * T))
      ≤ Real.exp (ε / 4) * ((3 / 2 + 1 / (4 * ε)) * ‖((-1 : ℂ) - z)⁻¹‖) *
          Real.exp (-(z.re * T)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h4 hy' (Real.exp_pos _).le (Real.exp_pos _).le)
          (Real.exp_pos _).le
    _ = _ := by ring

/-- The zero modes of the heated profile are absolutely summable. -/
theorem criticalState_summable_norm_heatedZeroModes {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    Summable fun q => ‖negativeHalfLineLaplace (cx F) (centredZero q) *
      stateHeatSymbol ε T (centredZero q)‖ := by
  have hp : ∀ q : XiZeroCopy, (1 / 2 : ℝ) ≤ ‖(-1 : ℂ) - centredZero q‖ := fun q => by
    have hre := (abs_lt.mp (abs_re_centredZero_lt q)).1
    have h := Complex.abs_re_le_norm ((-1 : ℂ) - centredZero q)
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re, abs_of_neg (by linarith)] at h
    linarith
  have hs := summable_norm_mul_inv_sub_centredZero
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) (by norm_num : (0 : ℝ) < 1 / 2) hp
  refine (hs.mul_left (Real.exp (ε / 4) * (3 / 2 + 1 / (4 * ε)) * Real.exp (|T| / 2))).of_nonneg_of_le
    (fun q => norm_nonneg _) (fun q => ?_)
  have hx := abs_lt.mp (abs_re_centredZero_lt q)
  have hT : Real.exp (-((centredZero q).re * T)) ≤ Real.exp (|T| / 2) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : |(centredZero q).re * T| ≤ 1 / 2 * |T| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_re_centredZero_lt q).le (abs_nonneg _)
    linarith [neg_abs_le ((centredZero q).re * T)]
  rw [norm_mul, norm_mul]
  calc ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ * ‖stateHeatSymbol ε T (centredZero q)‖
      ≤ ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ * (Real.exp (ε / 4) *
          (3 / 2 + 1 / (4 * ε)) * ‖((-1 : ℂ) - centredZero q)⁻¹‖ * Real.exp (|T| / 2)) :=
        mul_le_mul_of_nonneg_left ((norm_stateHeatSymbol_centredZero_le hε T q).trans
          (mul_le_mul_of_nonneg_left hT (by positivity))) (norm_nonneg _)
    _ = _ := by ring

/-! ### The heated confined state right of the wall -/

/-- For `T ≥ 0` the heated confined state is bounded: `|(e^{−8u}F)_ε(T)| ≤ k_ε(0) e^{64ε} ‖F‖₁`. -/
theorem abs_heatedState_le_of_nonneg {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T) :
    |heatedState ε F T| ≤
      (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (64 * ε) * ∫ u, |F u| := by
  unfold heatedState
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hF.integrable.abs.const_mul _)
    (Eventually.of_forall fun u => ?_)
  rcases le_or_gt 0 u with hu | hu
  · rw [hF.support u hu, mul_zero, mul_zero, norm_zero]
    exact mul_nonneg (by positivity) (abs_nonneg _)
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    unfold stateHeatKernel
    have hk : 0 ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) := by positivity
    rw [abs_of_nonneg (mul_nonneg hk (Real.exp_pos _).le)]
    have hexp : Real.exp (-((u - T) ^ 2 / (4 * ε))) * Real.exp (-(8 * u)) ≤ Real.exp (64 * ε) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : u ^ 2 ≤ (u - T) ^ 2 := by nlinarith
      have h2 : u ^ 2 / (4 * ε) ≤ (u - T) ^ 2 / (4 * ε) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      have h3 : 0 ≤ u ^ 2 / (4 * ε) + 8 * u + 64 * ε := by
        have e : u ^ 2 / (4 * ε) + 8 * u + 64 * ε = (u + 16 * ε) ^ 2 / (4 * ε) := by
          field_simp; ring
        rw [e]; positivity
      linarith
    calc (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (-((u - T) ^ 2 / (4 * ε))) *
          (Real.exp (-(8 * u)) * |F u|)
        = (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) *
            (Real.exp (-((u - T) ^ 2 / (4 * ε))) * Real.exp (-(8 * u))) * |F u| := by ring
      _ ≤ (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (64 * ε) * |F u| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hk) (abs_nonneg _)

/-! ### Growth at the rate of the zeros -/

/-- **The heated profile beyond the wall grows at the rate of the zeros.** If every centred zero
has `Re z ≥ −κ`, `κ ≥ 0`, then `‖F⁺_ε(T)‖ ≤ C e^{κT}` for `T ≥ 0`. -/
theorem criticalState_norm_heatedBeyondWall_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : ∀ q : XiZeroCopy, -κ ≤ (centredZero q).re) :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ‖heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T‖ ≤
        C * Real.exp (κ * T) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have hp : ∀ q : XiZeroCopy, (1 / 2 : ℝ) ≤ ‖(-1 : ℂ) - centredZero q‖ := fun q => by
    have hre := (abs_lt.mp (abs_re_centredZero_lt q)).1
    have h := Complex.abs_re_le_norm ((-1 : ℂ) - centredZero q)
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re, abs_of_neg (by linarith)] at h
    linarith
  have hs := summable_norm_mul_inv_sub_centredZero
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) (by norm_num : (0 : ℝ) < 1 / 2) hp
  set K : ℝ := Real.exp (ε / 4) * (3 / 2 + 1 / (4 * ε))
  set M : ℝ := ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q) *
    ((-1 : ℂ) - centredZero q)⁻¹‖
  set H : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (64 * ε) * ∫ u, |F u|
  have hK0 : 0 ≤ K := by positivity
  have hH0 : 0 ≤ H := by positivity
  refine ⟨(criticalAliasCoefficient W₀)⁻¹ * (K * M) + H, fun T hT => ?_⟩
  have hsum := criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε T
  -- the zero modes are bounded by `K M e^{κT}`
  have hb : ∀ q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q) *
      stateHeatSymbol ε T (centredZero q)‖ ≤
        K * Real.exp (κ * T) * ‖negativeHalfLineLaplace (cx F) (centredZero q) *
          ((-1 : ℂ) - centredZero q)⁻¹‖ := fun q => by
    have hT' : Real.exp (-((centredZero q).re * T)) ≤ Real.exp (κ * T) :=
      Real.exp_le_exp.mpr (by nlinarith [hκ q])
    rw [norm_mul, norm_mul]
    calc ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ * ‖stateHeatSymbol ε T (centredZero q)‖
        ≤ ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
            (K * ‖((-1 : ℂ) - centredZero q)⁻¹‖ * Real.exp (κ * T)) :=
          mul_le_mul_of_nonneg_left ((norm_stateHeatSymbol_centredZero_le hε T q).trans
            (mul_le_mul_of_nonneg_left hT' (by positivity))) (norm_nonneg _)
      _ = _ := by ring
  have hZ : ‖(criticalAliasCoefficient W₀ : ℂ) *
      (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ))‖ ≤ K * Real.exp (κ * T) * M := by
    rw [← hsum.tsum_eq, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm (criticalState_summable_norm_heatedZeroModes hW hthreshold hF
      hε T)).trans (Summable.tsum_le_tsum hb
        (criticalState_summable_norm_heatedZeroModes hW hthreshold hF hε T) (hs.mul_left _))
  have hH := abs_heatedState_le_of_nonneg hd hε hT
  have he1 : 1 ≤ Real.exp (κ * T) := Real.one_le_exp (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le] at hZ
  have hZ' : ‖heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)‖ ≤
      (criticalAliasCoefficient W₀)⁻¹ * (K * M) * Real.exp (κ * T) :=
    calc ‖heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)‖
        = (criticalAliasCoefficient W₀)⁻¹ * (criticalAliasCoefficient W₀ *
            ‖heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)‖) :=
          (inv_mul_cancel_left₀ ha.ne' _).symm
      _ ≤ (criticalAliasCoefficient W₀)⁻¹ * (K * Real.exp (κ * T) * M) :=
          mul_le_mul_of_nonneg_left hZ (inv_nonneg.mpr ha.le)
      _ = _ := by ring
  have hst : ‖((heatedState ε F T : ℝ) : ℂ)‖ ≤ H * Real.exp (κ * T) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hH.trans (le_mul_of_one_le_right hH0 he1)
  calc ‖heatedBeyondWall ε W₀ hd T‖
      = ‖(heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)) +
          ((heatedState ε F T : ℝ) : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)‖ +
          ‖((heatedState ε F T : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hZ' hst
    _ = _ := by ring

/-- The zeros are symmetric under `z ↦ −z`, so the zero-free half-plane `Re s > 20999/24000` also
bounds them from the left: `Re z ≥ −8999/24000`. -/
theorem neg_seed_le_re_centredZero (q : XiZeroCopy) : -(8999 / 24000 : ℝ) ≤ (centredZero q).re := by
  by_contra hlt
  have hgt : (centredZero q).re < -(8999 / 24000 : ℝ) := not_le.mp hlt
  have hxi : xi ((1 : ℂ) / 2 - centredZero q) = 0 := by
    rw [show (1 : ℂ) / 2 - centredZero q = 1 - (1 / 2 + centredZero q) by ring, xi_one_sub]
    exact xi_centredZero q
  have hre : ((1 : ℂ) / 2 - centredZero q).re = 1 / 2 - (centredZero q).re := by simp
  have hpos : 0 < ((1 : ℂ) / 2 - centredZero q).re := by
    rw [hre]; linarith [(abs_lt.mp (abs_re_centredZero_lt q)).2]
  have hne : (1 : ℂ) / 2 - centredZero q ≠ 1 := fun h => by
    have h1 := congrArg Complex.re h
    rw [hre, Complex.one_re] at h1
    have h2 := (abs_lt.mp (abs_re_centredZero_lt q)).1
    linarith
  have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hpos hne).mp hxi
  have hseed : (20999 / 24000 : ℝ) < ((1 : ℂ) / 2 - centredZero q).re := by rw [hre]; linarith
  exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
    hseed hζ

/-- **A heated sub-strip Hardy wave.** For every `δ > 8999/24000`, `e^{−δT} F⁺_ε(T) → 0` as
`T → ∞`. -/
theorem criticalState_tendsto_damped_heatedBeyondWall {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) {δ : ℝ}
    (hδ : 8999 / 24000 < δ) :
    Tendsto (fun T : ℝ => Real.exp (-(δ * T)) *
      ‖heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T‖) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := criticalState_norm_heatedBeyondWall_le hW hthreshold hF hε
    (κ := 8999 / 24000) (by norm_num) neg_seed_le_re_centredZero
  have h1 : Tendsto (fun T : ℝ => (δ - 8999 / 24000) * T) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  have h2 : Tendsto (fun T : ℝ => Real.exp (-((δ - 8999 / 24000) * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have hlim := h2.const_mul C
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun T => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  calc Real.exp (-(δ * T)) * ‖heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T‖
      ≤ Real.exp (-(δ * T)) * (C * Real.exp (8999 / 24000 * T)) :=
        mul_le_mul_of_nonneg_left (hC T hT) (Real.exp_pos _).le
    _ = C * Real.exp (-((δ - 8999 / 24000) * T)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
