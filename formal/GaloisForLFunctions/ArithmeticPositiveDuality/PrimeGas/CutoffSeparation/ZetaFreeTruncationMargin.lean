import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.StripLowerBounds
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven
import GaloisForLFunctions.RHTower.ZetaDiscLowerBoundsAtTypicalHeights

/-!
# `|ζ(w)|`-free truncation margins, verified-height reduction above `67`, and typical-height disc floors

In `DigitImbalanceLaw`, `digitImbalanceErrorConst` includes `‖2 q ζ(w) / (1 - q)‖ * C^(Re w)` from
approximating `(1 - q^L) Z` by `Z`. Eliminating `|ζ(w)|` from the single-cutoff error bound yields
self-contained nonvanishing certificates and sharpens the PGS frontier:

1. **All-cutoff `|ζ(w)|`-free certificate (`zetaFree_margin_forces_lower_bound`)**: splitting
   `cutoffTruncationBound = ‖Z‖ (C / X)^(Re w) + zetaFreeTruncationBound` shows that beating the
   elementary `|ζ(w)|`-free bound `zetaFreeTruncationBound t j X₀ w` at a single cutoff `X₀ ≥ 1`
   forces `‖Z‖ ≥ δ₀ > 0`, `ζ(w) ≠ 0`, and `‖renormalizedCutoff‖ ≥ δ₀ / 2` at all large `X`.
2. **Radix-shell `|ζ(w)|`-free damped bound (`norm_renormalizedCutoff_radix_pow_sub_damped_le`)**:
   retaining `(1 - q^K)` on the limit at `X = C^K` removes `ζ(w)` identically from the remainder.
3. **Unconditional margin through height `67` and high-ordinate RH reduction
   (`exists_zetaFree_margin_of_abs_im_le_sixtySeven`, `rh_iff_zetaFree_margin_above_sixtySeven`)**:
   the analytic Fejér Hadamard budget (`rhVerifiedThrough_sixtySeven`) certifies the strict
   `|ζ(w)|`-free cutoff margin unconditionally across `1/2 < Re w < 1` for all `|Im w| ≤ 67`,
   reducing RH to nonreal points with `1/2 < Re w ≤ 20999 / 24000` and `67 < |Im w|`.
4. **Typical-height uniform disc margin (`typical_heights_uniform_disc_zetaFree_margin`)**: on every
   compact disc inside `1/2 < Re w < 1` (in particular inside `1/2 < Re w ≤ 20999 / 24000`) and for
   every `δ > 0`, outside at most `δ T` of heights `τ ∈ [0, T]` there is a single shell depth `K₀`
   at which the entire shifted disc beats `zetaFreeRadixErrorBound` by a uniform margin `ε₀ > 0`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter MeasureTheory Metric Set
open scoped Topology ENNReal

/-- Purely elementary component of `digitImbalanceErrorConst`, completely independent of `ζ(w)`. -/
def zetaFreeDigitErrorConst (t : ExceptionalTime) (j : ℕ) (w : ℂ) : ℝ :=
  let C : ℝ := (tailRadix t j).val
  2 * C / ((C - 1) * ‖1 - w‖) +
    (2 * C / (C - 1) + 1) +
    (C / (C - 1)) * (2 : ℝ) ^ (w.re + 1) *
      (3 * ‖w‖ + ‖w * (w + 1)‖ / (4 * (w.re + 1)))

/-- All-cutoff `|ζ(w)|`-free truncation bound `(log_C X + 1 + zetaFreeDigitErrorConst) X^(-Re w)`. -/
def zetaFreeTruncationBound (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℝ :=
  (Real.logb (tailRadix t j).val X + 1 + zetaFreeDigitErrorConst t j w) * (X : ℝ) ^ (-w.re)

/-- Radix-shell `|ζ(w)|`-free truncation bound at `X = C^K` against `(1 - q^K) · 2 q ζ(w) / (1 - q)`. -/
def zetaFreeRadixErrorBound (t : ExceptionalTime) (j K : ℕ) (w : ℂ) : ℝ :=
  let C : ℝ := (tailRadix t j).val
  ((K : ℝ) + 2 / ((C - 1) * ‖1 - w‖) +
    C * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (C - 1))) * C ^ (-(K : ℝ) * w.re)

theorem digitImbalanceErrorConst_eq_zeta_add_zetaFree (t : ExceptionalTime) (j : ℕ) (w : ℂ) :
    let C := tailRadix t j
    let q := heat w C
    digitImbalanceErrorConst t j w =
      ‖2 * q * riemannZeta w / (1 - q)‖ * (C.val : ℝ) ^ w.re +
        zetaFreeDigitErrorConst t j w := by
  dsimp only
  unfold digitImbalanceErrorConst zetaFreeDigitErrorConst
  dsimp only
  ring

theorem cutoffTruncationBound_eq_zeta_add_zetaFree (t : ExceptionalTime) (j X : ℕ) (w : ℂ) :
    let C := tailRadix t j
    let q := heat w C
    cutoffTruncationBound t j X w =
      ‖2 * q * riemannZeta w / (1 - q)‖ * ((C.val : ℝ) ^ w.re * (X : ℝ) ^ (-w.re)) +
        zetaFreeTruncationBound t j X w := by
  dsimp only
  unfold cutoffTruncationBound zetaFreeTruncationBound
  rw [digitImbalanceErrorConst_eq_zeta_add_zetaFree]
  ring

theorem tendsto_zetaFreeTruncationBound_zero (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun X : ℕ => zetaFreeTruncationBound t j X w) atTop (𝓝 0) := by
  set C := tailRadix t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast radix_gt_one t j
  have hlogC : 0 < Real.log C.val := Real.log_pos hCr1
  have h1 : Tendsto (fun X : ℕ => Real.logb C.val X * (X : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
    have hexp := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hw)).const_mul
      (1 / (w.re * Real.log C.val))
    rw [mul_zero] at hexp
    refine hexp.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX0
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX0
    dsimp only [Function.comp_apply]
    rw [pow_one, Real.logb, Real.rpow_def_of_pos hXpos]
    have : -(w.re * Real.log X) = Real.log X * (-w.re) := by ring
    rw [this]
    field_simp [hw.ne', hlogC.ne']
  have h2 : Tendsto (fun X : ℕ =>
      (1 + zetaFreeDigitErrorConst t j w) * (X : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
    have hrp := (tendsto_rpow_neg_atTop hw).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_def] using hrp.const_mul (1 + zetaFreeDigitErrorConst t j w)
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr fun X => ?_
  unfold zetaFreeTruncationBound
  ring

/-- Exact `|ζ(w)|`-free truncation bound at radix powers `X = C^K` against `(1 - q^K) Z`. -/
theorem norm_renormalizedCutoff_radix_pow_sub_damped_le
    (t : ExceptionalTime) (j K : ℕ) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    let C := tailRadix t j
    let q := heat w C
    ‖renormalizedCutoff t j (C.val ^ K) w -
        (1 - q ^ K) * (2 * q * riemannZeta w / (1 - q))‖ ≤
      zetaFreeRadixErrorBound t j K w := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  have hC1 : 1 < C.val := radix_gt_one t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast hC1
  have hCr0 : (0 : ℝ) < C.val := by positivity
  have hq_lt : ‖q‖ < 1 := heat_contraction C hC1 w hw
  have hq1 : q ≠ 1 := fun he => hq_lt.ne (by rw [he, norm_one])
  have heq := renormalizedCutoff_radix_pow_eq t j K (by linarith) hw1 hq1
  dsimp only at heq
  have hrearr : renormalizedCutoff t j (C.val ^ K) w -
      (1 - q ^ K) * (2 * q * riemannZeta w / (1 - q)) =
      q ^ K * ((K : ℂ) - 2 / (((C.val : ℂ) - 1) * (1 - w)) +
        2 * (w * (w + 1)) * ∑ m ∈ Finset.range K,
          q⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w) := by
    linear_combination heq
  have hsum_bernoulli : ‖∑ m ∈ Finset.range K,
      q⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w‖ ≤
      (C.val : ℝ) / (8 * (w.re + 1) * ((C.val : ℝ) - 1)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun m _ =>
      norm_inv_heat_mul_bernoulliTail_le C (by linarith) m).trans ?_
    rw [← Finset.mul_sum]
    have hinv_ne : ((C.val : ℝ)⁻¹) - 1 ≠ 0 := by
      intro h; exact hCr1.ne' (inv_eq_one.mp (sub_eq_zero.mp h))
    have hc_sub : (C.val : ℝ) - 1 ≠ 0 := (sub_pos.mpr hCr1).ne'
    have hg : (∑ m ∈ Finset.range K, ((C.val : ℝ)⁻¹) ^ m) =
        (1 - ((C.val : ℝ)⁻¹) ^ K) / (1 - (C.val : ℝ)⁻¹) := by
      have hden2 : (1 : ℝ) - (C.val : ℝ)⁻¹ ≠ 0 := by
        intro h; exact hinv_ne (by linear_combination -h)
      rw [eq_div_iff hden2]
      linear_combination -(geom_sum_mul ((C.val : ℝ)⁻¹) K)
    have hgeom_le : (∑ m ∈ Finset.range K, ((C.val : ℝ)⁻¹) ^ m) ≤
        (C.val : ℝ) / ((C.val : ℝ) - 1) := by
      rw [hg]
      have h1_pos : 0 < 1 - (C.val : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hCr1)
      have hnum_le : 1 - ((C.val : ℝ)⁻¹) ^ K ≤ 1 :=
        sub_le_self 1 (pow_nonneg (inv_nonneg.mpr hCr0.le) K)
      calc (1 - ((C.val : ℝ)⁻¹) ^ K) / (1 - (C.val : ℝ)⁻¹)
          ≤ 1 / (1 - (C.val : ℝ)⁻¹) := div_le_div_of_nonneg_right hnum_le h1_pos.le
        _ = (C.val : ℝ) / ((C.val : ℝ) - 1) := by
            field_simp [hCr0.ne', hc_sub, h1_pos.ne']
    calc (1 / (8 * (w.re + 1))) * (∑ m ∈ Finset.range K, ((C.val : ℝ)⁻¹) ^ m)
        ≤ (1 / (8 * (w.re + 1))) * ((C.val : ℝ) / ((C.val : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hgeom_le (by positivity)
      _ = (C.val : ℝ) / (8 * (w.re + 1) * ((C.val : ℝ) - 1)) := by
          rw [div_mul_div_comm, one_mul]
  have hnorm_c1 : ‖(C.val : ℂ) - 1‖ = (C.val : ℝ) - 1 := by
    have : (C.val : ℂ) - 1 = (((C.val : ℝ) - 1 : ℝ) : ℂ) := by simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hCr1)]
  rw [hrearr, mul_comm (q ^ K), norm_mul, norm_heat_pow]
  unfold zetaFreeRadixErrorBound
  dsimp only [C]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hCr0.le _)
  refine ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans ?_
  rw [Complex.norm_natCast, norm_div, Complex.norm_ofNat, norm_mul, hnorm_c1,
    norm_mul, norm_mul, Complex.norm_ofNat]
  have hbern2 : 2 * ‖w * (w + 1)‖ * ‖∑ m ∈ Finset.range K,
      q⁻¹ ^ m * _root_.RHTower.zetaBernoulliTail (C.val ^ m) w‖ ≤
      (C.val : ℝ) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((C.val : ℝ) - 1)) := by
    calc 2 * ‖w * (w + 1)‖ * _
        ≤ 2 * ‖w * (w + 1)‖ * ((C.val : ℝ) / (8 * (w.re + 1) * ((C.val : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hsum_bernoulli (by positivity)
      _ = (C.val : ℝ) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((C.val : ℝ) - 1)) := by
          have hd4 : 4 * (w.re + 1) * ((C.val : ℝ) - 1) ≠ 0 :=
            mul_ne_zero (by linarith) (sub_pos.mpr hCr1).ne'
          have hd8 : 8 * (w.re + 1) * ((C.val : ℝ) - 1) ≠ 0 :=
            mul_ne_zero (by linarith) (sub_pos.mpr hCr1).ne'
          rw [mul_div_assoc', div_eq_div_iff hd8 hd4]
          ring
  linarith

/-- Self-contained `|ζ(w)|`-free single-cutoff margin certificate: if at one cutoff `X₀ ≥ 1` the
modulus of `renormalizedCutoff` exceeds `zetaFreeTruncationBound`, then `ζ(w) ≠ 0` and every large
cutoff stays bounded away from zero by an explicit `|ζ(w)|`-free positive floor `δ₀ / 2`. -/
theorem zetaFree_margin_forces_lower_bound (t : ExceptionalTime) (j : ℕ)
    {X₀ : ℕ} (hX₀ : 1 ≤ X₀) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    (hmargin : zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖) :
    let Cr : ℝ := (tailRadix t j).val
    let δ₀ := (‖renormalizedCutoff t j X₀ w‖ - zetaFreeTruncationBound t j X₀ w) /
      (1 + Cr ^ w.re * (X₀ : ℝ) ^ (-w.re))
    riemannZeta w ≠ 0 ∧
      (∀ X : ℕ, 1 ≤ X → Cr ^ w.re * (X : ℝ) ^ (-w.re) ≤ 1 / 4 →
        zetaFreeTruncationBound t j X w ≤ δ₀ / 4 →
          δ₀ / 2 ≤ ‖renormalizedCutoff t j X w‖) ∧
      (∀ᶠ X : ℕ in atTop, δ₀ / 2 ≤ ‖renormalizedCutoff t j X w‖) := by
  dsimp only
  set C := tailRadix t j
  let Cr : ℝ := C.val
  have hCr0 : (0 : ℝ) < Cr := Nat.cast_pos.mpr C.pos
  have hX₀_pos : (0 : ℝ) < X₀ := Nat.cast_pos.mpr hX₀
  set q := heat w C
  set L := 2 * q * riemannZeta w / (1 - q)
  set ratio₀ := Cr ^ w.re * (X₀ : ℝ) ^ (-w.re)
  have hratio₀_nn : 0 ≤ ratio₀ := mul_nonneg (Real.rpow_nonneg hCr0.le _) (Real.rpow_nonneg hX₀_pos.le _)
  have hden₀_pos : 0 < 1 + ratio₀ := by linarith
  set δ₀ := (‖renormalizedCutoff t j X₀ w‖ - zetaFreeTruncationBound t j X₀ w) / (1 + ratio₀)
  have hδ₀_pos : 0 < δ₀ := div_pos (sub_pos.mpr hmargin) hden₀_pos
  have hb₀ : ‖renormalizedCutoff t j X₀ w - L‖ ≤ cutoffTruncationBound t j X₀ w :=
    norm_renormalizedCutoff_sub_limit_le t j hX₀ hw hw1
  rw [cutoffTruncationBound_eq_zeta_add_zetaFree] at hb₀
  have hL_ge : δ₀ ≤ ‖L‖ := by
    have htri : ‖renormalizedCutoff t j X₀ w‖ ≤ ‖renormalizedCutoff t j X₀ w - L‖ + ‖L‖ := by
      simpa only [sub_add_cancel] using norm_add_le (renormalizedCutoff t j X₀ w - L) L
    have hmul : ‖renormalizedCutoff t j X₀ w‖ - zetaFreeTruncationBound t j X₀ w ≤
        ‖L‖ * (1 + ratio₀) := by
      dsimp only [L, q, C, ratio₀, Cr] at hb₀ htri ⊢
      linarith
    exact (div_le_iff₀ hden₀_pos).mpr hmul
  have hzeta_ne : riemannZeta w ≠ 0 := by
    intro hz
    have hL0 : L = 0 := by dsimp [L]; rw [hz, mul_zero, zero_div]
    rw [hL0, norm_zero] at hL_ge
    linarith
  have hall : ∀ X : ℕ, 1 ≤ X → Cr ^ w.re * (X : ℝ) ^ (-w.re) ≤ 1 / 4 →
      zetaFreeTruncationBound t j X w ≤ δ₀ / 4 → δ₀ / 2 ≤ ‖renormalizedCutoff t j X w‖ := by
    intro X hX1 hrat hzf
    have hbX : ‖renormalizedCutoff t j X w - L‖ ≤ cutoffTruncationBound t j X w :=
      norm_renormalizedCutoff_sub_limit_le t j hX1 hw hw1
    rw [cutoffTruncationBound_eq_zeta_add_zetaFree] at hbX
    have htri : ‖L‖ ≤ ‖renormalizedCutoff t j X w‖ + ‖L - renormalizedCutoff t j X w‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (renormalizedCutoff t j X w) (L - renormalizedCutoff t j X w)
    rw [norm_sub_rev] at htri
    have hL_rat : ‖L‖ * ((C.val : ℝ) ^ w.re * (X : ℝ) ^ (-w.re)) ≤ ‖L‖ * (1 / 4) :=
      mul_le_mul_of_nonneg_left hrat (norm_nonneg L)
    dsimp only [L, q, C, Cr] at hbX htri hL_rat ⊢
    linarith
  refine ⟨hzeta_ne, hall, ?_⟩
  have hrat_zero : Tendsto (fun X : ℕ => Cr ^ w.re * (X : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
    have hrp := (tendsto_rpow_neg_atTop hw).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_def] using hrp.const_mul (Cr ^ w.re)
  have hzf_zero := tendsto_zetaFreeTruncationBound_zero t j hw
  filter_upwards [eventually_ge_atTop 1,
    hrat_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hzf_zero.eventually (Iio_mem_nhds (by positivity : 0 < δ₀ / 4))] with X hX1 hrat hzf
  exact hall X hX1 hrat.le hzf.le

/-- Pointwise equivalence between `ζ(w) ≠ 0` and existence of one cutoff beating the `|ζ(w)|`-free
bound `zetaFreeTruncationBound`. -/
theorem exists_zetaFree_margin_iff_zeta_ne_zero (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    (∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖) ↔
      riemannZeta w ≠ 0 := by
  constructor
  · rintro ⟨X₀, hX1, hmarg⟩
    exact (zetaFree_margin_forces_lower_bound t j hX1 hw hw1 hmarg).1
  · intro hz
    obtain ⟨ε, hε, hev⟩ := (eventually_norm_renormalizedCutoff_ge_iff t j hw hw1).mpr hz
    have hzf := tendsto_zetaFreeTruncationBound_zero t j hw
    obtain ⟨X₀, ⟨hX1, hge⟩, hlt⟩ :=
      (((eventually_ge_atTop 1).and hev).and (hzf.eventually (Iio_mem_nhds hε))).exists
    exact ⟨X₀, hX1, lt_of_lt_of_le hlt hge⟩

/-! ### Unconditional `|ζ(w)|`-free margin through height `67` and high-ordinate RH reduction -/

/-- Unconditional nonvanishing of `ζ(w)` across `1/2 < Re w < 1` for all `|Im w| ≤ 67`, proved
analytically from the Fejér Hadamard budget (`rhVerifiedThrough_sixtySeven`). -/
theorem riemannZeta_ne_zero_of_strip_abs_im_le_sixtySeven {w : ℂ}
    (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (him : |w.im| ≤ 67) :
    riemannZeta w ≠ 0 := by
  intro hz
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  have hxi : _root_.RHTower.xi w = 0 := (_root_.RHTower.xi_eq_zero_iff hw0 hw1).mpr hz
  have hgt := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
    VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_sixtySeven
    hxi hw0 hhi (by linarith)
  linarith

/-- Unconditional `|ζ(w)|`-free single-cutoff margin for the actual shell weights at every point of
`1/2 < Re w < 1` with `|Im w| ≤ 67` (both real and nonreal). -/
theorem exists_zetaFree_margin_of_abs_im_le_sixtySeven (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (him : |w.im| ≤ 67) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  exact (exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mpr
    (riemannZeta_ne_zero_of_strip_abs_im_le_sixtySeven hlo hhi him)

/-- Exact equivalence of the Riemann Hypothesis with the `|ζ(w)|`-free single-cutoff margin on the
remaining high-ordinate strip `1/2 < Re w ≤ 20999 / 24000`, `67 < |Im w|`. -/
theorem rh_iff_zetaFree_margin_above_sixtySeven (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 67 < |w.im| →
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro hRH w hlo hhi _
    have hw0 : 0 < w.re := by linarith
    have hw_lt1 : w.re < 1 := by linarith
    have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
    exact (exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mpr (hRH w hlo hw_lt1)
  · intro hmarg w hlo hhi
    rcases lt_or_ge (20999 / 24000 : ℝ) w.re with hright | hstrip
    · exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
        hright
    · rcases le_or_gt |w.im| 67 with hlow | hhigh
      · exact riemannZeta_ne_zero_of_strip_abs_im_le_sixtySeven hlo hhi hlow
      · have hw0 : 0 < w.re := by linarith
        have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
        exact (exists_zetaFree_margin_iff_zeta_ne_zero t j hw0 hw1).mp
          (hmarg w hlo hstrip hhigh)

/-! ### Typical-height uniform disc margin inside `1/2 < Re w ≤ 20999 / 24000` -/

/-- On every compact disc strictly inside `1/2 < Re w < 1` (in particular every disc inside the
remaining strip `1/2 < Re w ≤ 20999 / 24000`) and for every density tolerance `δ > 0`, outside at
most `δ T` of heights `τ ∈ [0, T]` (eventually in `T`), a single radix shell `C^K₀` certifies a
uniform `|ζ(w)|`-free margin `ε₀ > 0` across the entire shifted disc `closedBall c r + iτ`. -/
theorem typical_heights_uniform_disc_zetaFree_margin (t : ExceptionalTime) (j : ℕ)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | ¬∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ z ∈ closedBall c r,
          zetaFreeRadixErrorBound t j K₀ (z + (τ : ℂ) * Complex.I) + ε₀ ≤
            ‖renormalizedCutoff t j ((tailRadix t j).val ^ K₀) (z + (τ : ℂ) * Complex.I)‖}
        ∩ Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  obtain ⟨b, hb, hbad_vol⟩ :=
    _root_.RHTower.exists_zeta_disc_floor_at_typical_heights hr h0 h1 hδ
  set C := tailRadix t j
  let Cr : ℝ := C.val
  have hCr1 : (1 : ℝ) < Cr := by dsimp only [Cr]; exact_mod_cast radix_gt_one t j
  have hCr0 : (0 : ℝ) < Cr := by positivity
  set σmin : ℝ := c.re - r
  set σmax : ℝ := c.re + r
  have hσmin_pos : 0 < σmin := by dsimp only [σmin]; linarith
  have h1_sub_max : 0 < 1 - σmax := by dsimp only [σmax]; linarith
  set ε₀ : ℝ := Cr ^ (-σmax) * b / 4
  have hε₀ : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀, hbad_vol.mono fun T hT => (measure_mono (inter_subset_inter_left _ ?_)).trans hT⟩
  intro τ hnot_marg
  rw [mem_setOf_eq] at hnot_marg ⊢
  by_contra! hgood
  apply hnot_marg
  -- Uniformly bound `zetaFreeRadixErrorBound` across `z ∈ closedBall c r` at height `τ`.
  set R : ℝ := ‖c‖ + r + |τ|
  set Mrad : ℝ := 2 / ((Cr - 1) * (1 - σmax)) +
    Cr * (R * (R + 1)) / (4 * (σmin + 1) * (Cr - 1))
  have hlogC : 0 < Real.log Cr := Real.log_pos hCr1
  have hdecay1 : Tendsto (fun K : ℕ => (K : ℝ) * Cr ^ (-(K : ℝ) * σmin)) atTop (𝓝 0) := by
    have hexp := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (mul_pos hσmin_pos hlogC))).const_mul
      (1 / (σmin * Real.log Cr))
    rw [mul_zero] at hexp
    refine hexp.congr fun K => ?_
    dsimp only [Function.comp_apply]
    rw [pow_one, Real.rpow_def_of_pos hCr0]
    have : -(σmin * Real.log Cr * (K : ℝ)) = Real.log Cr * (-(K : ℝ) * σmin) := by ring
    rw [this]
    field_simp [hσmin_pos.ne', hlogC.ne']
  have hdecay2 : Tendsto (fun K : ℕ => Mrad * Cr ^ (-(K : ℝ) * σmin)) atTop (𝓝 0) := by
    have hlt1 : Cr ^ (-σmin) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hCr1 (neg_neg_of_pos hσmin_pos)
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hCr0.le _) hlt1).const_mul Mrad
    rw [mul_zero] at hp
    refine hp.congr fun K => ?_
    rw [← Real.rpow_natCast (Cr ^ (-σmin)) K, ← Real.rpow_mul hCr0.le]
    congr 1; ring
  have hdecay_pow : Tendsto (fun K : ℕ => Cr ^ (-(K : ℝ) * σmin)) atTop (𝓝 0) := by
    have hlt1 : Cr ^ (-σmin) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hCr1 (neg_neg_of_pos hσmin_pos)
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg hCr0.le _) hlt1).congr fun K => ?_
    rw [← Real.rpow_natCast (Cr ^ (-σmin)) K, ← Real.rpow_mul hCr0.le]
    congr 1; ring
  have hsum_decay := hdecay1.add hdecay2
  rw [add_zero] at hsum_decay
  obtain ⟨K₀, ⟨hK1, hpow_small⟩, herr_small⟩ :=
    (((eventually_ge_atTop 1).and
      (hdecay_pow.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))).and
      (hsum_decay.eventually (Iio_mem_nhds hε₀))).exists
  refine ⟨K₀, hK1, fun z hz => ?_⟩
  set w : ℂ := z + (τ : ℂ) * Complex.I
  have hzc_norm : ‖z - c‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hzc_re := abs_le.mp ((Complex.abs_re_le_norm (z - c)).trans hzc_norm)
  rw [Complex.sub_re] at hzc_re
  have hw_re_lo : σmin ≤ w.re := by simp [w, σmin]; linarith [hzc_re.1]
  have hw_re_hi : w.re ≤ σmax := by simp [w, σmax]; linarith [hzc_re.2]
  have hw0 : 0 < w.re := lt_of_lt_of_le hσmin_pos hw_re_lo
  have hw_lt1 : w.re < 1 := lt_of_le_of_lt hw_re_hi (by dsimp only [σmax]; linarith)
  have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
  -- Upper-bound `zetaFreeRadixErrorBound t j K₀ w ≤ ε₀`.
  have h1w_ge : 1 - σmax ≤ ‖(1 : ℂ) - w‖ := by
    have hre : 1 - σmax ≤ ((1 : ℂ) - w).re := by simp; linarith
    exact hre.trans (Complex.re_le_norm _)
  have hw_norm_le : ‖w‖ ≤ R := by
    have hw_split : w = (z - c) + c + (τ : ℂ) * Complex.I := by dsimp only [w]; ring
    rw [hw_split]
    refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans ?_
    have hτ_norm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [hτ_norm]
    dsimp only [R]; linarith
  have hww1_le : ‖w * (w + 1)‖ ≤ R * (R + 1) := by
    rw [norm_mul]
    have hw1_le : ‖w + 1‖ ≤ R + 1 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    exact mul_le_mul hw_norm_le hw1_le (norm_nonneg _) (by dsimp only [R]; positivity)
  have herr_le : zetaFreeRadixErrorBound t j K₀ w ≤ ε₀ := by
    have hcoeff_le : (K₀ : ℝ) + 2 / ((Cr - 1) * ‖1 - w‖) +
        Cr * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1)) ≤ (K₀ : ℝ) + Mrad := by
      have ht1 : 2 / ((Cr - 1) * ‖1 - w‖) ≤ 2 / ((Cr - 1) * (1 - σmax)) :=
        div_le_div_of_nonneg_left zero_le_two
          (mul_pos (sub_pos.mpr hCr1) h1_sub_max)
          (mul_le_mul_of_nonneg_left h1w_ge (sub_pos.mpr hCr1).le)
      have ht2 : Cr * ‖w * (w + 1)‖ / (4 * (w.re + 1) * (Cr - 1)) ≤
          Cr * (R * (R + 1)) / (4 * (σmin + 1) * (Cr - 1)) :=
        div_le_div₀ (by dsimp only [R]; positivity)
          (mul_le_mul_of_nonneg_left hww1_le hCr0.le)
          (mul_pos (by linarith) (sub_pos.mpr hCr1))
          (mul_le_mul_of_nonneg_right (by linarith) (sub_pos.mpr hCr1).le)
      dsimp only [Mrad]; linarith
    have hrpow_le : Cr ^ (-(K₀ : ℝ) * w.re) ≤ Cr ^ (-(K₀ : ℝ) * σmin) :=
      Real.rpow_le_rpow_of_exponent_le hCr1.le
        (mul_le_mul_of_nonpos_left hw_re_lo (neg_nonpos.mpr (Nat.cast_nonneg K₀)))
    unfold zetaFreeRadixErrorBound
    dsimp only [Cr, C] at hcoeff_le hrpow_le herr_small ⊢
    have hprod : ((K₀ : ℝ) + 2 / (((C.val : ℝ) - 1) * ‖1 - w‖) +
        (C.val : ℝ) * ‖w * (w + 1)‖ / (4 * (w.re + 1) * ((C.val : ℝ) - 1))) *
          (C.val : ℝ) ^ (-(K₀ : ℝ) * w.re) ≤
        ((K₀ : ℝ) + Mrad) * (C.val : ℝ) ^ (-(K₀ : ℝ) * σmin) :=
      mul_le_mul hcoeff_le hrpow_le (Real.rpow_nonneg hCr0.le _)
        (le_trans (by positivity) hcoeff_le)
    have hsum_eq : ((K₀ : ℝ) + Mrad) * (C.val : ℝ) ^ (-(K₀ : ℝ) * σmin) =
        (K₀ : ℝ) * (C.val : ℝ) ^ (-(K₀ : ℝ) * σmin) +
          Mrad * (C.val : ℝ) ^ (-(K₀ : ℝ) * σmin) := add_mul _ _ _
    linarith [herr_small]
  -- Lower-bound `‖(1 - q^K₀) * Z‖ ≥ 3 * ε₀`.
  set q := heat w C
  set Z := 2 * q * riemannZeta w / (1 - q)
  have hzeta_b : b ≤ ‖riemannZeta w‖ := hgood z hz
  have hq_norm : ‖q‖ = Cr ^ (-w.re) := by
    rw [norm_heat, energy, Real.rpow_def_of_pos hCr0]
    congr 1; dsimp only [Cr]; ring
  have hq_ge : Cr ^ (-σmax) ≤ ‖q‖ := by
    rw [hq_norm]
    exact Real.rpow_le_rpow_of_exponent_le hCr1.le (neg_le_neg hw_re_hi)
  have h1q_le2 : ‖(1 : ℂ) - q‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    linarith [(heat_contraction C (radix_gt_one t j) w hw0).le]
  have h1q_pos : 0 < ‖(1 : ℂ) - q‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun he =>
      (heat_contraction C (radix_gt_one t j) w hw0).ne (by dsimp only [q] at he; rw [← he, norm_one]))
  have hZ_ge : 4 * ε₀ ≤ ‖Z‖ := by
    dsimp only [Z, ε₀]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    calc 4 * (Cr ^ (-σmax) * b / 4)
        = (2 * Cr ^ (-σmax) * b) / 2 := by ring
      _ ≤ (2 * ‖q‖ * ‖riemannZeta w‖) / 2 := by
          refine div_le_div_of_nonneg_right ?_ zero_le_two
          exact mul_le_mul (mul_le_mul_of_nonneg_left hq_ge zero_le_two) hzeta_b
            hb.le (mul_nonneg zero_le_two (norm_nonneg q))
      _ ≤ (2 * ‖q‖ * ‖riemannZeta w‖) / ‖(1 : ℂ) - q‖ :=
          div_le_div_of_nonneg_left (by positivity) h1q_pos h1q_le2
  have hqK_le : ‖q ^ K₀‖ ≤ 1 / 4 := by
    rw [norm_heat_pow]
    have hrp : (C.val : ℝ) ^ (-(K₀ : ℝ) * w.re) ≤ Cr ^ (-(K₀ : ℝ) * σmin) :=
      Real.rpow_le_rpow_of_exponent_le hCr1.le
        (mul_le_mul_of_nonpos_left hw_re_lo (neg_nonpos.mpr (Nat.cast_nonneg K₀)))
    exact hrp.trans hpow_small.le
  have h1qK_ge : 3 / 4 ≤ ‖(1 : ℂ) - q ^ K₀‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (q ^ K₀)
    rw [norm_one] at h
    linarith
  have hdamped_ge : 3 * ε₀ ≤ ‖(1 - q ^ K₀) * Z‖ := by
    rw [norm_mul]
    calc 3 * ε₀ = (3 / 4) * (4 * ε₀) := by ring
      _ ≤ ‖(1 : ℂ) - q ^ K₀‖ * ‖Z‖ :=
          mul_le_mul h1qK_ge hZ_ge (by positivity) (by linarith)
  have hdamped_err := norm_renormalizedCutoff_radix_pow_sub_damped_le t j K₀ hw0 hw1
  dsimp only at hdamped_err
  have htri : ‖(1 - q ^ K₀) * Z‖ ≤
      ‖renormalizedCutoff t j (C.val ^ K₀) w‖ +
        ‖(1 - q ^ K₀) * Z - renormalizedCutoff t j (C.val ^ K₀) w‖ := by
    simpa only [add_sub_cancel] using
      norm_add_le (renormalizedCutoff t j (C.val ^ K₀) w)
        ((1 - q ^ K₀) * Z - renormalizedCutoff t j (C.val ^ K₀) w)
  rw [norm_sub_rev] at htri
  dsimp only [Z, q, C] at hdamped_ge htri herr_le hdamped_err ⊢
  linarith

#print axioms norm_renormalizedCutoff_radix_pow_sub_damped_le
#print axioms zetaFree_margin_forces_lower_bound
#print axioms exists_zetaFree_margin_iff_zeta_ne_zero
#print axioms riemannZeta_ne_zero_of_strip_abs_im_le_sixtySeven
#print axioms exists_zetaFree_margin_of_abs_im_le_sixtySeven
#print axioms rh_iff_zetaFree_margin_above_sixtySeven
#print axioms typical_heights_uniform_disc_zetaFree_margin

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
