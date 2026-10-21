import GaloisForLFunctions.SquareRootThreshold.ZetaHidingRequiresLoudTwins
import GaloisForLFunctions.SquareRootThreshold.ZetaLagFamilyUnconditionalEnvelope

/-!
# The two-parameter lag family sees near-top zeros of `ζ`

For the one-parameter family `κ_w(t ± v/2)` a zero at height `γ` enters with the coefficient
`|D| ≈ |h_w(γ − iδ)|² ≲ γ^{−4}`, so the companion laws need a depth offset `κ ≈ log(1/|D|)` that
grows with the height of the Legendre record. Modulating the bump to the height of the zero
removes this loss. This module does so at the height of a zero near the top depth.

**Coefficients of the modulated family** (`norm_evenCoeff_modScaledBump_le`,
`norm_evenCoeff_modScaledBump_center_ge`). With the multiplicity bound
`m ≤ 40 log(180|γ|)` from the corpus local count (`mult_le_log_zeta`), the bump modulated to `c` has
`|D_c(z)| ≤ 40 log(180|Im z|)(e^{w/2}B_w)²((1 + |Im z − c|)^{−4} + (1 + |Im z + c|)^{−4})`, and at the
center `c = Im z₀` of a zero `½ + z₀` it has `|D_c(z₀)| ≥ a_w² − 40 log(180 c)(e^{w/2}B_w)²/(1 + 2c)⁴`,
`a_w = 4w e^{−w/2}∫κ` (`centerAmplitude`). Records stay near the center:
`|Im z*| ≤ max(2c, (2880 K)^{1/3})` (`abs_im_le_of_norm_evenCoeff_modScaledBump_ge`).

**Near-top zeros** (`zeta_modulated_near_top_twin`). Let `½ + z₀` be `1/V`-near the top: every
exponent has `Re z ≤ Re z₀ + 1/V`. If RH fails such zeros exist for every `V`, whether or not the top
depth is attained. Then the Legendre record `z*` of the family modulated to `γ₀ = Im z₀` keeps the
coefficient `|D(z*)| ≥ |D(z₀)|/e ≥ a_w²/(2e)`, uniformly in `V`: the record cannot drift to small
coefficients. The twin law for an arbitrary bump (`zeta_twin_law_of_bump`) with the explicit
`κ = log(2 + 3e(C + 1)/(2Πa_w²))` (`twinKappa`, `C` from `|M|`, `W` and `r`) gives: if the modulated
difference tests are nonnegative on `[0, V]`, `V ≥ 2κ/Re z*` and `V³ ≥ (8/3)κ(κ² + 4π²)Π(r, Im z*)`,
then another zero lies within `r` of `(Re z* − κ/V) + i Im z*`.

Here `κ` depends only on `|M|`, `W`, `Re z*` and constants of the bump; for the modulated family
`M` and `W` are sums of coefficients weighted by `(1 + |Im z ∓ γ₀|)^{−4}`, governed by the local zero
count near `±γ₀`. So `r ≍ κ (log γ₀)^{1/3}/V → 0`: **a non-attained top is seen by the two-parameter family at a
controlled lag, unless it is realized by loud twins, or its near-top zeros escape to heights
`log γ₀ ≳ (V/κ)³`.** What replaces the attainment premise is a near-top zero together with the
modulation to its height.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Twin law for every bump.** `zeta_twin_law` for an arbitrary `C²` bump supported in
`[−w, w]`, with the positivity hypothesis on the Weil side. -/
theorem zeta_twin_law_of_bump {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : π ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig (b) z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig (b) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (b) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (b) z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hVr : 4 * π ≤ V * r)
    (hV3 : 8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * (480 * Real.log 1080 * (1 / 64 + 3) +
      480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) ≤ V ^ 3) :
    4 / 3 * (480 * Real.log 1080 * (1 / 64 + 3) +
        480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) *
        ‖evenCoeff zetaZeroConfig (b) z₁‖ * (Real.exp κ - 2) ≤
      |2 * (lagStructure zetaZeroConfig (b) 0).re| *
          (1 / (z₁.re - κ / V) ^ 3 + 1 / 24) +
        8 / 3 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (b) z‖) *
          (1 / 64 + 1 / r ^ 3) +
        V ^ 3 / (2 * π ^ 2) * ∑' z : ℂ, (if evenCoeff zetaZeroConfig (b) z ≠ 0 ∧
          z ≠ z₁ ∧ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < r then
            ‖evenCoeff zetaZeroConfig (b) z‖ *
              (1 + Real.exp ((z.re - (z₁.re - κ / V)) * V)) else 0) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set σ : ℝ := z₁.re - κ / V with hσdef
  set θ : ℝ := κ / V with hθdef
  have hV0 : 0 < V := lt_of_lt_of_le Real.pi_pos hV
  have hθ0 : 0 < θ := div_pos hκ hV0
  have hθV : θ * V = κ := by rw [hθdef]; field_simp
  set s : ℂ := (σ : ℂ) + z₁.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = z₁.im := by simp [hs]
  have hcore := norm_evenCoeff_mul_fejerWin_le zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
    hV0.le hm z₁ σ z₁.im
  rw [← hs] at hcore
  -- the record term
  have hz₁s : z₁ - s = (θ : ℂ) := by apply Complex.ext <;> simp [hs, hσdef, hθdef]
  have hLHS : ‖D z₁ * fejerWin V (z₁ - s)‖ =
      ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) := by
    rw [norm_mul, hz₁s, norm_fejerWin_ofReal_pos hV0 hθ0, hθV]
  -- the loudness of every exponent, relative to the record
  have hloud : ∀ z, D z ≠ 0 → ‖D z‖ * Real.exp ((z.re - σ) * V) ≤ ‖D z₁‖ * Real.exp κ + ‖D z‖ :=
    fun z hz => by
      by_cases hre : 0 < z.re
      · have h := hrec z hz hre
        have e1 : ‖D z‖ * Real.exp ((z.re - σ) * V) =
            ‖D z‖ * Real.exp (z.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        have e2 : ‖D z₁‖ * Real.exp κ = ‖D z₁‖ * Real.exp (z₁.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hσdef]; linarith [hθV]
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-σ * V)).le
        linarith [norm_nonneg (D z)]
      · push Not at hre
        have : Real.exp ((z.re - σ) * V) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0.le)
        have := mul_le_mul_of_nonneg_left this (norm_nonneg (D z))
        have := mul_nonneg (norm_nonneg (D z₁)) (Real.exp_pos κ).le
        linarith
  set c : ℝ := 8 * π ^ 2 / 3 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- potential kernels
  have hkern : ∀ {z u : ℂ} {d : ℝ}, 0 < d → 4 * π ≤ V * d → u.re = σ → D z ≠ 0 →
      d ≤ ‖z - u‖ → ‖D z‖ * ‖fejerWin V (z - u)‖ ≤
        c / V ^ 2 * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3) + 2 * ‖D z‖ / d ^ 3) := by
    intro z u d hd hVd hu hz hgap
    have hzu : 0 < ‖z - u‖ := lt_of_lt_of_le hd hgap
    have h4 : 4 * π ≤ V * ‖z - u‖ := hVd.trans (mul_le_mul_of_nonneg_left hgap hV0.le)
    have hcube := norm_fejerWin_le_cube hV0 h4
    rw [Complex.sub_re, hu, ← hc] at hcube
    have hcube' : 1 / ‖z - u‖ ^ 3 ≤ 1 / d ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd.le hgap 3)
    have hl := hloud z hz
    calc ‖D z‖ * ‖fejerWin V (z - u)‖
        ≤ ‖D z‖ * (c * (Real.exp ((z.re - σ) * V) + 1) / (V ^ 2 * ‖z - u‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hcube (norm_nonneg _)
      _ = c / V ^ 2 * ((‖D z‖ * Real.exp ((z.re - σ) * V) + ‖D z‖) * (1 / ‖z - u‖ ^ 3)) := by
          field_simp
      _ ≤ c / V ^ 2 * ((‖D z₁‖ * Real.exp κ + 2 * ‖D z‖) * (1 / ‖z - u‖ ^ 3)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          linarith
      _ ≤ c / V ^ 2 * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3) + 2 * ‖D z‖ / d ^ 3) := by
          gcongr
          rw [add_mul]
          have : 2 * ‖D z‖ * (1 / ‖z - u‖ ^ 3) ≤ 2 * ‖D z‖ * (1 / d ^ 3) :=
            mul_le_mul_of_nonneg_left hcube' (by positivity)
          rw [show 2 * ‖D z‖ / d ^ 3 = 2 * ‖D z‖ * (1 / d ^ 3) by ring]
          linarith
  -- the potential sums
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
  obtain ⟨hs0, hP0b⟩ := tsum_inv_cube_le (b := b) (s := (σ : ℂ)) (r := 4) (by norm_num)
    (fun z => D z ≠ 0) fun z hz => ⟨hz, (four_le_abs_im_of_evenCoeff_zeta hz).trans (by
      have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this)⟩
  obtain ⟨hs1, hP1b⟩ := tsum_inv_cube_le (b := b) (s := s) hr
    (fun z => D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖) fun z hz => ⟨hz.1, hz.2.2⟩
  rw [show (|((σ : ℂ)).im| : ℝ) = 0 by simp, zero_add] at hP0b
  rw [hsim] at hP1b
  set P0 : ℝ := ∑' z : ℂ, (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) with hP0
  set P1 : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0)
    with hP1
  set Nn : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
    ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) with hNn
  have hsN : Summable fun z : ℂ => (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
      ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) :=
    (hsD.mul_right (1 + Real.exp ((1 / 2 + |σ|) * V))).of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) fun z => by
        split_ifs with h
        · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h1 : (z.re - σ) * V ≤ (1 / 2 + |σ|) * V := mul_le_mul_of_nonneg_right
            (by linarith [(abs_le.mp (abs_re_le_of_evenCoeff_ne_zero h.1)).2, neg_abs_le σ]) hV0.le
          linarith [Real.exp_le_exp.mpr h1]
        · positivity
  have hP0 : ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤
      c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) := by
    have hle : ∀ z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤ c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) +
          2 * ‖D z‖ / 4 ^ 3) := fun z => by
      by_cases hz : D z = 0
      · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, if_false, mul_zero,
          zero_add, zero_div]
        positivity
      · rw [if_pos hz]
        exact hkern (by norm_num) (by linarith [Real.pi_pos]) (by simp) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
    have hR : Summable fun z : ℂ => c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) +
          2 * ‖D z‖ / 4 ^ 3) :=
      ((hs0.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le (fun _ => by positivity) hle) hR).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add (hs0.mul_left _) ((hsD.mul_left 2).div_const _),
      tsum_mul_left, tsum_div_const, tsum_mul_left]
  have hP1 : ∑' z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤
      c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) + V * Nn := by
    have hle : ∀ z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤ c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0) +
          2 * ‖D z‖ / r ^ 3) + V * (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
            ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) := fun z => by
      have hc0' : 0 ≤ c / V ^ 2 := by positivity
      by_cases hzz : z = z₁
      · rw [if_pos hzz]; split_ifs <;> positivity
      · rw [if_neg hzz]
        by_cases hz : D z = 0
        · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
            mul_zero, zero_div, add_zero]
          positivity
        · by_cases hfar : r ≤ ‖z - s‖
          · rw [if_pos ⟨hz, hzz, hfar⟩, if_neg (fun h => absurd h.2.2 (not_lt.mpr hfar)), mul_zero,
              add_zero]
            exact hkern hr hVr hsre hz hfar
          · push Not at hfar
            rw [if_neg (fun h => absurd h.2.2 (not_le.mpr hfar)), if_pos ⟨hz, hzz, hfar⟩, mul_zero,
              zero_add]
            have hn := norm_mul_fejerWin_le_near hV0.le ‖D z‖ (norm_nonneg _) z s
            rw [hsre] at hn
            have h0 : 0 ≤ c / V ^ 2 * (2 * ‖D z‖ / r ^ 3) := by positivity
            calc ‖D z‖ * ‖fejerWin V (z - s)‖
                ≤ V * (‖D z‖ + ‖D z‖ * Real.exp ((z.re - σ) * V)) := hn
              _ = V * (‖D z‖ * (1 + Real.exp ((z.re - σ) * V))) := by ring
              _ ≤ _ := le_add_of_nonneg_left h0
    have hR : Summable fun z : ℂ => c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 ∧ z ≠ z₁ ∧ r ≤ ‖z - s‖ then 1 / ‖z - s‖ ^ 3 else 0) +
          2 * ‖D z‖ / r ^ 3) + V * (if D z ≠ 0 ∧ z ≠ z₁ ∧ ‖z - s‖ < r then
            ‖D z‖ * (1 + Real.exp ((z.re - σ) * V)) else 0) :=
      (((hs1.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _).add (hsN.mul_left V)
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) hle) hR).trans (le_of_eq ?_)
    rw [Summable.tsum_add (((hs1.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _)
      (hsN.mul_left V), tsum_mul_left, Summable.tsum_add (hs1.mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_mul_left, tsum_mul_left]
  -- the archimedean-pole kernels
  have hE1 : ‖fejerWin V (-(σ : ℂ))‖ ≤ 2 * π ^ 2 / (V ^ 2 * σ ^ 3) := norm_fejerWin_neg_le hV0 hσ
  have hE2 : ‖fejerWin V (-s)‖ ≤ c * 2 / (V ^ 2 * 4 ^ 3) := by
    have h4 : (4 : ℝ) ≤ ‖(0 : ℂ) - s‖ := by
      rw [zero_sub, norm_neg]
      exact (four_le_abs_im_of_evenCoeff_zeta hz₁).trans (by
        rw [← hsim]; exact Complex.abs_im_le_norm s)
    have := norm_fejerWin_sub_le hV0 (by norm_num) (by linarith [Real.pi_pos]) h4
    rw [zero_sub, Complex.zero_re, hsre, ← hc] at this
    refine this.trans ?_
    have : Real.exp ((0 - σ) * V) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0.le)
    gcongr
    linarith
  -- assemble, in units of `u = 2π²/V²`
  set u : ℝ := 2 * π ^ 2 / V ^ 2 with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  set Pb : ℝ := 480 * Real.log 1080 * (1 / 64 + 3) +
    480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3) with hPb
  have hPle : P0 + P1 ≤ Pb := by
    have h0 : P0 ≤ 480 * Real.log 1080 * (1 / 64 + 3) := by
      refine hP0b.trans (le_of_eq ?_); norm_num
    rw [hPb]; linarith [hP1b]
  have hcu : c / V ^ 2 = u * (4 / 3) := by rw [hc, hu]; field_simp; ring
  have hE1' : 2 * π ^ 2 / (V ^ 2 * σ ^ 3) = u * (1 / σ ^ 3) := by rw [hu]; field_simp
  have hE2' : c * 2 / (V ^ 2 * 4 ^ 3) = u * (1 / 24) := by rw [hc, hu]; field_simp; norm_num
  have hDe : 0 ≤ ‖D z₁‖ * Real.exp κ := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hbig : ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) ≤
      u * (|M| * (1 / σ ^ 3 + 1 / 24) + 4 / 3 * (‖D z₁‖ * Real.exp κ) * Pb +
        8 / 3 * W * (1 / 64 + 1 / r ^ 3)) + V * Nn := by
    rw [← hLHS]
    refine hcore.trans ?_
    have h1 : |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤ u * (|M| * (1 / σ ^ 3 + 1 / 24)) := by
      calc |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤
            |M| * (u * (1 / σ ^ 3) + u * (1 / 24)) :=
            mul_le_mul_of_nonneg_left (add_le_add (hE1.trans_eq hE1') (hE2.trans_eq hE2'))
              (abs_nonneg M)
        _ = _ := by ring
    have h2 : c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) +
        c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) ≤
        u * (4 / 3 * (‖D z₁‖ * Real.exp κ) * Pb + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
      rw [hcu]
      have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
      have : ‖D z₁‖ * Real.exp κ * (P0 + P1) ≤ ‖D z₁‖ * Real.exp κ * Pb :=
        mul_le_mul_of_nonneg_left hPle hDe
      have e : u * (4 / 3) * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) +
          u * (4 / 3) * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) =
          u * (4 / 3 * (‖D z₁‖ * Real.exp κ * (P0 + P1)) + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hu0.le
      linarith
    linarith
  -- `V³/(κ(κ² + 4π²)) ≥ (8/3)Π`
  have hQ : θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2) = κ * (κ ^ 2 + 4 * π ^ 2) / V := by
    rw [hθdef]; field_simp
  have hQ0 : 0 < κ * (κ ^ 2 + 4 * π ^ 2) := by positivity
  have hexp : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ.le]
  have hlow : u * (8 / 3 * Pb * (‖D z₁‖ * (Real.exp κ - 1))) ≤
      ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) := by
    rw [hQ]
    have hX : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hexp
    have hk : u * (8 / 3 * Pb) ≤ 2 * π ^ 2 / (κ * (κ ^ 2 + 4 * π ^ 2) / V) := by
      rw [hu, div_div_eq_mul_div, le_div_iff₀ hQ0]
      have : 8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2)) ≤ V ^ 3 :=
        calc 8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2)) = 8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * Pb := by
              ring
          _ ≤ V ^ 3 := hV3
      calc 2 * π ^ 2 / V ^ 2 * (8 / 3 * Pb) * (κ * (κ ^ 2 + 4 * π ^ 2))
          = 2 * π ^ 2 / V ^ 2 * (8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2))) := by ring
        _ ≤ 2 * π ^ 2 / V ^ 2 * V ^ 3 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * π ^ 2 * V := by field_simp
    calc u * (8 / 3 * Pb * (‖D z₁‖ * (Real.exp κ - 1)))
        = u * (8 / 3 * Pb) * (‖D z₁‖ * (Real.exp κ - 1)) := by ring
      _ ≤ 2 * π ^ 2 / (κ * (κ ^ 2 + 4 * π ^ 2) / V) * (‖D z₁‖ * (Real.exp κ - 1)) :=
          mul_le_mul_of_nonneg_right hk hX
      _ = ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (κ * (κ ^ 2 + 4 * π ^ 2) / V)) := by ring
  have hVN : V * Nn = u * (V ^ 3 / (2 * π ^ 2) * Nn) := by rw [hu]; field_simp
  have hcomb := hlow.trans hbig
  rw [hVN, ← mul_add] at hcomb
  have hfin := le_of_mul_le_mul_left hcomb hu0
  linarith

/-! ### Multiplicities and coefficients of the modulated family -/

/-- Nontrivial zeros of `ζ` have `|γ| ≥ 4`. -/
theorem four_le_abs_im_of_mem_zetaCarrier {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    4 ≤ |ρ.im| := by
  by_contra h; push Not at h
  have hs : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
  exact riemannZeta_ne_zero_of_abs_im_lt_four hs.1 hs.2 h hρ.1

/-- **Multiplicity bound.** A nontrivial zero of `ζ` has multiplicity at most `40 log(180|γ|)`. -/
theorem mult_le_log_zeta {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    (zetaZeroConfig.mult ρ : ℝ) ≤ 40 * Real.log (180 * |ρ.im|) := by
  classical
  set d : XiDivisorSupport := xiDivisorZetaCarrierEquiv.symm ⟨ρ, hρ⟩ with hd
  have hdv : ((d : ℂ)) = ρ := rfl
  have hk : (MeromorphicOn.divisor xi Set.univ (d : ℂ)).toNat = zetaZeroConfig.mult ρ := by
    have := xiDivisorZetaCarrierEquiv_multiplicity d
    rw [this, hd, Equiv.apply_symm_apply]
  set F : Finset XiZeroCopy := Finset.univ.image fun i => (⟨d, i⟩ : XiZeroCopy) with hF
  have hinj : Function.Injective fun i : Fin (MeromorphicOn.divisor xi Set.univ (d : ℂ)).toNat =>
      (⟨d, i⟩ : XiZeroCopy) := fun i j h => by
    simpa using h
  have hcard : F.card = zetaZeroConfig.mult ρ := by
    rw [hF, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hk]
  have := card_le_of_ordinates_in_window (four_le_abs_im_of_mem_zetaCarrier hρ) F fun q hq => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
    simp [hdv]
  rwa [hcard] at this

/-- The decay constant of the unmodulated bump `κ_w`. -/
abbrev scaledBumpDecay (w : ℝ) : ℝ := bumpDecayConstant (scaledBump w)

theorem scaledBump_support' {w : ℝ} (hw : 0 < w) : ∀ u, scaledBump w u ≠ 0 → |u| ≤ w :=
  fun u hu => by
    by_contra h; push Not at h; exact hu (scaledBump_eq_zero hw h.le)

/-- `|h_w(x)| ≤ e^{w/2} B_w (1 + |Re x|)^{−2}` on the strip `|Im x| ≤ ½`. -/
theorem norm_paperFT_scaledBump_le {w : ℝ} (hw : 0 < w) {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ‖paperFT (scaledBump w) x‖ ≤ Real.exp (w / 2) * scaledBumpDecay w / (1 + |x.re|) ^ 2 := by
  have h := norm_paperFT_le_decay ((contDiff_scaledBump w).of_le (by norm_num)) (scaledBump_support' hw) x
  rw [← bumpDecayConstant] at h
  refine h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x.im])) (bumpDecayConstant_nonneg _))
    (by positivity))

/-- **Modulated coefficients decay away from the center.** For `½ + z` a zero,
`|F_c(z)| ≤ m (e^{w/2} B_w)² (1 + |Im z − c|)^{−4}`. -/
theorem norm_lagCoeff_modScaledBump_le (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ}
    (hz : (1 / 2 + z) ∈ Z.carrier) :
    ‖lagCoeff Z (modScaledBump w c) z‖ ≤ (Z.mult (1 / 2 + z) : ℝ) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + |z.im - c|) ^ 4 := by
  rw [lagCoeff_modScaledBump Z hw c hz, norm_mul, norm_pow, Complex.norm_natCast]
  have hstrip := Z.strip _ hz
  have hx : |(-(I * z) - (c : ℂ)).im| ≤ 1 / 2 := by
    simp at hstrip ⊢; rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hre : (-(I * z) - (c : ℂ)).re = z.im - c := by simp
  have h := norm_paperFT_scaledBump_le hw hx
  rw [hre] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  calc (Z.mult (1 / 2 + z) : ℝ) * ‖paperFT (scaledBump w) (-(I * z) - c)‖ ^ 2
      ≤ (Z.mult (1 / 2 + z) : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w / (1 + |z.im - c|) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = _ := by rw [div_pow, mul_pow, ← pow_mul]; ring

/-- **Two-sided decay of the merged coefficient.** For `ζ`,
`|D_c(z)| ≤ 40 log(180|Im z|)(e^{w/2}B_w)² ((1 + |Im z − c|)^{−4} + (1 + |Im z + c|)^{−4})`. -/
theorem norm_evenCoeff_modScaledBump_le {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ}
    (hz : evenCoeff zetaZeroConfig (modScaledBump w c) z ≠ 0) :
    ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤ 40 * Real.log (180 * |z.im|) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (1 / (1 + |z.im - c|) ^ 4 + 1 / (1 + |z.im + c|) ^ 4) := by
  have h4z : 4 ≤ |z.im| := four_le_abs_im_of_evenCoeff_zeta hz
  have hL0 : 0 ≤ Real.log (180 * |z.im|) := Real.log_nonneg (by linarith)
  set K := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      40 * Real.log (180 * |z.im|) * K / (1 + |z.im - c|) ^ 4 := by
    by_cases hc : (1 / 2 + z) ∈ zetaZeroConfig.carrier
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc).trans ?_
      have hm := mult_le_log_zeta hc
      have him : (1 / 2 + z).im = z.im := by simp
      rw [him] at hm
      gcongr
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  have h2 : ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖ ≤
      40 * Real.log (180 * |z.im|) * K / (1 + |z.im + c|) ^ 4 := by
    by_cases hc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc).trans ?_
      have hm := mult_le_log_zeta hc
      have him : (1 / 2 + conj z).im = -z.im := by simp
      rw [him, abs_neg] at hm
      rw [Complex.conj_im, show |-z.im - c| = |z.im + c| by
        rw [show -z.im - c = -(z.im + c) by ring, abs_neg]]
      gcongr
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  calc ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖
      ≤ ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ +
          ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖ := by
        rw [evenCoeff]; exact (norm_add_le _ _).trans (le_of_eq (by rw [Complex.norm_conj]))
    _ ≤ _ := by
        rw [mul_add, mul_one_div, mul_one_div]; exact add_le_add h1 h2

/-- **The coefficient at the center.** For a zero `½ + z₀` right of the line with `Im z₀ > 0`, the
bump modulated to `c = Im z₀` has
`|D_c(z₀)| ≥ (4w e^{−w/2} ∫κ)² − 40 log(180 Im z₀)(e^{w/2}B_w)²(1 + 2 Im z₀)^{−4}`. -/
theorem norm_evenCoeff_modScaledBump_center_ge {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre : 0 < z₀.re) (him : 0 < z₀.im) :
    (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u))) ^ 2 -
        40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
          (1 + 2 * z₀.im) ^ 4 ≤
      ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ := by
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre2 : z₀.re ≤ 1 / 2 := by
    have h2 : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2, h2]
  -- the zero itself, seen at the center
  have hmain : (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u))) ^ 2 ≤
      ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ := by
    rw [lagCoeff_modScaledBump zetaZeroConfig hw _ hz₀, norm_mul, norm_pow, Complex.norm_natCast]
    have hpt : -(I * z₀) - (z₀.im : ℂ) = ((-z₀.re : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hpt]
    have hlow := norm_paperFT_scaledBump_I_mul_ge hw (-z₀.re)
    have hb : 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) ≤
        4 * w * (Real.exp (-(w * |-z₀.re|)) * (∫ u, weilBump u)) := by
      have hint : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
      gcongr
      rw [abs_neg, abs_of_pos hre]; nlinarith
    have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z₀) := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ hz₀
    have h0 : 0 ≤ 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) := by
      have hint : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
      positivity
    have hsq := pow_le_pow_left₀ h0 (hb.trans hlow) 2
    calc (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u))) ^ 2
        ≤ ‖paperFT (scaledBump w) (((-z₀.re : ℝ) : ℂ) * I)‖ ^ 2 := hsq
      _ ≤ (zetaZeroConfig.mult (1 / 2 + z₀) : ℝ) *
            ‖paperFT (scaledBump w) (((-z₀.re : ℝ) : ℂ) * I)‖ ^ 2 :=
          le_mul_of_one_le_left (by positivity) hm
  -- the reflected zero, seen from the center at distance `2 Im z₀`
  have hconj : ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) (conj z₀)‖ ≤
      40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
        (1 + 2 * z₀.im) ^ 4 := by
    by_cases hc : (1 / 2 + conj z₀) ∈ zetaZeroConfig.carrier
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw _ hc).trans ?_
      have hm := mult_le_log_zeta hc
      have hci : (1 / 2 + conj z₀).im = -z₀.im := by simp
      rw [hci, abs_neg, abs_of_pos him] at hm
      rw [Complex.conj_im, show |-z₀.im - z₀.im| = 2 * z₀.im by
        rw [show -z₀.im - z₀.im = -(2 * z₀.im) by ring, abs_neg, abs_of_pos (by linarith)]]
      gcongr
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]
      have : 0 ≤ Real.log (180 * z₀.im) := by
        have h4 := four_le_abs_im_of_mem_zetaCarrier hz₀
        simp at h4; rw [abs_of_pos him] at h4; exact Real.log_nonneg (by linarith)
      positivity
  calc (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u))) ^ 2 -
        40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
          (1 + 2 * z₀.im) ^ 4
      ≤ ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ -
          ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) (conj z₀)‖ := by linarith
    _ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ := by
        rw [evenCoeff]
        have := norm_sub_norm_le (lagCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀)
          (-conj (lagCoeff zetaZeroConfig (modScaledBump w z₀.im) (conj z₀)))
        rw [norm_neg, Complex.norm_conj, sub_neg_eq_add] at this
        exact this

/-! ### Near-top zeros are seen by the modulated family, up to twins -/

/-- The cubic potential bound `Π(r, γ) = 480 log 1080 (1/64 + 3) + 480 log(180(|γ| + 6))(1/r³ + 3)`. -/
def twinPotential (r γ : ℝ) : ℝ :=
  480 * Real.log 1080 * (1 / 64 + 3) + 480 * Real.log (180 * (|γ| + 6)) * (1 / r ^ 3 + 3)

/-- The center amplitude `a_w = 4w e^{−w/2} ∫κ`, a lower bound for `|h_w(−iδ)|`, `δ ≤ ½`. -/
def centerAmplitude (w : ℝ) : ℝ := 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u))

/-- The threshold `C = |M|(8/x³ + 1/24) + (8/3)W(1/64 + 1/r³)` of the twin law at `σ ≥ x/2`. -/
def twinThreshold (M W x r : ℝ) : ℝ := |M| * (8 / x ^ 3 + 1 / 24) + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)

/-- The depth offset `κ = log(2 + 3e(C + 1)/(2Π a²))` at which a record of coefficient
`≥ a²/(2e)` cannot be quiet. -/
def twinKappa (M W x r γ a : ℝ) : ℝ :=
  Real.log (2 + 3 * Real.exp 1 * (twinThreshold M W x r + 1) / (2 * twinPotential r γ * a ^ 2))

theorem twinPotential_pos {r : ℝ} (hr : 0 < r) (γ : ℝ) : 0 < twinPotential r γ := by
  unfold twinPotential
  have h1 : 0 < Real.log 1080 := Real.log_pos (by norm_num)
  have h2 : 0 ≤ Real.log (180 * (|γ| + 6)) := Real.log_nonneg (by nlinarith [abs_nonneg γ])
  positivity

theorem centerAmplitude_pos {w : ℝ} (hw : 0 < w) : 0 < centerAmplitude w := by
  unfold centerAmplitude
  have h : (0 : ℝ) < ∫ u, weilBump u := weilBump.integral_pos
  positivity

/-- **The two-parameter dichotomy for `ζ`.** Let `w > 0`, `V ≥ π`, and let `½ + z₀` be a zero right of
the line, at height `γ₀ = Im z₀ > 0` with `40 log(180γ₀)(e^{w/2}B_w)²(1 + 2γ₀)^{−4} ≤ a_w²/2`, which is
`1/V`-near the top: every exponent has `Re z ≤ Re z₀ + 1/V`. Modulate the bump to `γ₀`. If the
difference tests are Weil nonnegative at every lag `v ∈ [0, V]`, then the Legendre record `z*` at lag
`V` exists, and for every `r` with `Vr ≥ 4π`, `κ = twinKappa`, `V ≥ 2κ/Re z*` and
`V³ ≥ (8/3)κ(κ² + 4π²)Π(r, Im z*)`, some other exponent lies within `r` of
`(Re z* − κ/V) + i Im z*`. -/
theorem zeta_modulated_near_top_twin {w V : ℝ} (hw : 0 < w) (hV : π ≤ V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) (him₀ : 0 < z₀.im)
    (hΓ : 40 * Real.log (180 * z₀.im) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
      (1 + 2 * z₀.im) ^ 4 ≤ centerAmplitude w ^ 2 / 2)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ 0 < z₁.re ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∀ r : ℝ, 0 < r → 4 * π ≤ V * r →
        2 * twinKappa (2 * (lagStructure zetaZeroConfig (modScaledBump w z₀.im) 0).re)
          (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖) z₁.re r z₁.im
          (centerAmplitude w) / z₁.re ≤ V →
        8 / 3 * (twinKappa (2 * (lagStructure zetaZeroConfig (modScaledBump w z₀.im) 0).re)
          (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖) z₁.re r z₁.im
          (centerAmplitude w) * (twinKappa (2 * (lagStructure zetaZeroConfig
            (modScaledBump w z₀.im) 0).re)
          (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖) z₁.re r z₁.im
          (centerAmplitude w) ^ 2 + 4 * π ^ 2)) * twinPotential r z₁.im ≤ V ^ 3 →
        ∃ z, z ≠ z₁ ∧ evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - ((z₁.re - twinKappa (2 * (lagStructure zetaZeroConfig
            (modScaledBump w z₀.im) 0).re)
          (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖) z₁.re r z₁.im
          (centerAmplitude w) / V : ℝ) + z₁.im * I)‖ < r := by
  classical
  set b := modScaledBump w z₀.im with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w _
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := modScaledBump_support hw _
  set D := evenCoeff zetaZeroConfig b with hDdef
  have hV0 : 0 < V := lt_of_lt_of_le Real.pi_pos hV
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  -- the coefficient at the center is at least `a²/2`
  have hD₀ : a ^ 2 / 2 ≤ ‖D z₀‖ := by
    have := norm_evenCoeff_modScaledBump_center_ge hw hz₀ hre₀ him₀
    rw [show 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) = a from rfl] at this
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hD₀; nlinarith
  obtain ⟨z₁, hz₁, hre₁, hrec⟩ := exists_right_record zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hbs hV0.le hD₀ne hre₀
  refine ⟨z₁, hz₁, hre₁, hrec, fun r hr hVr hκV hV3 => ?_⟩
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set Pb := twinPotential r z₁.im with hPb
  set C := twinThreshold M W z₁.re r with hC
  set κ := twinKappa M W z₁.re r z₁.im a with hκ
  -- the record is at least `e^{−1}` as loud as `z₀` at the coefficient level
  have hD₁ : a ^ 2 / (2 * Real.exp 1) ≤ ‖D z₁‖ := by
    have h1 := hrec z₀ hD₀ne hre₀
    have h2 := htop z₁ hz₁
    have h3 : Real.exp (z₁.re * V) ≤ Real.exp (z₀.re * V) * Real.exp 1 := by
      rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
      have : (z₁.re - z₀.re) * V ≤ 1 := by
        have := mul_le_mul_of_nonneg_right (show z₁.re - z₀.re ≤ 1 / V by linarith) hV0.le
        rwa [div_mul_cancel₀ _ hV0.ne'] at this
      linarith
    have h4 : ‖D z₀‖ * Real.exp (z₀.re * V) ≤ ‖D z₁‖ * (Real.exp (z₀.re * V) * Real.exp 1) :=
      h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
    have hE := Real.exp_pos (z₀.re * V)
    have h5 : ‖D z₀‖ ≤ ‖D z₁‖ * Real.exp 1 := by
      have : ‖D z₀‖ * Real.exp (z₀.re * V) ≤ (‖D z₁‖ * Real.exp 1) * Real.exp (z₀.re * V) := by
        linarith
      exact le_of_mul_le_mul_right this hE
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hPb0 : 0 < Pb := twinPotential_pos hr _
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hC0 : 0 ≤ C := by rw [hC, twinThreshold]; positivity
  have hfrac : 0 ≤ 3 * Real.exp 1 * (C + 1) / (2 * Pb * a ^ 2) :=
    div_nonneg (mul_nonneg (by positivity) (by linarith))
      (mul_pos (mul_pos two_pos hPb0) (pow_pos ha0 2)).le
  have hκ0 : 0 < κ := by
    rw [hκ, twinKappa, ← hC, ← hPb]; exact Real.log_pos (by linarith)
  have hexpκ : Real.exp κ = 2 + 3 * Real.exp 1 * (C + 1) / (2 * Pb * a ^ 2) := by
    rw [hκ, twinKappa, ← hC, ← hPb]; exact Real.exp_log (by linarith)
  have hσ : z₁.re / 2 ≤ z₁.re - κ / V := by
    have : κ / V ≤ z₁.re / 2 := by
      rw [div_le_iff₀ hV0]; rw [div_le_iff₀ hre₁] at hκV; linarith
    linarith
  have hσ0 : 0 < z₁.re - κ / V := by linarith
  by_contra hno
  push Not at hno
  have hPbeq : Pb = 480 * Real.log 1080 * (1 / 64 + 3) +
      480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3) := by rw [hPb, twinPotential]
  have hlaw := zeta_twin_law_of_bump hb hbs hV hm hz₁ hrec hκ0 hσ0 hr hVr (by
    rw [← hPbeq]; exact hV3)
  -- the near zone is empty
  have hnear : ∑' z : ℂ, (if evenCoeff zetaZeroConfig b z ≠ 0 ∧ z ≠ z₁ ∧
      ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ < r then
        ‖evenCoeff zetaZeroConfig b z‖ * (1 + Real.exp ((z.re - (z₁.re - κ / V)) * V)) else 0) =
      0 := by
    refine (tsum_congr fun z => ?_).trans tsum_zero
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact absurd (hno z h2 h1) (not_le.mpr h3)
  rw [hnear, mul_zero, add_zero] at hlaw
  -- the record is not quiet for this `κ`
  have hσ3 : 1 / (z₁.re - κ / V) ^ 3 ≤ 8 / z₁.re ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (by positivity) hσ 3
    nlinarith
  have hRHS : |M| * (1 / (z₁.re - κ / V) ^ 3 + 1 / 24) + 8 / 3 * W * (1 / 64 + 1 / r ^ 3) ≤ C := by
    rw [hC, twinThreshold]
    have := mul_le_mul_of_nonneg_left (add_le_add_right hσ3 (1 / 24)) (abs_nonneg M)
    linarith
  have hLHS : C + 1 ≤ 4 / 3 * Pb * ‖D z₁‖ * (Real.exp κ - 2) := by
    rw [hexpκ, show 2 + 3 * Real.exp 1 * (C + 1) / (2 * Pb * a ^ 2) - 2 =
      3 * Real.exp 1 * (C + 1) / (2 * Pb * a ^ 2) by ring]
    have hE := Real.exp_pos 1
    calc C + 1 = 4 / 3 * Pb * (a ^ 2 / (2 * Real.exp 1)) *
          (3 * Real.exp 1 * (C + 1) / (2 * Pb * a ^ 2)) := by field_simp; ring
      _ ≤ 4 / 3 * Pb * ‖D z₁‖ * (3 * Real.exp 1 * (C + 1) / (2 * Pb * a ^ 2)) := by
          gcongr
  rw [← hPbeq] at hlaw
  linarith

/-- **Records stay near the center.** For the bump modulated to `c ≥ 0`, an exponent of `ζ` whose
coefficient is at least `ε > 0` lies at height `|Im z| ≤ max(2c, (2880 K)^{1/3})`,
`K = 80 (e^{w/2}B_w)²/ε`: the decay `(1 + ||Im z| − c|)^{−4}` beats the multiplicity `O(log |Im z|)`. -/
theorem abs_im_le_of_norm_evenCoeff_modScaledBump_ge {w c ε : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hε : 0 < ε) {z : ℂ} (hz : evenCoeff zetaZeroConfig (modScaledBump w c) z ≠ 0)
    (hge : ε ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖) :
    |z.im| ≤ max (2 * c) ((2880 * (80 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / ε)) ^
      ((1 : ℝ) / 3)) := by
  set y := |z.im| with hy
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  have h4 : 4 ≤ y := four_le_abs_im_of_evenCoeff_zeta hz
  rcases le_or_gt y (2 * c) with h | h
  · exact le_max_of_le_left h
  refine le_max_of_le_right ?_
  -- both distances `|Im z ∓ c|` are at least `y/2`
  have hd1 : y / 2 ≤ |z.im - c| := by
    have := abs_sub_abs_le_abs_sub z.im c
    rw [abs_of_nonneg hc] at this; linarith
  have hd2 : y / 2 ≤ |z.im + c| := by
    have := abs_sub_abs_le_abs_sub z.im (-c)
    rw [abs_neg, abs_of_nonneg hc, sub_neg_eq_add] at this; linarith
  have hb := norm_evenCoeff_modScaledBump_le hw c hz
  rw [← hK₀] at hb
  have hlog : Real.log (180 * y) ≤ 180 * y := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 180 * y by linarith); linarith
  have hy4 : (0 : ℝ) < (1 + y / 2) ^ 4 := by positivity
  have hinv1 : 1 / (1 + |z.im - c|) ^ 4 ≤ 1 / (1 + y / 2) ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) hy4 (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hinv2 : 1 / (1 + |z.im + c|) ^ 4 ≤ 1 / (1 + y / 2) ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) hy4 (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hL0 : 0 ≤ Real.log (180 * y) := Real.log_nonneg (by linarith)
  -- `ε (1 + y/2)⁴ ≤ 80 K₀ · 180 y`
  have hkey : ε * (1 + y / 2) ^ 4 ≤ 80 * K₀ * (180 * y) := by
    have h1 : ε ≤ 40 * Real.log (180 * y) * K₀ * (2 / (1 + y / 2) ^ 4) := by
      refine hge.trans (hb.trans ?_)
      have := add_le_add hinv1 hinv2
      rw [show 2 / (1 + y / 2) ^ 4 = 1 / (1 + y / 2) ^ 4 + 1 / (1 + y / 2) ^ 4 by ring]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    rw [show 40 * Real.log (180 * y) * K₀ * (2 / (1 + y / 2) ^ 4) =
      80 * K₀ * Real.log (180 * y) / (1 + y / 2) ^ 4 by ring, le_div_iff₀ hy4] at h1
    have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 80 * K₀ by positivity)
    linarith
  -- hence `y³ ≤ 2880 · 80 K₀/ε`
  have hy3 : y ^ 3 ≤ 2880 * (80 * K₀ / ε) := by
    have h1 : y ^ 4 / 16 ≤ (1 + y / 2) ^ 4 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ y / 2) (by linarith : y / 2 ≤ 1 + y / 2) 4
      calc y ^ 4 / 16 = (y / 2) ^ 4 := by ring
        _ ≤ _ := this
    have h2 : ε * (y ^ 4 / 16) ≤ 80 * K₀ * (180 * y) :=
      (mul_le_mul_of_nonneg_left h1 hε.le).trans hkey
    rw [mul_div_assoc', le_div_iff₀ hε]
    have hy0 : 0 < y := by linarith
    nlinarith
  have hrt := Real.rpow_le_rpow (by positivity) hy3 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by
    norm_num, Real.rpow_one] at hrt

end GaloisForLFunctions.SquareRootThreshold
