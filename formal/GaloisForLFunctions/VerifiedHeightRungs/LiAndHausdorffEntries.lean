import GaloisForLFunctions.RHTower.LiFirstCoefficientsNonneg
import GaloisForLFunctions.RHTower.VerifiedHeightAmplification
import GaloisForLFunctions.RHTower.PrimeArchOrderTwentyHausdorffSourceBand

/-!
# Li entries and Hausdorff rows from a verified height

If RH is verified through height `T`, every off-line zero has `|γ| > T`, and at such a zero the terms
of two RH ladders keep their sign well beyond the unconditional range:

* **Li** (`re_xiLiPaired_nonneg_of_rhVerifiedThrough`): `Re(2λ_n) ≥ 0` for every `n ≤ (47/10) T`. The
  Cayley image `w_ρ = 1 − 1/ρ` has `|arg w_ρ| ≤ |γ|/(γ² − ¼)` and log-modulus at most the angle, so its
  term is nonnegative as long as `n |arg w_ρ| ≤ 3π/2`.
* **Hausdorff** (`scaledHausdorffMomentDifference_nonneg_of_rhVerifiedThrough`): the calibrated
  difference `(k, r)` of the endpoint tower is nonnegative for `k + 1 ≤ (3/2)(T − 1)` and `r ≤ R T³`,
  `R` the endpoint radius. The reciprocal square `z = (γ − iδ)⁻²` has argument `≤ 1/(T − 1)` and
  `|Im z| ≤ T⁻³`; the complement `R − z` has the opposite phase, so the two arguments do not add.

Both are atomwise, so no comparison of on-line mass with off-line mass enters.
-/

open Complex
open scoped Real

noncomputable section

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower

/-- **Verified heights push off-line zeros up**: an off-line zero of `ξ` in the strip has `|γ| > T`. -/
theorem lt_abs_im_of_rhVerifiedThrough {T : ℝ} (hv : RHVerifiedThrough T) {ρ : ℂ} (hρ : xi ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2) : T < |ρ.im| := by
  by_contra hle
  push Not at hle
  have hγ := im_sq_ge_of_xi_eq_zero_of_re_ne_half hρ hoff
  have him0 : ρ.im ≠ 0 := by
    intro h
    rw [h] at hγ
    norm_num at hγ
  rcases lt_or_gt_of_ne him0 with hneg | hpos
  · have hconj : xi ((starRingEnd ℂ) ρ) = 0 := by rw [xi_conj, hρ, map_zero]
    have hre := hv hconj (by simpa using h0) (by simpa using h1) (by simpa using hneg)
      (by simpa [abs_of_neg hneg] using hle)
    exact hoff (by simpa using hre)
  · exact hoff (hv hρ h0 h1 hpos ((le_abs_self _).trans hle))

/-! ### Li entries -/

/-- One paired Li term stays nonnegative at a zero above the verified height. -/
theorem re_liTerm_xiRootW_nonneg_of_rhVerifiedThrough {T : ℝ} (hT : 14 ≤ T)
    (hv : RHVerifiedThrough T) {ρ : ℂ} (hρ : xi ρ = 0) (hβ0 : 0 < ρ.re) (hβ1 : ρ.re < 1) {n : ℕ}
    (hn : (n : ℝ) ≤ 47 / 10 * T) : 0 ≤ (liTerm (xiRootW ρ) n).re := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hβ0
    simp at hβ0
  by_cases hoff : ρ.re = 1 / 2
  · exact re_liTerm_nonneg_of_norm_eq_one ((norm_xiRootW_eq_one_iff hρ0).mpr hoff) n
  have hγ := im_sq_ge_of_xi_eq_zero_of_re_ne_half hρ hoff
  have hθ := abs_arg_xiRootW_le hβ0 hβ1 hγ
  have hx := abs_log_norm_xiRootW_le_abs_arg hβ0 hβ1 hγ
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hβ1
    simp at hβ1
  have hw0 : xiRootW ρ ≠ 0 := xiRootW_ne_zero hρ0 hρ1
  refine re_liTerm_nonneg_of_angle hw0 hx ?_
  have hg := lt_abs_im_of_rhVerifiedThrough hv hρ hβ0 hβ1 hoff
  set g := |ρ.im| with hgdef
  have hg2 : g ^ 2 = ρ.im ^ 2 := sq_abs _
  have hg0 : 0 ≤ g := abs_nonneg _
  have hden : 0 < ρ.im ^ 2 - 1 / 4 := by linarith only [hγ]
  have hπ : (3 : ℝ) * 3.14 / 2 ≤ 3 * π / 2 := by linarith only [Real.pi_gt_d2]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg14 : 14 ≤ g := by linarith only [hg, hT]
  calc (n : ℝ) * |Complex.arg (xiRootW ρ)| ≤ (47 / 10 * T) * (g / (ρ.im ^ 2 - 1 / 4)) :=
        mul_le_mul hn hθ (abs_nonneg _) (by linarith only [hT])
    _ ≤ 3 * 3.14 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hden, ← hg2]
        nlinarith only [hg, hg14, hg0, hT]
    _ ≤ 3 * π / 2 := hπ

/-- **Li entries from a verified height.** If RH is verified through `T ≥ 14`, then `Re(2λ_n) ≥ 0` for
every `n ≤ (47/10) T`. -/
theorem re_xiLiPaired_nonneg_of_rhVerifiedThrough {T : ℝ} (hT : 14 ≤ T) (hv : RHVerifiedThrough T)
    {n : ℕ} (hn : (n : ℝ) ≤ 47 / 10 * T) : 0 ≤ (xiLiPaired n).re := by
  rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
  refine tsum_nonneg fun ρ => ?_
  rw [xiLiPairedTerm, Complex.re_ofReal_mul]
  have hstrip := xi_divisor_support_re_mem_open_unit ρ
  exact mul_nonneg (by have := xi_divisor_pos_on_support ρ; exact_mod_cast this.le)
    (re_liTerm_xiRootW_nonneg_of_rhVerifiedThrough hT hv (xi_eq_zero_of_mem_divisor_support ρ)
      hstrip.1 hstrip.2 hn)

/-! ### Hausdorff rows -/

/-- Two right-facing numbers of opposite phase: the arguments of `z^p w^r` do not add. -/
theorem re_pow_mul_pow_nonneg_of_opposite_phase {z w : ℂ} {p r : ℕ} {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B) (hzre : 0 < z.re) (hwre : 0 < w.re) (hwim : w.im = -z.im)
    (hzs : A * |z.im| ≤ z.re) (hws : B * |w.im| ≤ w.re) (hp : (p : ℝ) ≤ 3 / 2 * A)
    (hr : (r : ℝ) ≤ 3 / 2 * B) : 0 ≤ (z ^ p * w ^ r).re := by
  have hzarg : |z.arg| ≤ 1 / A := abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hA]
    linarith only [hzs])
  have hwarg : |w.arg| ≤ 1 / B := abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hB]
    linarith only [hws])
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  set x : ℝ := (p : ℝ) * z.arg with hx
  set y : ℝ := (r : ℝ) * w.arg with hy
  have hxb : |x| ≤ 3 / 2 := by
    rw [hx, abs_mul, abs_of_nonneg hp0]
    calc (p : ℝ) * |z.arg| ≤ (3 / 2 * A) * (1 / A) :=
          mul_le_mul hp hzarg (abs_nonneg _) (by positivity)
      _ = 3 / 2 := by field_simp
  have hyb : |y| ≤ 3 / 2 := by
    rw [hy, abs_mul, abs_of_nonneg hr0]
    calc (r : ℝ) * |w.arg| ≤ (3 / 2 * B) * (1 / B) :=
          mul_le_mul hr hwarg (abs_nonneg _) (by positivity)
      _ = 3 / 2 := by field_simp
  have hsign : (0 ≤ x ∧ y ≤ 0) ∨ (x ≤ 0 ∧ 0 ≤ y) := by
    have hargw : ∀ u : ℂ, 0 < u.re → u.im ≤ 0 → u.arg ≤ 0 := fun u hu him => by
      rw [arg_eq_arctan_of_re_pos hu]
      have hratio : 0 ≤ -(u.im / u.re) := neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg him hu.le)
      have h := Real.arctan_nonneg.mpr hratio
      rw [Real.arctan_neg] at h
      linarith only [h]
    rcases le_total 0 z.im with h | h
    · left
      refine ⟨mul_nonneg hp0 (Complex.arg_nonneg_iff.mpr h), ?_⟩
      exact mul_nonpos_of_nonneg_of_nonpos hr0 (hargw w hwre (by rw [hwim]; linarith only [h]))
    · right
      refine ⟨mul_nonpos_of_nonneg_of_nonpos hp0 (hargw z hzre h), ?_⟩
      exact mul_nonneg hr0 (Complex.arg_nonneg_iff.mpr (by rw [hwim]; linarith only [h]))
  have hxb' := abs_le.mp hxb
  have hyb' := abs_le.mp hyb
  have hπ : (3 : ℝ) / 2 < π / 2 := by linarith only [Real.pi_gt_three]
  rw [pow_mul_pow_re_eq_norm_cos]
  refine mul_nonneg (mul_nonneg (pow_nonneg (norm_nonneg z) p) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_pos_of_mem_Ioo ?_).le
  rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Coordinates of the reciprocal square at a zero above the verified height. -/
theorem xiZeroCopyReciprocalSquare_bounds {T : ℝ} (hT : 15 ≤ T) {q : XiZeroCopy}
    (hg : T < |(q.1 : ℂ).im|) (h0 : 0 < (q.1 : ℂ).re) (h1 : (q.1 : ℂ).re < 1) :
    (T - 1) * |(xiZeroCopyReciprocalSquare q).im| ≤ (xiZeroCopyReciprocalSquare q).re ∧
      T ^ 3 * |(xiZeroCopyReciprocalSquare q).im| ≤ 1 := by
  rw [xiZeroCopyReciprocalSquare_re_formula, xiZeroCopyReciprocalSquare_im_formula]
  set δ := (q.1 : ℂ).re - 1 / 2 with hδ
  set γ := (q.1 : ℂ).im with hγ
  have hδ1 : |2 * δ| ≤ 1 := by
    rw [abs_le]
    constructor <;> rw [hδ] <;> linarith only [h0, h1]
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by
    have := sq_abs (2 * δ)
    nlinarith only [this, hδ1, abs_nonneg (2 * δ)]
  have hg0 : 0 < |γ| := by linarith only [hg, hT]
  have hg2 : γ ^ 2 = |γ| ^ 2 := (sq_abs γ).symm
  set D := δ ^ 2 + γ ^ 2 with hD
  have hDpos : 0 < D := by nlinarith only [hg0, hg2, sq_nonneg δ]
  have hD2 : 0 < D ^ 2 := by positivity
  have habs : |2 * δ * γ / D ^ 2| = |2 * δ| * |γ| / D ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos hD2]
  rw [habs]
  have hnum : |2 * δ| * |γ| ≤ |γ| := by
    nlinarith only [mul_le_mul_of_nonneg_right hδ1 hg0.le]
  have hTg : T ≤ |γ| := hg.le
  constructor
  · rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hD2.le
    have h2 : (T - 1) * |γ| ≤ |γ| ^ 2 - 1 / 4 := by nlinarith only [hTg, hg0, hT]
    have h3 : (T - 1) * (|2 * δ| * |γ|) ≤ (T - 1) * |γ| :=
      mul_le_mul_of_nonneg_left hnum (by linarith only [hT])
    rw [hg2]
    linarith only [h2, h3, hδ2]
  · rw [← mul_div_assoc, div_le_one hD2]
    have hT3 : T ^ 3 ≤ |γ| ^ 3 := pow_le_pow_left₀ (by linarith only [hT]) hTg 3
    have h4 : T ^ 3 * (|2 * δ| * |γ|) ≤ |γ| ^ 3 * |γ| :=
      mul_le_mul hT3 hnum (by positivity) (by positivity)
    have h5 : |γ| ^ 4 ≤ D ^ 2 := by
      have hle : |γ| ^ 2 ≤ D := by rw [hD, ← hg2]; linarith only [sq_nonneg δ]
      calc |γ| ^ 4 = (|γ| ^ 2) ^ 2 := by ring
        _ ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    calc T ^ 3 * (|2 * δ| * |γ|) ≤ |γ| ^ 3 * |γ| := h4
      _ = |γ| ^ 4 := by ring
      _ ≤ D ^ 2 := h5

/-- **Hausdorff rows from a verified height.** If RH is verified through `T ≥ 15`, the calibrated
endpoint difference `(k, r)` is nonnegative for `k + 1 ≤ (3/2)(T − 1)` and `r ≤ R T³`. -/
theorem scaledHausdorffMomentDifference_nonneg_of_rhVerifiedThrough {T : ℝ} (hT : 15 ≤ T)
    (hv : RHVerifiedThrough T) {k r : ℕ} (hk : ((k + 1 : ℕ) : ℝ) ≤ 3 / 2 * (T - 1))
    (hr : (r : ℝ) ≤ primeArchEndpointHausdorffRadius * T ^ 3) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius k r)]
  refine tsum_nonneg fun q => ?_
  change 0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
    ((primeArchEndpointHausdorffRadius : ℂ) - xiZeroCopyReciprocalSquare q) ^ r).re
  set z := xiZeroCopyReciprocalSquare q with hz
  set R := primeArchEndpointHausdorffRadius with hRdef
  set w : ℂ := (R : ℂ) - z with hw
  have hzre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      rw [hz, xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hzReal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hwReal : w = ((R - z.re : ℝ) : ℂ) := by
      rw [hw, hzReal]
      norm_num
    have hzleR : z.re ≤ R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre.le _) (pow_nonneg (sub_nonneg.mpr hzleR) r)
  · have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hon
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hg := lt_abs_im_of_rhVerifiedThrough hv (xi_eq_zero_of_mem_divisor_support q.1)
      hstrip.1 hstrip.2 hon
    obtain ⟨hz1, hz2⟩ := xiZeroCopyReciprocalSquare_bounds hT hg hstrip.1 hstrip.2
    have hwre : 0 < w.re := by
      rw [hw]
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith only [hzQuarter, hR]
    have hwim : w.im = -z.im := by
      rw [hw]
      simp
    have hT3 : 0 < T ^ 3 := by have : 0 < T := by linarith only [hT]
                               positivity
    refine re_pow_mul_pow_nonneg_of_opposite_phase (A := T - 1) (B := 3 / 4 * R * T ^ 3)
      (by linarith only [hT]) (by positivity) hzre hwre hwim hz1 ?_ hk ?_
    · rw [hwim, abs_neg]
      have h1 : 3 / 4 * R * T ^ 3 * |z.im| = 3 / 4 * R * (T ^ 3 * |z.im|) := by ring
      rw [h1]
      have h2 : 3 / 4 * R * (T ^ 3 * |z.im|) ≤ 3 / 4 * R * 1 :=
        mul_le_mul_of_nonneg_left hz2 (by positivity)
      rw [hw]
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith only [h2, hzQuarter]
    · have hle : R * T ^ 3 ≤ 3 / 2 * (3 / 4 * R * T ^ 3) := by
        nlinarith only [mul_pos hR hT3]
      exact hr.trans hle

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.re_xiLiPaired_nonneg_of_rhVerifiedThrough
#print axioms GaloisForLFunctions.VerifiedHeightRungs.scaledHausdorffMomentDifference_nonneg_of_rhVerifiedThrough
