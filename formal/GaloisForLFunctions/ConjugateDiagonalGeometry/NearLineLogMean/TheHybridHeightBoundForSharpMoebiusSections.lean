import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.HTGeometry.SmoothWeightSharpMellin
import GaloisForLFunctions.RHTower.ZetaVerticalMeanSquare

/-!
# The height cost of a sharp Möbius section on the critical line

A smooth Mellin cutoff, as in El Kaouni (arXiv:2610.42022, Appendix F),
can agree with a sharp cutoff at every integer. Translating the reciprocal
zeta function before moving the contour keeps the height and the cutoff
independent. The remaining power of height in the integrated bound is
arbitrarily close to the length of the interval.
-/

noncomputable section

open Complex Filter MeasureTheory Finset
open scoped Topology Interval
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.MultiscaleMollifiedZetaField
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg
  zetaZeroWidth_eq_zetaZeroAbscissa_sub_half)
open RHTower (mobCoeff edPoly zetaZeroAbscissa half_le_zetaZeroAbscissa zetaZeroAbscissa_le_one
  riemannZeta_ne_zero_of_zetaZeroAbscissa_lt exists_invZeta_shift_data_of_zeroFree
  exists_integral_normSq_zeta_critical_le)
open RHTower.Sieve (invZeta tsum_moebius_cpow_eq_invZeta)

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def lineCoeff (u : ℝ) (n : ℕ) : ℂ := mobCoeff n * (n : ℂ) ^ (-linePoint u)

private theorem lineCoeff_zero (u : ℝ) : lineCoeff u 0 = 0 := by simp [lineCoeff, mobCoeff]

private theorem norm_lineCoeff_le_one (u : ℝ) (n : ℕ) : ‖lineCoeff u n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lineCoeff_zero]
  have hm : ‖mobCoeff n‖ ≤ 1 := by
    rw [mobCoeff, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hline : linePoint u = (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
    unfold linePoint
    norm_num
  rw [lineCoeff, norm_mul, hline, norm_natCast_cpow_neg_line hn]
  exact mul_le_one₀ hm (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by norm_num))

private theorem sharp_section_perron (u : ℝ) {N : ℕ} (hN : 0 < N) :
    (2 * Real.pi : ℝ) • moebiusPoly N (linePoint u) =
    ∫ y : ℝ, invZeta (linePoint u + ((2 : ℂ) + (y : ℂ) * I)) *
      mellin (fun x : ℝ => (smoothWeight N 1 x : ℂ)) ((2 : ℂ) + (y : ℂ) * I) := by
  have hcut : (∑' n : ℕ, lineCoeff u n * (smoothWeight N 1 (n : ℝ) : ℂ)) =
      moebiusPoly N (linePoint u) := by
    rw [tsum_eq_sum (s := Icc 1 N)]
    · refine sum_congr rfl fun n hn => ?_
      rw [smoothWeight_eq_one zero_lt_one (Nat.cast_le.mpr (mem_Icc.mp hn).2)]
      simp [lineCoeff]
    · intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp [lineCoeff_zero]
      · have h : N + 1 ≤ n := by
          by_contra! h
          exact hn (mem_Icc.mpr ⟨hp, by omega⟩)
        rw [smoothWeight_eq_zero zero_lt_one (by exact_mod_cast h)]
        simp
  have hseries (z : ℂ) (hz : 1 < (linePoint u + z).re) :
      (∑' n : ℕ, lineCoeff u n * (n : ℂ) ^ (-z)) = invZeta (linePoint u + z) := by
    rw [← tsum_moebius_cpow_eq_invZeta hz]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [lineCoeff_zero]
    · change mobCoeff n * (n:ℂ)^(-linePoint u) * (n:ℂ)^(-z) = mobCoeff n * (n:ℂ)^(-(linePoint u+z))
      rw [mul_assoc, ←Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne'),neg_add]
  have hper := tsum_mul_smoothWeight_eq_integral (norm_lineCoeff_le_one u) (lineCoeff_zero u)
    (Nat.cast_pos.mpr hN) (H := 1) zero_lt_one (σ := 2) (by norm_num)
  rw [hcut] at hper
  refine hper.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_))
  push_cast
  rw [hseries _ (by norm_num [Complex.add_re, linePoint_re])]

/-- The critical-line translates of the regular reciprocal grow subpolynomially
in both imaginary coordinates, with a single strip constant. -/
private theorem translated_reciprocal {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    let c := zetaZeroWidth + e
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ,
      DifferentiableOn ℂ (fun z => invZeta (linePoint u + z)) (HTGeometry.verticalStrip c 2) ∧
      ∀ z ∈ HTGeometry.verticalStrip c 2, ‖invZeta (linePoint u + z)‖ ≤
        (K * (2 + |u|) ^ e) * (2 + |z.im|) ^ e := by
  intro c
  obtain ⟨K, hK, hdiff, hbound⟩ := exists_invZeta_shift_data_of_zeroFree
    half_le_zetaZeroAbscissa zetaZeroAbscissa_le_one
    (fun _ hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) he he1 he (5 / 2)
  refine ⟨K, hK, fun u => ?_⟩
  have hmap : Set.MapsTo (fun z => linePoint u + z) (HTGeometry.verticalStrip c 2)
      (HTGeometry.verticalStrip (zetaZeroAbscissa + e) (5 / 2)) := by
    intro z hz
    obtain ⟨hl, hh⟩ := hz
    dsimp only [c] at hl
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half] at hl
    change _ ≤ (linePoint u + z).re ∧ (linePoint u + z).re ≤ _
    rw [Complex.add_re, linePoint_re]
    constructor <;> linarith
  refine ⟨hdiff.comp ((differentiableOn_const (linePoint u)).add differentiableOn_id) hmap, fun z hz => ?_⟩
  have hsum : 2 + |(linePoint u + z).im| ≤ (2 + |u|) * (2 + |z.im|) := by
    rw [Complex.add_im, linePoint_im]
    nlinarith only [abs_add_le u z.im, abs_nonneg u, abs_nonneg z.im,
      mul_nonneg (abs_nonneg u) (abs_nonneg z.im)]
  have hpow := Real.rpow_le_rpow (by positivity) hsum he.le
  rw [Real.mul_rpow (by positivity) (by positivity)] at hpow
  exact (hbound _ (hmap hz)).trans ((mul_le_mul_of_nonneg_left hpow hK).trans_eq (mul_assoc _ _ _).symm)

/-- Uniform sharp-cutoff estimate, with independent loss in length and height. -/
theorem hybrid_moebius_section_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (u : ℝ), ‖moebiusPoly N (linePoint u)‖ ≤
      C * ((N : ℝ) + 1) ^ (zetaZeroWidth + ε) * (2 + |u|) ^ ε := by
  let e := min ε 1 / 8
  have he : 0 < e := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have he1 : 8 * e ≤ 1 := by dsimp only [e]; linarith only [min_le_right ε 1]
  have heε : 8 * e ≤ ε := by dsimp only [e]; linarith only [min_le_left ε 1]
  let c := zetaZeroWidth + e
  let q := 2 * e
  have hc : 0 < c := add_pos_of_nonneg_of_pos zetaZeroWidth_nonneg he
  have hc2 : c ≤ 2 := by
    dsimp only [c]; rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    linarith only [he1, zetaZeroAbscissa_le_one]
  have hq : e < q := by dsimp only [q]; linarith
  have hq1 : q ≤ 1 := by dsimp only [q]; linarith
  obtain ⟨K, hK, hstrip⟩ := translated_reciprocal he (by linarith)
  obtain ⟨C₀, C₁, h₀, h₁, hfrac⟩ := exists_integral_norm_mul_mellin_smoothWeight_fractional_bound
  let P := C₀ ^ (1 - q) * C₁ ^ q
  have hP : 0 ≤ P := mul_nonneg (Real.rpow_nonneg (zero_le_one.trans h₀) _)
    (Real.rpow_nonneg (zero_le_one.trans h₁) _)
  let C := 2 * K * 3 ^ e * (1 / c + P / (q - e))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C / (2 * Real.pi), by positivity, fun N u => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [moebiusPoly, edPoly]
    positivity
  let X := (N : ℝ) + 1
  let V := (2 + |u|) ^ e
  let F := fun z => invZeta (linePoint u + z)
  obtain ⟨hdiff, hbd⟩ := hstrip u
  have hV : 0 ≤ V := Real.rpow_nonneg (by positivity) _
  have hKV : 0 ≤ K * V := mul_nonneg hK hV
  have hline (y : ℝ) : ‖F ((c : ℂ) + (y : ℂ) * I)‖ ≤ (K * V) * (2 + |y|) ^ e := by
    simpa [F, V] using hbd _ (line_mem_verticalStrip le_rfl hc2 y)
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hint := integrable_mul_mellin_smoothWeight_line hN' (H := 1) zero_lt_one hc
    hdiff.continuousOn hKV he.le hbd le_rfl hc2
  have hraw := hfrac N 1 c e q (K * V) hN' zero_lt_one hc he.le hq hq1 hKV F hline hint
  have hex := (sharp_section_perron u hN).trans
    (integral_mul_mellin_smoothWeight_shift hN' (H := 1) zero_lt_one hc hc2 hdiff hKV he.le hbd)
  have hn := (norm_integral_le_integral_norm _).trans hraw
  rw [← hex, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hn
  have hX : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hXp := zero_lt_one.trans_le hX
  have hxc := Real.rpow_le_rpow_of_exponent_le hX (le_add_of_nonneg_left (he.le.trans hq.le) : c ≤ q + c)
  have hheight := Real.rpow_le_rpow_of_exponent_le (by linarith only [abs_nonneg u] : 1 ≤ 2 + |u|)
    (by linarith : e ≤ ε)
  have hlength := Real.rpow_le_rpow_of_exponent_le hX (by dsimp only [q, c]; linarith : q + c ≤ zetaZeroWidth + ε)
  simp only [div_one] at hn
  change _ ≤ 2 * (K * V * 3 ^ e * (X ^ c / c)) +
    2 * (K * V * 3 ^ e * (P * X ^ q * X ^ c)) * (1 / (q - e)) at hn
  rw [mul_assoc P, ← Real.rpow_add hXp] at hn
  have hfirst := mul_le_mul_of_nonneg_left hxc (by positivity : 0 ≤ 2 * (K * V * 3 ^ e) / c)
  have hsmall : (2 * Real.pi) * ‖moebiusPoly N (linePoint u)‖ ≤ C * X ^ (q + c) * V := by
    have hs : 2*(K*V*3^e*(X^c/c)) ≤ 2*(K*V*3^e*(X^(q+c)/c)) := by
      calc _ = (2*(K*V*3^e)/c)*X^c := by ring
           _ ≤ _ := hfirst
           _ = _ := by ring
    refine hn.trans ((add_le_add hs le_rfl).trans_eq ?_)
    dsimp only [C]
    ring
  have hbig := mul_le_mul (mul_le_mul_of_nonneg_left hlength hC) hheight hV (by positivity)
  have hfinal := hsmall.trans hbig
  have hp : 0 < 2 * Real.pi := by positivity
  calc
    _ ≤ (C * X ^ (zetaZeroWidth + ε) * (2 + |u|) ^ ε) / (2 * Real.pi) :=
      (le_div_iff₀ hp).mpr ((mul_comm _ _).le.trans hfinal)
    _ = _ := by ring

private theorem section_square_on_power_window {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ u ∈ Set.Icc 1 T,
      ‖moebiusPoly ⌊T ^ θ⌋₊ (linePoint u)‖^2 ≤ C * T ^ (2 * zetaZeroWidth * θ + ε) := by
  let d := ε / (2 * (1 + θ))
  have hd : 0 < d := by dsimp only [d]; positivity
  obtain ⟨K, hK, hbound⟩ := hybrid_moebius_section_bound hd
  let r := zetaZeroWidth + d
  have hr : 0 ≤ r := add_nonneg zetaZeroWidth_nonneg hd.le
  let B := K * 2 ^ r * 3 ^ d
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B ^ 2, sq_nonneg _, fun T hT => ?_⟩
  have hp := zero_lt_one.trans_le hT
  let N := ⌊T ^ θ⌋₊
  have hN : (N : ℝ) + 1 ≤ 2 * T ^ θ := by
    linarith only [Nat.floor_le (Real.rpow_nonneg hp.le θ), Real.one_le_rpow hT hθ.le]
  have hlen := Real.rpow_le_rpow (by positivity) hN hr
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hp.le _), ← Real.rpow_mul hp.le] at hlen
  have hpt (u : ℝ) (hu : u ∈ Set.Icc 1 T) :
      ‖moebiusPoly N (linePoint u)‖ ^ 2 ≤ B ^ 2 * T ^ (2 * zetaZeroWidth * θ + ε) := by
    have ht : 2 + |u| ≤ 3 * T := by
      rw [abs_of_pos (zero_lt_one.trans_le hu.1)]
      linarith only [hT, hu.2]
    have hy := Real.rpow_le_rpow (by positivity) ht hd.le
    rw [Real.mul_rpow (by norm_num) hp.le] at hy
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hlen hK) hy
      (Real.rpow_nonneg (by positivity) _) (by positivity)
    have hv : ‖moebiusPoly N (linePoint u)‖ ≤ B * T ^ (θ * r + d) := by
      refine (hbound N u).trans (hprod.trans_eq ?_)
      rw [Real.rpow_add hp]
      dsimp only [B]
      ring
    refine (pow_le_pow_left₀ (norm_nonneg _) hv 2).trans_eq ?_
    rw [mul_pow, ← Real.rpow_natCast (T ^ _) 2, ← Real.rpow_mul hp.le]
    congr 2
    dsimp only [r, d]
    push_cast
    field_simp [show 1 + θ ≠ 0 by positivity]
    ring
  exact hpt

/-- At every fixed power length, the pure second moment costs a single
power of height in addition to the length contribution of the zero width. -/
theorem long_moebius_moment_unit_intercept {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ u in (1 : ℝ)..T, ‖moebiusPoly ⌊T ^ θ⌋₊ (linePoint u)‖ ^ 2) ≤
        C * T ^ (1 + 2 * zetaZeroWidth * θ + ε) := by
  obtain ⟨K, hK, hpt⟩ := section_square_on_power_window hθ hε
  refine ⟨K, hK, fun T hT => ?_⟩
  have hp := zero_lt_one.trans_le hT
  let N := ⌊T ^ θ⌋₊
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hT
    ((((differentiable_moebiusPoly N).continuous.comp continuous_linePoint).norm.pow 2).intervalIntegrable 1 T)
    intervalIntegrable_const (hpt T hT)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine hmono.trans ((mul_le_mul_of_nonneg_right (by linarith : T - 1 ≤ T) (by positivity)).trans_eq ?_)
  rw [show 1 + 2 * zetaZeroWidth * θ + ε = 1 + (2 * zetaZeroWidth * θ + ε) by ring,
    Real.rpow_add hp 1 (2*zetaZeroWidth*θ+ε), Real.rpow_one]
  ring

private theorem critical_zeta_cont : Continuous (fun t : ℝ => riemannZeta (linePoint t)) :=
  continuous_iff_continuousAt.mpr fun u =>
    (differentiableAt_riemannZeta (linePoint_ne_one u)).continuousAt.comp continuous_linePoint.continuousAt

private theorem zeta_square_small_power {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖riemannZeta (linePoint t)‖^2) ≤ C*T^(1+e) := by
  obtain ⟨D, hD, hcrit⟩ := exists_integral_normSq_zeta_critical_le
  let a := e/2
  have ha : 0 < a := by dsimp only [a]; positivity
  let B := 1 + Real.log 6 + 1/a
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨6*D*B^2, by positivity, fun T hT => ?_⟩
  let N := ⌈T⌉₊ + 4
  have hN : 4 ≤ N := Nat.le_add_left 4 _
  have hT0 := zero_lt_one.trans_le hT
  have hlarge : T ≤ (N:ℝ) := by
    dsimp only [N]; push_cast; linarith only [Nat.le_ceil T]
  have hsmall : (N:ℝ) ≤ 6*T := by
    dsimp only [N]; push_cast; linarith only [Nat.ceil_lt_add_one hT0.le, hT]
  have hlim := intervalIntegral.integral_mono_interval (μ := volume)
    (f := fun t : ℝ => ‖riemannZeta (linePoint t)‖^2)
    ((neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) N)).trans zero_le_one) hT hlarge
    (.of_forall (fun x : ℝ => sq_nonneg ‖riemannZeta (linePoint x)‖))
    ((critical_zeta_cont.norm.pow 2).intervalIntegrable (-(N:ℝ)) N)
  have hreal : (∫ t in (-(N:ℝ))..(N:ℝ), ‖riemannZeta (linePoint t)‖^2) ≤
      D*N*(1+Real.log N)^2 := by simpa [linePoint] using hcrit hN
  have hlog := Real.log_le_log (hT0.trans_le hlarge) hsmall
  rw [Real.log_mul (by norm_num) hT0.ne'] at hlog
  have hlogT := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hT0 a)
  rw [Real.log_rpow hT0] at hlogT
  have hu := Real.one_le_rpow hT ha.le
  have haux : Real.log T ≤ T^a / a := (le_div_iff₀ ha).mpr (by linarith only [hlogT])
  have hstep : 1+Real.log N ≤ B*T^a := by
    have hmain := mul_le_mul_of_nonneg_left hu (add_nonneg zero_le_one hlog6)
    calc
      1+Real.log N ≤ 1+Real.log 6+Real.log T := by linarith only [hlog]
      _ ≤ (1+Real.log 6)*T^a+T^a/a := add_le_add (by simpa only [mul_one] using hmain) haux
      _ = B*T^a := by dsimp only [B]; ring
  have hz := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_nonneg (hT.trans hlarge))) hstep 2
  refine (hlim.trans hreal).trans ((mul_le_mul (mul_le_mul_of_nonneg_left hsmall hD) hz
    (sq_nonneg _) (by positivity)).trans_eq ?_)
  rw [mul_pow, ←Real.rpow_natCast (T^a) 2, ←Real.rpow_mul hT0.le,
    show a*(2:ℕ) = e by dsimp only [a]; push_cast; ring, Real.rpow_add hT0, Real.rpow_one]
  ring

/-- Multiplication by zeta preserves the same height intercept and the same
zero-width slope for the second moment. -/
theorem long_zeta_moebius_moment_unit_intercept {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1:ℝ)..T, ‖riemannZeta (linePoint t)*moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2) ≤
        C*T^(1+2*zetaZeroWidth*θ+ε) := by
  have he : 0 < ε/2 := by positivity
  obtain ⟨K, hK, hsec⟩ := section_square_on_power_window hθ he
  obtain ⟨D, hD, hz⟩ := zeta_square_small_power he
  refine ⟨K*D,mul_nonneg hK hD, fun T hT => ?_⟩
  have hp := zero_lt_one.trans_le hT
  let N := ⌊T^θ⌋₊
  let V := K*T^(2*zetaZeroWidth*θ+ε/2)
  have hV : 0 ≤ V := mul_nonneg hK (Real.rpow_nonneg hp.le _)
  have hpt (t : ℝ) (ht : t ∈ Set.Icc 1 T) :
      ‖riemannZeta (linePoint t)*moebiusPoly N (linePoint t)‖^2 ≤ V*‖riemannZeta (linePoint t)‖^2 := by
    rw [norm_mul, mul_pow, mul_comm V]
    exact mul_le_mul_of_nonneg_left (hsec T hT t ht) (sq_nonneg _)
  have hcont := (differentiable_moebiusPoly N).continuous.comp continuous_linePoint
  have hint := intervalIntegral.integral_mono_on (μ := volume) hT
    (((critical_zeta_cont.mul hcont).norm.pow 2).intervalIntegrable 1 T)
    ((continuous_const.mul (critical_zeta_cont.norm.pow 2)).intervalIntegrable 1 T) hpt
  change (∫ t in (1:ℝ)..T, ‖riemannZeta (linePoint t)*moebiusPoly N (linePoint t)‖^2) ≤
    ∫ t in (1:ℝ)..T, V*‖riemannZeta (linePoint t)‖^2 at hint
  rw [intervalIntegral.integral_const_mul V] at hint
  refine hint.trans ((mul_le_mul_of_nonneg_left (hz T hT) hV).trans_eq ?_)
  dsimp only [V]
  calc
    _ = K*D*(T^(2*zetaZeroWidth*θ+ε/2)*T^(1+ε/2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hp,show 2*zetaZeroWidth*θ+ε/2+(1+ε/2)=1+2*zetaZeroWidth*θ+ε by ring]

#print axioms hybrid_moebius_section_bound
#print axioms long_moebius_moment_unit_intercept
#print axioms long_zeta_moebius_moment_unit_intercept

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
