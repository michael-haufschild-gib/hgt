import GaloisForLFunctions.RHTower.OddWeilResolventIntegral
import GaloisForLFunctions.RHTower.OddWeilResolventApproximation

/-!
# Arithmetic identification of the odd resolvent Gram form

Write `F(a) = weilFunction lam (a + 1/2)`. For first-quadrant seed widths,
the limit of the actual mixed odd Weil form is exactly

`mixedWeilLimit lam a b = 4 (a F(a) - conj (b F(b))) / (a² - conj(b)²)`.

The pole, digamma, and Dirichlet terms are identified separately. Odd
positivity supplies the existing absolute convergence theorem for the
weights; no spectral representation or Pick positivity is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent
open WeilHerglotz

theorem integrable_cauchy_gamma {a : ℂ} (ha : 0 < a.re) :
    Integrable fun r => cauchy a r * (EF.gammaBracket r : ℂ) := by
  have h1 := integrable_cauchy_weight ha (continuous_re_digamma_half (c := 1 / 4) (by norm_num))
    (integrable_poissonWeight_mul_re_digamma_half (a := 1) (c := 1 / 4) (by norm_num) (by norm_num))
  have h2 := (integrable_cauchy ha).mul_const (Real.log Real.pi : ℂ)
  refine (h1.sub h2).congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.sub_apply, gammaBracket_eq, Complex.ofReal_sub]
  ring

theorem integral_cauchy_gamma {a : ℂ} (ha : 0 < a.re) (hai : 0 < a.im) :
    (∫ r, cauchy a r * (EF.gammaBracket r : ℂ)) =
      Real.pi / a * (Complex.digamma ((1 / 4 : ℂ) + a / 2) - Real.log Real.pi) := by
  have h1 := integrable_cauchy_weight ha (continuous_re_digamma_half (c := 1 / 4) (by norm_num))
    (integrable_poissonWeight_mul_re_digamma_half (a := 1) (c := 1 / 4) (by norm_num) (by norm_num))
  have h2 := (integrable_cauchy ha).mul_const (Real.log Real.pi : ℂ)
  simp_rw [gammaBracket_eq, Complex.ofReal_sub, mul_sub]
  rw [integral_sub h1 h2, integral_mul_const, integral_cauchy ha,
    integral_cauchy_re_digamma ha hai (by norm_num : (0 : ℝ) < 1 / 4)]
  push_cast
  ring

theorem integral_cauchy_gamma_conj {a : ℂ} (ha : 0 < a.re) (hai : 0 < a.im) :
    (∫ r, cauchy (conj a) r * (EF.gammaBracket r : ℂ)) =
      conj (Real.pi / a * (Complex.digamma ((1 / 4 : ℂ) + a / 2) - Real.log Real.pi)) := by
  rw [← integral_cauchy_gamma ha hai, ← integral_conj]
  congr 1
  funext r
  simp [cauchy_conj]

theorem primeExp_eq_term (lam : ℕ → ℝ) (a : ℂ) (n : ℕ) :
    primeCoeff lam n * Complex.exp (-(a * (Real.log n : ℂ))) =
      LSeries.term (lamC lam) (a + 1 / 2) n := by
  by_cases hn : 2 ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsqrt : (Real.sqrt n : ℂ) = Complex.exp ((Real.log n : ℂ) / 2) := by
      rw [show (Real.log n : ℂ) / 2 = ((Real.log n / 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp]
      congr 1
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    rw [primeCoeff, if_pos hn, LSeries.term_def, if_neg hn0, lamC, if_pos hn,
      Complex.ofReal_div, hsqrt, natCast_cpow_eq_cexp hn]
    simp only [div_eq_mul_inv, ← Complex.exp_neg]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · simp [primeCoeff, lamC, hn, LSeries.term_def]

theorem summable_term_odd {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam)
    {s : ℂ} (hs : 1 < s.re) : Summable fun n => LSeries.term (lamC lam) s n := by
  refine Summable.of_norm_bounded
    (OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight hW hs) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · positivity
  · rw [lamC, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hn
    · rfl
    · simp only [abs_zero, zero_div]
      positivity

theorem primeCoeff_conj (lam : ℕ → ℝ) (n : ℕ) : conj (primeCoeff lam n) = primeCoeff lam n := by
  simp [primeCoeff]

theorem primeExp_conj (lam : ℕ → ℝ) (a : ℂ) (n : ℕ) :
    primeCoeff lam n * Complex.exp (-(conj a * (Real.log n : ℂ))) =
      conj (primeCoeff lam n * Complex.exp (-(a * (Real.log n : ℂ)))) := by
  simp only [map_mul, map_neg, ← Complex.exp_conj, Complex.conj_ofReal, primeCoeff_conj]

theorem lseries_conj_width (lam : ℕ → ℝ) (a : ℂ) :
    LSeries (lamC lam) (conj a + 1 / 2) = conj (LSeries (lamC lam) (a + 1 / 2)) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [← primeExp_eq_term, ← primeExp_eq_term, primeExp_conj]

theorem upper_square_sub_conj_square_ne_zero {a b : ℂ}
    (ha : 0 < a.re) (hai : 0 < a.im) (hb : 0 < b.re) (hbi : 0 < b.im) :
    a ^ 2 - (conj b) ^ 2 ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [sub_im, sq, mul_im, conj_re, conj_im, zero_im] at hi
  nlinarith [mul_pos ha hai, mul_pos hb hbi]

theorem oddTransform_mul_conj {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (r : ℝ) :
    oddTransform a r * conj (oddTransform b r) =
      4 * (r : ℂ) ^ 2 * cauchy a r * cauchy (conj b) r := by
  unfold oddTransform
  rw [oddResolvent_formula ha, oddResolvent_formula hb]
  simp only [map_div₀, map_mul, map_add, map_pow, map_ofNat, conj_I, conj_ofReal]
  unfold cauchy
  ring_nf
  rw [I_sq]
  ring

theorem mixedSumLimit_eq {a b : ℂ}
    (ha : 0 < a.re) (hai : 0 < a.im) (hb : 0 < b.re) (hbi : 0 < b.im) (x : ℝ) :
    mixedSumLimit a b x =
      4 / (a ^ 2 - (conj b) ^ 2) *
        (a * Complex.exp (-(a * (|x| : ℝ))) -
          conj b * Complex.exp (-(conj b * (|x| : ℝ)))) := by
  have hd := upper_square_sub_conj_square_ne_zero ha hai hb hbi
  unfold mixedSumLimit
  simp_rw [oddTransform_mul_conj ha hb,
    show ∀ r : ℝ, 4 * (r : ℂ) ^ 2 * cauchy a r * cauchy (conj b) r *
      (Real.cos (r * x) : ℂ) =
      4 * ((r : ℂ) ^ 2 * cauchy a r * cauchy (conj b) r * (Real.cos (r * x) : ℂ))
      from fun r => by ring]
  rw [integral_const_mul, integral_oddGram_cos ha (by simpa using hb) hd]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp

theorem mixed_arch_eq {a b : ℂ}
    (ha : 0 < a.re) (hai : 0 < a.im) (hb : 0 < b.re) (hbi : 0 < b.im) :
    (∫ r : ℝ, oddTransform a r * conj (oddTransform b r) * (EF.gammaBracket r : ℂ)) =
      4 / (a ^ 2 - (conj b) ^ 2) *
        (a ^ 2 * (Real.pi / a * (Complex.digamma ((1 / 4 : ℂ) + a / 2) - Real.log Real.pi)) -
          (conj b) ^ 2 * conj (Real.pi / b *
            (Complex.digamma ((1 / 4 : ℂ) + b / 2) - Real.log Real.pi))) := by
  have hd := upper_square_sub_conj_square_ne_zero ha hai hb hbi
  have he : ∀ r : ℝ,
      oddTransform a r * conj (oddTransform b r) * (EF.gammaBracket r : ℂ) =
        4 / (a ^ 2 - (conj b) ^ 2) *
          (a ^ 2 * (cauchy a r * (EF.gammaBracket r : ℂ)) -
            (conj b) ^ 2 * (cauchy (conj b) r * (EF.gammaBracket r : ℂ))) := by
    intro r
    rw [oddTransform_mul_conj ha hb]
    calc 4 * (r : ℂ) ^ 2 * cauchy a r * cauchy (conj b) r * (EF.gammaBracket r : ℂ)
        = 4 * ((r : ℂ) ^ 2 * cauchy a r * cauchy (conj b) r) * (EF.gammaBracket r : ℂ) := by ring
      _ = _ := by rw [oddGram_partial ha (by simpa using hb) hd]; ring
  simp_rw [he]
  rw [integral_const_mul,
    integral_sub ((integrable_cauchy_gamma ha).const_mul _)
      ((integrable_cauchy_gamma (a := conj b) (by simpa using hb)).const_mul _),
    integral_const_mul, integral_const_mul, integral_cauchy_gamma ha hai,
    integral_cauchy_gamma_conj hb hbi]

theorem oddTransform_neg (a z : ℂ) : oddTransform a (-z) = -oddTransform a z := by
  simp [oddTransform]
  ring

theorem mixedTransform_neg (a b z : ℂ) : mixedTransform a b (-z) = mixedTransform a b z := by
  simp [mixedTransform, oddTransform_neg]

theorem oddPole_ne_zero {a : ℂ} (ha : 2 ≤ a.re) : a ^ 2 - 1 / 4 ≠ 0 := by
  have hp : a + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hm : a - 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  rw [show a ^ 2 - 1 / 4 = (a + 1 / 2) * (a - 1 / 2) by ring]
  exact mul_ne_zero hp hm

theorem oddTransform_I_half {a : ℂ} (ha : 2 ≤ a.re) :
    oddTransform a (I / 2) = -1 / (a ^ 2 - 1 / 4) := by
  have hp : a + 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hm : a - 1 / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hd := oddPole_ne_zero ha
  have hI : I * (I / 2) = -(1 / 2 : ℂ) := by rw [← mul_div_assoc, ← sq, I_sq]; ring
  unfold oddTransform
  rw [hI, sub_neg_eq_add]
  change 1 / (a + 1 / 2) - 1 / (a - 1 / 2) = -1 / (a ^ 2 - 1 / 4)
  have hfrac : ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → 1 / x - 1 / y = (y - x) / (x * y) := by
    intro x y hx hy
    field_simp
  rw [hfrac _ _ hp hm,
    show (a - 1 / 2) - (a + 1 / 2) = (-1 : ℂ) by ring,
    show (a + 1 / 2) * (a - 1 / 2) = a ^ 2 - (1 / 4 : ℂ) by ring]

theorem mixed_pole_eq {a b : ℂ} (ha : 2 ≤ a.re) (hb : 2 ≤ b.re) :
    mixedTransform a b (I / 2) + mixedTransform a b (-I / 2) =
      -2 / ((a ^ 2 - 1 / 4) * ((conj b) ^ 2 - 1 / 4)) := by
  rw [show -I / 2 = -(I / 2) by ring, mixedTransform_neg]
  unfold mixedTransform
  simp only [map_div₀, conj_I, map_ofNat]
  rw [show -I / 2 = -(I / 2) by ring, oddTransform_neg,
    oddTransform_I_half ha, oddTransform_I_half hb]
  simp only [map_mul, map_neg, map_inv₀, map_sub, map_pow, map_ofNat, map_one, div_eq_mul_inv, mul_inv]
  ring

theorem mixed_prime_term {a b : ℂ}
    (ha : 0 < a.re) (hai : 0 < a.im) (hb : 0 < b.re) (hbi : 0 < b.im)
    (lam : ℕ → ℝ) (n : ℕ) :
    primeCoeff lam n * mixedSumLimit a b (Real.log n) =
      4 / (a ^ 2 - (conj b) ^ 2) *
        (a * LSeries.term (lamC lam) (a + 1 / 2) n -
          conj b * LSeries.term (lamC lam) (conj b + 1 / 2) n) := by
  rw [mixedSumLimit_eq ha hai hb hbi, abs_of_nonneg (Real.log_natCast_nonneg n)]
  calc primeCoeff lam n * (4 / (a ^ 2 - (conj b) ^ 2) *
        (a * Complex.exp (-(a * (Real.log n : ℂ))) -
          conj b * Complex.exp (-(conj b * (Real.log n : ℂ))))) =
      4 / (a ^ 2 - (conj b) ^ 2) *
        (a * (primeCoeff lam n * Complex.exp (-(a * (Real.log n : ℂ)))) -
          conj b * (primeCoeff lam n * Complex.exp (-(conj b * (Real.log n : ℂ))))) := by ring
    _ = _ := by rw [primeExp_eq_term, primeExp_eq_term]

theorem mixed_prime_eq {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam)
    {a b : ℂ} (ha : 2 ≤ a.re) (hai : 0 < a.im) (hb : 2 ≤ b.re) (hbi : 0 < b.im) :
    (∑' n : ℕ, primeCoeff lam n * mixedSumLimit a b (Real.log n)) =
      4 / (a ^ 2 - (conj b) ^ 2) *
        (a * LSeries (lamC lam) (a + 1 / 2) -
          conj b * conj (LSeries (lamC lam) (b + 1 / 2))) := by
  have hsa := summable_term_odd hW (s := a + 1 / 2) (by norm_num; linarith)
  have hsb := summable_term_odd hW (s := conj b + 1 / 2) (by norm_num; linarith)
  simp_rw [mixed_prime_term (by linarith : 0 < a.re) hai (by linarith : 0 < b.re) hbi]
  rw [tsum_mul_left, (hsa.mul_left a).tsum_sub (hsb.mul_left (conj b)),
    tsum_mul_left, tsum_mul_left]
  change 4 / (a ^ 2 - (conj b) ^ 2) *
    (a * LSeries (lamC lam) (a + 1 / 2) - conj b * LSeries (lamC lam) (conj b + 1 / 2)) = _
  rw [lseries_conj_width]

theorem halfShift_ne_zero {a : ℂ} (ha : 2 ≤ a.re) : a + 1 / 2 ≠ 0 ∧ a - 1 / 2 ≠ 0 := by
  constructor <;> intro h <;>
    have hh := congrArg Complex.re h <;> norm_num at hh <;> linarith

theorem mixedWeilLimit_eq {lam : ℕ → ℝ} (hW : WeilPositiveOddAt 1 lam)
    {a b : ℂ} (ha : 2 ≤ a.re) (hai : 0 < a.im) (hb : 2 ≤ b.re) (hbi : 0 < b.im) :
    mixedWeilLimit lam a b =
      4 * ((a * weilFunction lam (a + 1 / 2) - conj (b * weilFunction lam (b + 1 / 2))) /
        (a ^ 2 - (conj b) ^ 2)) := by
  have ha0 : 0 < a.re := by linarith
  have hb0 : 0 < b.re := by linarith
  have hna : a ≠ 0 := by intro h; simp [h] at ha0
  have hnb : conj b ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hd := upper_square_sub_conj_square_ne_zero ha0 hai hb0 hbi
  have hda := oddPole_ne_zero ha
  have hdb := oddPole_ne_zero (a := conj b) (by simpa using hb)
  obtain ⟨hpa, hma⟩ := halfShift_ne_zero ha
  obtain ⟨hpb, hmb⟩ := halfShift_ne_zero (a := conj b) (by simpa using hb)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  rw [mixedWeilLimit, mixed_pole_eq ha hb, mixed_prime_eq hW ha hai hb hbi,
    mixed_arch_eq ha0 hai hb0 hbi]
  unfold weilFunction
  rw [show (a + 1 / 2) / 2 = (1 / 4 : ℂ) + a / 2 by ring,
    show (b + 1 / 2) / 2 = (1 / 4 : ℂ) + b / 2 by ring]
  simp only [map_mul, map_sub, map_add, map_div₀, conj_ofReal, map_one, map_ofNat]
  rw [show a + 1 / 2 - 1 = a - (1 / 2 : ℂ) by ring,
    show conj b + 1 / 2 - 1 = conj b - (1 / 2 : ℂ) by ring]
  generalize hDa : a ^ 2 - 1 / 4 = Da at *
  generalize hDb : (conj b) ^ 2 - 1 / 4 = Db at *
  generalize hD : a ^ 2 - (conj b) ^ 2 = D at *
  generalize hPa : a + 1 / 2 = Pa at *
  generalize hMa : a - 1 / 2 = Ma at *
  generalize hPb : conj b + 1 / 2 = Pb at *
  generalize hMb : conj b - 1 / 2 = Mb at *
  field_simp
  rw [← hDa, ← hDb, ← hD, ← hPa, ← hMa, ← hPb, ← hMb]
  ring

end RHTower.OddResolvent
