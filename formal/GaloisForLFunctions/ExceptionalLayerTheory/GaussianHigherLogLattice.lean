import GaloisForLFunctions.ExceptionalLayerTheory.GaussianHigherMomentLattice
import GaloisForLFunctions.ExceptionalLayerTheory.GaussianLogarithmicContinuum

/-!
# Logarithmic lattice errors for higher Gaussian moments

First variation suffices when the logarithmic divisor cutoff is small.
Every fixed normalized moment retains the error `O(t X^(-σ))`, with its
scale logarithm and both signed continuum terms explicit.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem norm_mellinWeight {w ε : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖gaussianMellinWeight w ε x‖ = x ^ w.re * Real.exp (-ε.re * x ^ 2) := by
  rw [gaussianMellinWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp]
  congr 2
  simp [pow_two]

/-- Logarithmic samples are absolutely summable for every Mellin exponent. -/
theorem summable_gaussianLogMellinWeight_lattice_all {w ε : ℂ}
    (hε : 0 < ε.re) {b B : ℝ} (hb : 0 < b) (hB : 0 < B) :
    Summable (fun n : ℕ => gaussianLogMellinWeight w ε B (b * (n + 1))) := by
  obtain ⟨K, hK⟩ := exists_nat_ge w.re
  have hs := (summable_nat_add_iff 1).mpr
    (RHTower.summable_pow_mul_exp_neg_nat_sq (K + 1)
      (show 0 < ε.re * b ^ 2 by positivity))
  apply (hs.mul_left ((2 + |Real.log (b / B)|) * b ^ w.re)).of_norm_bounded
  intro n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hx : 0 < b * ((n : ℝ) + 1) := by positivity
  have hl := abs_log_div_le_scaled hx hb hB
  have hd1 : b * ((n : ℝ) + 1) / b = (n : ℝ) + 1 := by field_simp
  have hd2 : b / (b * ((n : ℝ) + 1)) = ((n : ℝ) + 1)⁻¹ := by field_simp
  rw [hd1, hd2] at hl
  have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ hn0).mpr hn
  have hlog : |Real.log (b * ((n : ℝ) + 1) / B)| ≤
      (2 + |Real.log (b / B)|) * ((n : ℝ) + 1) := by
    nlinarith only [hl, hi, hn, mul_nonneg (abs_nonneg (Real.log (b / B))) (sub_nonneg.mpr hn)]
  rw [gaussianLogMellinWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_mellinWeight hx, Real.mul_rpow hb.le hn0.le]
  have hp : ((n : ℝ) + 1) ^ w.re ≤ ((n : ℝ) + 1) ^ K := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hn hK
  have he : -ε.re * (b * ((n : ℝ) + 1)) ^ 2 =
      -(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2 := by ring
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ((2 + |Real.log (b / B)|) * ((n : ℝ) + 1)) *
        (b ^ w.re * ((n : ℝ) + 1) ^ K *
          Real.exp (-(ε.re * b ^ 2) * ((n : ℝ) + 1) ^ 2)) := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- First variation controls the complete logarithmic lattice at every exponent above one. -/
theorem norm_tsum_gaussianLogMellinWeight_sub_integral_all_le {w ε : ℂ}
    (hw : 1 < w.re) (hε : 0 < ε.re) {X B b : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hb : 0 < b) :
    ‖(∑' n : ℕ, gaussianLogMellinWeight w ε B (b * (n + 1))) -
        (b : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε B x‖ ≤
      gaussianLogMellinVariation w ε X B := by
  have hs := (summable_gaussianLogMellinWeight_lattice_all (w := w) hε hb hB).hasSum.tendsto_sum_nat
  have hN : Tendsto (fun n : ℕ => b * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hb
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_gaussianLogMellinWeight (by linarith : 0 < w.re) hε hB) hN
  exact le_of_tendsto ((hs.sub (hi.const_mul (b : ℂ)⁻¹)).norm)
    (Filter.Eventually.of_forall fun N =>
      norm_sum_gaussianLogMellinWeight_sub_integral_le hw hε hX hB hb N)

/-- Three absolute Gaussian moments controlling one scale-normalized logarithm. -/
def gaussianLogScaleMoment (q : ℝ) : ℝ :=
  gaussianRealMoment (q + 1) 2 + gaussianRealMoment (q - 1) 2 + gaussianRealMoment q 2

private theorem realMoment_nonneg {q α : ℝ} (hq : -1 < q) (hα : 0 < α) :
    0 ≤ gaussianRealMoment q α := by
  have hG := (Real.Gamma_pos_of_pos (show 0 < (q + 1) / 2 by linarith)).le
  unfold gaussianRealMoment
  positivity

private theorem logMomentBudget_nonneg {q α X b : ℝ}
    (hq : 0 < q) (hα : 0 < α) (hX : 0 < X) :
    0 ≤ gaussianLogMomentBudget q α X b := by
  have hp := realMoment_nonneg (show -1 < q + 1 by linarith) hα
  have hm := realMoment_nonneg (show -1 < q - 1 by linarith) hα
  have h0 := realMoment_nonneg (show -1 < q by linarith) hα
  unfold gaussianLogMomentBudget
  positivity

private theorem logScaleMoment_nonneg {q : ℝ} (hq : 0 < q) :
    0 ≤ gaussianLogScaleMoment q := by
  have hp := realMoment_nonneg (show -1 < q + 1 by linarith) (by norm_num : (0 : ℝ) < 2)
  have hm := realMoment_nonneg (show -1 < q - 1 by linarith) (by norm_num : (0 : ℝ) < 2)
  have h0 := realMoment_nonneg (show -1 < q by linarith) (by norm_num : (0 : ℝ) < 2)
  exact add_nonneg (add_nonneg hp hm) h0

private theorem realMoment_scale {α X : ℝ} (hα : 0 < α) (hX : 0 < X)
    (hscale : α * X ^ 2 = 2) (q : ℝ) :
    gaussianRealMoment q α = X ^ (q + 1) * gaussianRealMoment q 2 := by
  have hi : 1 / α = (1 / 2 : ℝ) * X ^ 2 := by
    apply (div_eq_iff hα.ne').mpr
    nlinarith only [hscale]
  have hp : (X ^ 2) ^ ((q + 1) / 2) = X ^ (q + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hX.le]
    congr 1
    ring
  unfold gaussianRealMoment
  rw [hi, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg X), hp]
  ring

private theorem logMomentBudget_le {q α X b : ℝ} (hq : 0 < q)
    (hα : 0 < α) (hX : 0 < X) (hscale : α * X ^ 2 = 2) :
    gaussianLogMomentBudget q α X b ≤
      X ^ (q + 1) * gaussianLogScaleMoment q * (1 + |Real.log (X / b)|) := by
  have hplus : X ^ (q + 1 + 1) = X ^ (q + 1) * X := by
    rw [Real.rpow_add hX, Real.rpow_one]
  have hminus : X * X ^ (q - 1 + 1) = X ^ (q + 1) := by
    rw [show q - 1 + 1 = q by ring, Real.rpow_add hX, Real.rpow_one]
    ring
  have he : gaussianLogMomentBudget q α X b = X ^ (q + 1) *
      (gaussianRealMoment (q + 1) 2 + gaussianRealMoment (q - 1) 2 +
        |Real.log (X / b)| * gaussianRealMoment q 2) := by
    unfold gaussianLogMomentBudget
    rw [realMoment_scale hα hX hscale, realMoment_scale hα hX hscale,
      realMoment_scale hα hX hscale, hplus]
    have hm : X * (X ^ (q - 1 + 1) * gaussianRealMoment (q - 1) 2) =
        X ^ (q + 1) * gaussianRealMoment (q - 1) 2 := by rw [← mul_assoc, hminus]
    rw [hm]
    field_simp
  have hp := realMoment_nonneg (show -1 < q + 1 by linarith) (by norm_num : (0 : ℝ) < 2)
  have hm := realMoment_nonneg (show -1 < q - 1 by linarith) (by norm_num : (0 : ℝ) < 2)
  have h0 := realMoment_nonneg (show -1 < q by linarith) (by norm_num : (0 : ℝ) < 2)
  have hL := abs_nonneg (Real.log (X / b))
  rw [he, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX.le _)
  unfold gaussianLogScaleMoment
  nlinarith only [hp, hm, h0, hL, mul_nonneg hp hL, mul_nonneg hm hL]

/-- The explicit constant for the logarithmic error of a normalized higher moment. -/
def gaussianHigherLogMomentConstant (r : ℕ) (σ : ℝ) : ℝ :=
  8 ^ r * (gaussianRealMoment ((2 * r : ℕ) - σ - 1) 2 +
    ((2 * r : ℕ) + 1) * gaussianLogScaleMoment ((2 * r : ℕ) - σ - 1) +
    16 * gaussianLogScaleMoment ((2 * r : ℕ) - σ + 1))

theorem gaussianHigherLogMomentConstant_nonneg {r : ℕ} (hr : r ≠ 0) {σ : ℝ}
    (hσ : σ < 1) : 0 ≤ gaussianHigherLogMomentConstant r σ := by
  have hr' : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * r by omega)
  have hm := realMoment_nonneg (show -1 < (2 * r : ℕ) - σ - 1 by linarith)
    (by norm_num : (0 : ℝ) < 2)
  have h0 := logScaleMoment_nonneg (show 0 < (2 * r : ℕ) - σ - 1 by linarith)
  have hp := logScaleMoment_nonneg (show 0 < (2 * r : ℕ) - σ + 1 by linarith)
  unfold gaussianHigherLogMomentConstant
  positivity

private theorem norm_mul_logVariation_le {r : ℕ} (hr : r ≠ 0) {σ t X b : ℝ} {ε : ℂ}
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2) :
    ‖(ε / (t : ℂ)) ^ r‖ *
      gaussianLogMellinVariation (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε X b ≤
      gaussianHigherLogMomentConstant r σ * t * X ^ (-σ) * (1 + |Real.log (X / b)|) := by
  let w : ℂ := ((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)
  let a : ℝ := ((2 * r : ℕ) : ℝ) - σ
  let L : ℝ := 1 + |Real.log (X / b)|
  have hwa : w.re = a := by simp [w, a]
  have hr' : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * r by omega)
  have ha : 1 < a := by dsimp [a]; linarith only [hr', hσ1]
  have hL : 1 ≤ L := le_add_of_nonneg_right (abs_nonneg _)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hnorm : ‖w‖ ≤ ((2 * r : ℕ) + 1) * t := by
    have hh := Complex.norm_le_abs_re_add_abs_im w
    have hi : |w.im| = t := by simp [w, abs_of_pos ht0]
    rw [hwa, hi, abs_of_pos (by linarith : 0 < a)] at hh
    have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (2 * r) : (0 : ℝ) ≤ (2 * r : ℕ))
    dsimp [a] at hh
    nlinarith only [hh, hm, hσ]
  have hA := realMoment_nonneg (show -1 < a - 1 by linarith) (by norm_num : (0 : ℝ) < 2)
  have hB := logScaleMoment_nonneg (show 0 < a - 1 by linarith)
  have hD := logScaleMoment_nonneg (show 0 < a + 1 by linarith)
  have hbm := logMomentBudget_le (show 0 < a - 1 by linarith) hε hX hscale (b := b)
  have hbp := logMomentBudget_le (show 0 < a + 1 by linarith) hε hX hscale (b := b)
  rw [show a - 1 + 1 = a by ring] at hbm
  have hxplus : X ^ (a + 1 + 1) = X ^ a * X ^ 2 := by
    rw [show a + 1 + 1 = a + 2 by ring, Real.rpow_add hX, Real.rpow_two]
  rw [hxplus] at hbp
  have hj : 2 * ‖ε‖ * X ^ 2 ≤ 16 * t := by
    calc
      _ ≤ 2 * (4 * ε.re * t) * X ^ 2 := by gcongr
      _ = 8 * t * (ε.re * X ^ 2) := by ring
      _ = 16 * t := by rw [hscale]; ring
  have hv : gaussianLogMellinVariation w ε X b ≤
      X ^ a * L * t * (gaussianRealMoment (a - 1) 2 +
        ((2 * r : ℕ) + 1) * gaussianLogScaleMoment (a - 1) +
        16 * gaussianLogScaleMoment (a + 1)) := by
    unfold gaussianLogMellinVariation
    rw [hwa, realMoment_scale hε hX hscale, show a - 1 + 1 = a by ring]
    have hA' : X ^ a * gaussianRealMoment (a - 1) 2 ≤
        X ^ a * L * t * gaussianRealMoment (a - 1) 2 := by
      have hLt : 1 ≤ L * t := by
        nlinarith only [hL, ht, mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr ht)]
      nlinarith only [mul_le_mul_of_nonneg_left hLt
        (mul_nonneg (Real.rpow_nonneg hX.le a) hA)]
    have hB' := mul_le_mul hnorm hbm
      (logMomentBudget_nonneg (show 0 < a - 1 by linarith) hε hX)
      (by positivity : 0 ≤ ((2 * r : ℕ) + 1) * t)
    have hD' := mul_le_mul_of_nonneg_left hbp (by positivity : 0 ≤ 2 * ‖ε‖)
    have hj' := mul_le_mul_of_nonneg_right hj
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg hX.le a) (by linarith : 0 ≤ L)) hD)
    dsimp only [L] at hA' hj' ⊢
    nlinarith only [hA', hB', hD', hj']
  have hv0 : 0 ≤ gaussianLogMellinVariation w ε X b := by
    have h0 := realMoment_nonneg (show -1 < w.re - 1 by rw [hwa]; linarith) hε
    have h1 := logMomentBudget_nonneg (show 0 < w.re - 1 by rw [hwa]; linarith) hε hX (b := b)
    have h2 := logMomentBudget_nonneg (show 0 < w.re + 1 by rw [hwa]; linarith) hε hX (b := b)
    unfold gaussianLogMellinVariation
    positivity
  have he : ‖(ε / (t : ℂ)) ^ r‖ ≤ (4 * ε.re) ^ r := by
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr hsector
  have hpower : (4 * ε.re) ^ r * X ^ a = 8 ^ r * X ^ (-σ) := by
    have hx : X ^ a = X ^ (-σ) * (X ^ 2) ^ r := by
      rw [← pow_mul, ← Real.rpow_natCast X (2 * r), ← Real.rpow_add hX]
      congr 1
      dsimp [a]
      ring
    rw [hx]
    calc
      _ = ((4 * ε.re) * X ^ 2) ^ r * X ^ (-σ) := by rw [mul_pow]; ring
      _ = _ := by rw [show 4 * ε.re * X ^ 2 = 8 by nlinarith only [hscale]]
  apply (mul_le_mul he hv hv0 (by positivity : 0 ≤ (4 * ε.re) ^ r)).trans_eq
  calc
    _ = ((4 * ε.re) ^ r * X ^ a) * L * t *
        (gaussianRealMoment (a - 1) 2 + ((2 * r : ℕ) + 1) * gaussianLogScaleMoment (a - 1) +
          16 * gaussianLogScaleMoment (a + 1)) := by ring
    _ = _ := by rw [hpower]; unfold gaussianHigherLogMomentConstant; dsimp [a, L]; ring

/-- The logarithmic continuous pole of the normalized higher moment. -/
def gaussianHigherMomentLogPole (r : ℕ) (s ε : ℂ) (t : ℝ) : ℂ :=
  (ε / (t : ℂ)) ^ r *
    ∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight (((2 * r : ℕ) : ℂ) - s) ε 1 x

private theorem integral_logWeight_split {w ε : ℂ}
    (hw : 0 < w.re) (hε : 0 < ε.re) {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε b x) =
      (∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε 1 x) -
        (Real.log b : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) * ε ^ (-(w + 1) / 2)) := by
  have he : ∀ x ∈ Ioi (0 : ℝ), gaussianLogMellinWeight w ε b x =
      gaussianLogMellinWeight w ε 1 x - (Real.log b : ℂ) * gaussianMellinWeight w ε x := by
    intro x hx
    rw [gaussianLogMellinWeight, gaussianLogMellinWeight, div_one,
      Real.log_div hx.ne' hb.ne', Complex.ofReal_sub, sub_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi he,
    integral_sub (integrableOn_gaussianLogMellinWeight hw hε zero_lt_one)
      ((integrableOn_gaussianMellinWeight hw hε).const_mul _),
    integral_const_mul, integral_gaussianMellinWeight hw hε]

/-- Every higher logarithmic moment retains its two signed continuum terms
with error `O(t X^(-σ)(1+|log(X/b)|))`. -/
theorem norm_tsum_gaussianHigherLogMoment_sub_poles_le (r : ℕ) (hr : r ≠ 0)
    {σ t X : ℝ} {ε : ℂ} (hσ : 0 ≤ σ) (hσ1 : σ < 1) (ht : 1 ≤ t) (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hX : 0 < X) (hscale : ε.re * X ^ 2 = 2)
    {b : ℝ} (hb : 0 < b) :
    ‖(ε / (t : ℂ)) ^ r * (∑' n : ℕ,
        gaussianLogMellinWeight (((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)) ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * (gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t -
        (Real.log b : ℂ) * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t)‖ ≤
      gaussianHigherLogMomentConstant r σ * t * X ^ (-σ) * (1 + |Real.log (X / b)|) := by
  let w : ℂ := ((2 * r : ℕ) : ℂ) - ((σ : ℂ) + t * I)
  have hr' : (2 : ℝ) ≤ ((2 * r : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * r by omega)
  have hwre : w.re = ((2 * r : ℕ) : ℝ) - σ := by simp [w]
  have hw : 1 < w.re := by rw [hwre]; linarith only [hr', hσ1]
  have hh := mul_le_mul_of_nonneg_left
    (norm_tsum_gaussianLogMellinWeight_sub_integral_all_le hw hε hX hb hb)
      (norm_nonneg ((ε / (t : ℂ)) ^ r))
  rw [← norm_mul, integral_logWeight_split (by linarith) hε hb] at hh
  have heq : (ε / (t : ℂ)) ^ r * ((∑' n : ℕ, gaussianLogMellinWeight w ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * ((∫ x in Ioi (0 : ℝ), gaussianLogMellinWeight w ε 1 x) -
        (Real.log b : ℂ) * ((1 / 2 : ℂ) * Complex.Gamma ((w + 1) / 2) * ε ^ (-(w + 1) / 2)))) =
      (ε / (t : ℂ)) ^ r * (∑' n : ℕ, gaussianLogMellinWeight w ε b (b * (n + 1))) -
      (b : ℂ)⁻¹ * (gaussianHigherMomentLogPole r ((σ : ℂ) + t * I) ε t -
        (Real.log b : ℂ) * gaussianHigherMomentPole r ((σ : ℂ) + t * I) ε t) := by
    unfold gaussianHigherMomentLogPole gaussianHigherMomentPole
    dsimp [w]
    ring
  rw [heq] at hh
  exact hh.trans (norm_mul_logVariation_le hr hσ hσ1 ht hε hsector hX hscale)

#print axioms summable_gaussianLogMellinWeight_lattice_all
#print axioms norm_tsum_gaussianLogMellinWeight_sub_integral_all_le
#print axioms norm_tsum_gaussianHigherLogMoment_sub_poles_le

end GaloisForLFunctions.ExceptionalLayerTheory
