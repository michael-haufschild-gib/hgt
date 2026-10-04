import GaloisForLFunctions.HTGeometry.HelsonCharacterLSeries
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!
# A strict integral phase gap for a one-prime Liouville twist

The completely multiplicative source has value `I` at the prime `2` and value `-1` at every
other prime. Its full exponential harmonic density has noncollinear values at `u` and `2 * u`
for every `u > log 16`. The geometric estimate retains the entire tail after the first two
nonzero coefficients; no finite truncation is substituted for the density.

This yields an unconditional strict triangle gap on a compact interval for the weighted
integral of the actual source. It supplies the phase-separation ingredient of MC-C12.92's
moving-prime simple-zero argument. This module does not prove that simple-zero theorem,
Liouville positivity, a critical cancellation estimate, or RH.
-/

open Complex Filter
open scoped Topology BigOperators

namespace RHTower.LiouvilleTwistedDensity

noncomputable section

/-- Change only the prime-two value of the Liouville prime phases. -/
def primePhase (p : ℕ) : ℂ := if p = 2 then I else -1

/-- The full completely multiplicative source. -/
def twist : ℕ →*₀ ℂ := GaloisForLFunctions.HTGeometry.phaseChar primePhase

@[simp] theorem twist_zero : twist 0 = 0 := map_zero twist
@[simp] theorem twist_one : twist 1 = 1 := map_one twist

@[simp] theorem twist_two : twist 2 = I := by
  rw [twist, GaloisForLFunctions.HTGeometry.phaseChar_prime _ Nat.prime_two]
  simp [primePhase]

theorem norm_twist_le_one (n : ℕ) : ‖twist n‖ ≤ 1 := by
  apply GaloisForLFunctions.HTGeometry.norm_phaseChar_le_one
  intro p _
  by_cases hp : p = 2 <;> simp [primePhase, hp]

/-- Harmonic coefficients, with the zero-index coefficient equal to zero. -/
def coefficient (n : ℕ) : ℂ := twist n / n

/-- The full Abel density, evaluated below at real radii in `(0, 1)`. -/
def density (q : ℝ) : ℂ := ∑' n : ℕ, coefficient n * (q : ℂ) ^ n

theorem norm_coefficient_le_one (n : ℕ) : ‖coefficient n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coefficient]
  · rw [coefficient, norm_div, Complex.norm_natCast]
    apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    exact (norm_twist_le_one n).trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

private theorem norm_term_le {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ‖coefficient n * (q : ℂ) ^ n‖ ≤ q ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  exact mul_le_of_le_one_left (pow_nonneg hq n) (norm_coefficient_le_one n)

theorem summable_density {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => coefficient n * (q : ℂ) ^ n) :=
  (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded (norm_term_le hq0)

/-- The full tail after the linear and imaginary quadratic terms. -/
theorem density_second_order {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ‖density q - ((q : ℂ) + I * (q : ℂ) ^ 2 / 2)‖ ≤ q ^ 3 / (1 - q) := by
  have h := norm_sub_le_of_geometric_bound_of_hasSum hq1
    (C := 1) (fun n => by simpa using norm_term_le hq0 n)
    (summable_density hq0 hq1).hasSum 3
  have hhead : (∑ n ∈ Finset.range 3, coefficient n * (q : ℂ) ^ n) =
      (q : ℂ) + I * (q : ℂ) ^ 2 / 2 := by
    simp [Finset.sum_range_succ, coefficient]
    ring
  rw [hhead, norm_sub_rev] at h
  simpa only [one_mul, density] using h

private theorem density_components {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1 / 16) :
    q / 2 ≤ (density q).re ∧ (density q).re ≤ 2 * q ∧
      q ^ 2 / 4 ≤ (density q).im ∧ (density q).im ≤ q ^ 2 := by
  have hq : q < 1 := by linarith
  have htail := density_second_order hq0.le hq
  have hbound : q ^ 3 / (1 - q) ≤ 2 * q ^ 3 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - q)]
    nlinarith [mul_nonneg (pow_nonneg hq0.le 3) (show 0 ≤ 1 - 2 * q by linarith)]
  have hre := (Complex.abs_re_le_norm
    (density q - ((q : ℂ) + I * (q : ℂ) ^ 2 / 2))).trans (htail.trans hbound)
  have him := (Complex.abs_im_le_norm
    (density q - ((q : ℂ) + I * (q : ℂ) ^ 2 / 2))).trans (htail.trans hbound)
  simp [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im] at hre him
  have hcub : 2 * q ^ 3 ≤ q ^ 2 / 4 := by
    nlinarith [mul_nonneg (sq_nonneg q) (show 0 ≤ 1 / 8 - q by linarith)]
  have hsq : q ^ 2 ≤ q := by nlinarith [mul_nonneg hq0.le (le_of_lt (sub_pos.mpr hq))]
  rcases abs_le.mp hre with ⟨hrel, hreu⟩
  rcases abs_le.mp him with ⟨himl, himu⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The complete values at radii `q` and `q²` have distinct complex directions. -/
theorem density_phase_separation {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1 / 16) :
    0 < ((starRingEnd ℂ) (density (q ^ 2)) * density q).im := by
  have hq : q < 1 := by linarith
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq0
  have hq2lt : q ^ 2 < q := by nlinarith [mul_pos hq0 (sub_pos.mpr hq)]
  obtain ⟨hre, hre', him, him'⟩ := density_components hq0 hq1
  obtain ⟨hres, hres', hims, hims'⟩ := density_components hq2 (hq2lt.trans hq1)
  have hlo : q ^ 4 / 8 ≤ (density (q ^ 2)).re * (density q).im := by
    calc
      q ^ 4 / 8 = (q ^ 2 / 2) * (q ^ 2 / 4) := by ring
      _ ≤ (density (q ^ 2)).re * (density q).im :=
        mul_le_mul hres him (by positivity) (by linarith)
  have hhi : (density (q ^ 2)).im * (density q).re ≤ 2 * q ^ 5 := by
    calc
      (density (q ^ 2)).im * (density q).re ≤ (q ^ 2) ^ 2 * (2 * q) :=
        mul_le_mul hims' hre' (by linarith) (by positivity)
      _ = 2 * q ^ 5 := by ring
  have hgap : 0 < q ^ 4 / 8 - 2 * q ^ 5 := by
    have h := mul_pos (pow_pos hq0 4) (show 0 < 1 / 8 - 2 * q by linarith)
    nlinarith
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  nlinarith

/-- The actual exponentially smoothed harmonic source. -/
def exponentialDensity : ℝ → ℂ :=
  GaloisForLFunctions.HTGeometry.coeffLaplaceProfile coefficient

theorem exponentialDensity_eq_density (u : ℝ) :
    exponentialDensity u = density (Real.exp (-u)) :=
  GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow coefficient u

theorem continuousOn_exponentialDensity :
    ContinuousOn exponentialDensity (Set.Ioi 0) :=
  GaloisForLFunctions.HTGeometry.continuousOn_coeffLaplaceProfile norm_coefficient_le_one

/-- Strict phase separation at two physical scales. -/
theorem exponentialDensity_phase_separation {u : ℝ} (hu : Real.log 16 < u) :
    0 < ((starRingEnd ℂ) (exponentialDensity (2 * u)) * exponentialDensity u).im := by
  rw [exponentialDensity_eq_density, exponentialDensity_eq_density]
  have heq : Real.exp (-(2 * u)) = Real.exp (-u) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [heq]
  apply density_phase_separation (Real.exp_pos _)
  calc
    Real.exp (-u) < Real.exp (-Real.log 16) := Real.exp_lt_exp.mpr (neg_lt_neg hu)
    _ = 1 / 16 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

private theorem norm_integral_lt_of_cross_im_ne_zero {f : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hcross : ((starRingEnd ℂ) (f b) * f a).im ≠ 0) :
    ‖∫ x in a..b, f x‖ < ∫ x in a..b, ‖f x‖ := by
  obtain ⟨c, hc, hrotate⟩ := Complex.exists_norm_eq_mul_self (∫ x in a..b, f x)
  have hnorm (z : ℂ) : ‖c * z‖ = ‖z‖ := by rw [norm_mul, hc, one_mul]
  have hle (z : ℂ) : (c * z).re ≤ ‖z‖ :=
    ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans_eq (hnorm z)
  have him (z : ℂ) (hz : (c * z).re = ‖z‖) : (c * z).im = 0 := by
    have hs := Complex.sq_norm_sub_sq_re (c * z)
    rw [hnorm, hz] at hs
    nlinarith
  have hprod : (starRingEnd ℂ) (c * f b) * (c * f a) =
      (starRingEnd ℂ) (f b) * f a := by
    calc
      _ = ((starRingEnd ℂ) c * c) * ((starRingEnd ℂ) (f b) * f a) := by
        rw [map_mul]
        ring
      _ = _ := by rw [Complex.conj_mul', hc]; simp
  have hstrict : (c * f a).re < ‖f a‖ ∨ (c * f b).re < ‖f b‖ := by
    by_contra h
    push Not at h
    have ha := him (f a) (le_antisymm (hle _) h.1)
    have hb := him (f b) (le_antisymm (hle _) h.2)
    have hz : ((starRingEnd ℂ) (c * f b) * (c * f a)).im = 0 := by
      rw [Complex.mul_im, Complex.conj_im, ha, hb]
      simp
    rw [hprod] at hz
    exact hcross hz
  have hcf : ContinuousOn (fun x => c * f x) (Set.Icc a b) := continuousOn_const.mul hf
  have hgap := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (Complex.continuous_re.comp_continuousOn hcf) hf.norm
    (fun x _ => hle (f x)) (hstrict.elim
      (fun h => ⟨a, ⟨le_rfl, hab.le⟩, h⟩)
      (fun h => ⟨b, ⟨hab.le, le_rfl⟩, h⟩))
  change (∫ x in a..b, (c * f x).re) < ∫ x in a..b, ‖f x‖ at hgap
  have hint : (∫ x in a..b, (c * f x).re) = ‖∫ x in a..b, f x‖ := by
    calc
      _ = (∫ x in a..b, c * f x).re :=
        Complex.reCLM.intervalIntegral_comp_comm (hcf.intervalIntegrable_of_Icc hab.le)
      _ = (c * ∫ x in a..b, f x).re := by rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [← hrotate, Complex.ofReal_re]
  rwa [hint] at hgap

/-- The strict integral gap needed for the moving-prime linear capacity. -/
theorem exponentialDensity_integral_gap {u : ℝ} (hu : Real.log 16 < u) :
    ‖∫ x in u..2 * u, exponentialDensity x / (x : ℂ)‖ <
      ∫ x in u..2 * u, ‖exponentialDensity x / (x : ℂ)‖ := by
  have hu0 : 0 < u := (Real.log_pos (by norm_num : (1 : ℝ) < 16)).trans hu
  have hf : ContinuousOn exponentialDensity (Set.Icc u (2 * u)) :=
    continuousOn_exponentialDensity.mono (fun x hx => hu0.trans_le hx.1)
  apply norm_integral_lt_of_cross_im_ne_zero (by linarith)
    (hf.div Complex.continuous_ofReal.continuousOn (fun x hx =>
      Complex.ofReal_ne_zero.mpr (hu0.trans_le hx.1).ne'))
  have heq : (starRingEnd ℂ) (exponentialDensity (2 * u) / ((2 * u : ℝ) : ℂ)) *
      (exponentialDensity u / (u : ℂ)) =
      ((starRingEnd ℂ) (exponentialDensity (2 * u)) * exponentialDensity u) /
        (((2 * u) * u : ℝ) : ℂ) := by
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, ← Complex.ofReal_mul]
  change ((starRingEnd ℂ) (exponentialDensity (2 * u) / ((2 * u : ℝ) : ℂ)) *
    (exponentialDensity u / (u : ℂ))).im ≠ 0
  rw [heq, Complex.div_ofReal_im]
  exact (div_pos (exponentialDensity_phase_separation hu) (by positivity)).ne'

/-- An unconditional compact interval with a strict phase gap. -/
theorem exists_exponentialDensity_integral_gap :
    ∃ u : ℝ, 1 < u ∧
      ‖∫ x in u..2 * u, exponentialDensity x / (x : ℂ)‖ <
        ∫ x in u..2 * u, ‖exponentialDensity x / (x : ℂ)‖ := by
  refine ⟨Real.log 16 + 1, ?_, exponentialDensity_integral_gap (by linarith)⟩
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 16)
  linarith

end
end RHTower.LiouvilleTwistedDensity
