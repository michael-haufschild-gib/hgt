import GaloisForLFunctions.RHTower.StepProfileMellinLSeries
import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.HTGeometry.ShiftDivisorLSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Power-sum densities of rational Mellin factors

Convolving a power with the integer measure gives an explicit power sum.
Abel summation identifies its Mellin transform on `Re s>1`. Conjugate pairs
of critical-line exponents give real densities for quadratic rational factors.
-/

noncomputable section
set_option autoImplicit false

open Complex MeasureTheory Set Finset
open RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The density of the integer measure convolved with one complex power. -/
def integerPowerDensity (r : ℂ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (r - 1) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℂ) ^ (-r)

private theorem critical_power_sum_bound {r : ℂ} (hr : r.re = 1 / 2) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-r)‖ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-r)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := by have := (Finset.mem_Icc.mp hn).1; omega
      rw [Complex.norm_natCast_cpow_of_pos hnpos, Complex.neg_re, hr,
        Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    _ ≤ 2 * Real.sqrt N := sum_inv_sqrt_le N
    _ = _ := by rw [Real.sqrt_eq_rpow]

private theorem integerPowerDensity_integrand {r s : ℂ} {Y : ℝ} (hY : 0 < Y) :
    (Y : ℂ) ^ (-s) * integerPowerDensity r Y =
      (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n : ℂ) ^ (-r)) *
        (Y : ℂ) ^ (-(s - r) - 1) := by
  have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  rw [integerPowerDensity, ← mul_assoc, ← Complex.cpow_add _ _ hYc]
  rw [show -s + (r - 1) = -(s - r) - 1 by ring, mul_comm]

/-- The power-sum density is absolutely Mellin integrable to the right of one. -/
theorem integrableOn_integerPowerDensity {r s : ℂ}
    (hr : r.re = 1 / 2) (hs : 1 < s.re) :
    IntegrableOn (fun Y : ℝ => (Y : ℂ) ^ (-s) * integerPowerDensity r Y) (Set.Ioi 1) := by
  have hsw : 0 < (s - r).re := by simp only [Complex.sub_re]; linarith only [hr, hs]
  have hθw : 1 / 2 < (s - r).re := by simp only [Complex.sub_re]; linarith only [hr, hs]
  have h := integrableOn_complexPartialSum (by norm_num : (0 : ℝ) ≤ 2)
    (critical_power_sum_bound hr) hsw hθw
  apply h.congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with Y hY
  exact (integerPowerDensity_integrand (lt_trans (by norm_num : (0 : ℝ) < 1) hY)).symm

/-- The literal density has transform `ζ(s)/(s-r)`, without a zero assumption. -/
theorem mellin_integerPowerDensity {r s : ℂ}
    (hr : r.re = 1 / 2) (hs : 1 < s.re) :
    (∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) * integerPowerDensity r Y) =
      riemannZeta s / (s - r) := by
  have hsw : 0 < (s - r).re := by simp only [Complex.sub_re]; linarith only [hr, hs]
  have hθw : 1 / 2 < (s - r).re := by simp only [Complex.sub_re]; linarith only [hr, hs]
  have hsum : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ (-r)) (s - r) := by
    simpa only [Pi.one_apply, mul_one, sub_add_cancel] using
      (LSeriesSummable_cpow_shift_iff r (s - r) 1).mpr
        (by simpa only [sub_add_cancel] using LSeriesSummable_one_iff.mpr hs)
  have h := mellin_complexPartialSum_eq_LSeries (by norm_num : (0 : ℝ) ≤ 2)
    (critical_power_sum_bound hr) hsw hθw hsum
  have hL : LSeries (fun n : ℕ => (n : ℂ) ^ (-r)) (s - r) = riemannZeta s := by
    simpa only [Pi.one_apply, mul_one, sub_add_cancel, LSeries_one_eq_riemannZeta hs] using
      LSeries_cpow_shift r (s - r) 1
  rw [hL] at h
  have hsr : s - r ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.zero_re] at this
    linarith only [hsw, this]
  apply (eq_div_iff hsr).mpr
  rw [mul_comm]
  convert h using 2
  apply setIntegral_congr_fun measurableSet_Ioi
  intro Y hY
  exact integerPowerDensity_integrand (lt_trans (by norm_num : (0 : ℝ) < 1) hY)

/-- Conjugation of the exponent conjugates the density on the positive axis. -/
theorem integerPowerDensity_conj (r : ℂ) {Y : ℝ} (hY : 0 ≤ Y) :
    integerPowerDensity (starRingEnd ℂ r) Y = starRingEnd ℂ (integerPowerDensity r Y) := by
  have hp : ∀ (x : ℝ), 0 ≤ x → ∀ a : ℂ,
      (x : ℂ) ^ (starRingEnd ℂ a) = starRingEnd ℂ ((x : ℂ) ^ a) := by
    intro x hx a
    simpa only [Complex.conj_ofReal] using Complex.cpow_conj (x : ℂ) a
      (by rw [Complex.arg_ofReal_of_nonneg hx]; exact Real.pi_ne_zero.symm)
  rw [integerPowerDensity, integerPowerDensity, map_mul, map_sum]
  congr 1
  · simpa only [map_sub, map_one] using hp Y hY (r - 1)
  · apply Finset.sum_congr rfl
    intro n _
    simpa only [map_neg, Complex.ofReal_natCast] using hp n (by positivity) (-r)

/-- The real density for a conjugate pair of poles on the critical line. -/
def criticalPairDensity (γ Y : ℝ) : ℝ :=
  (integerPowerDensity (1 / 2 + (γ : ℂ) * I) Y).im / γ

private theorem critical_pair_factorization (γ : ℝ) (s : ℂ) :
    (s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 =
      (s - (1 / 2 + (γ : ℂ) * I)) * (s - starRingEnd ℂ (1 / 2 + (γ : ℂ) * I)) := by
  simp only [map_add, map_div₀, map_one, map_ofNat, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  linear_combination (γ : ℂ) ^ 2 * Complex.I_sq

private theorem critical_pair_den_ne_zero (γ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
  rw [critical_pair_factorization]
  have hn : ∀ r : ℂ, r.re = 1 / 2 → s - r ≠ 0 := by
    intro r hr he
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    rw [hr] at he'
    linarith only [he', hs]
  exact mul_ne_zero (hn _ (by norm_num)) (hn _ (by norm_num))

private theorem criticalPairDensity_cast {γ Y : ℝ} (hγ : γ ≠ 0) (hY : 0 ≤ Y) :
    (criticalPairDensity γ Y : ℂ) =
      (integerPowerDensity (1 / 2 + (γ : ℂ) * I) Y -
        integerPowerDensity (starRingEnd ℂ (1 / 2 + (γ : ℂ) * I)) Y) /
          (2 * I * (γ : ℂ)) := by
  rw [integerPowerDensity_conj _ hY, criticalPairDensity, Complex.ofReal_div]
  have hid (z : ℂ) : z - starRingEnd ℂ z = 2 * I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hid]
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  field_simp [hγc]

/-- The pair density is absolutely Mellin integrable on `Re s>1`. -/
theorem integrableOn_criticalPairDensity {γ : ℝ} (hγ : γ ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun Y : ℝ => (Y : ℂ) ^ (-s) * (criticalPairDensity γ Y : ℂ)) (Set.Ioi 1) := by
  let r : ℂ := 1 / 2 + (γ : ℂ) * I
  have hr : r.re = 1 / 2 := by norm_num [r]
  have hrc : (starRingEnd ℂ r).re = 1 / 2 := by simpa using hr
  apply (((integrableOn_integerPowerDensity hr hs).sub
    (integrableOn_integerPowerDensity hrc hs)).div_const (2 * I * (γ : ℂ))).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with Y hY
  dsimp only [Pi.sub_apply]
  rw [criticalPairDensity_cast hγ (le_trans (by norm_num : (0 : ℝ) ≤ 1) hY.le)]
  dsimp only [r]
  ring

/-- A conjugate pair gives the quadratic denominator without a spectral assumption. -/
theorem mellin_criticalPairDensity {γ : ℝ} (hγ : γ ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) * (criticalPairDensity γ Y : ℂ)) =
      riemannZeta s / ((s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2) := by
  let r : ℂ := 1 / 2 + (γ : ℂ) * I
  have hr : r.re = 1 / 2 := by norm_num [r]
  have hrc : (starRingEnd ℂ r).re = 1 / 2 := by simpa using hr
  have hint : (∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) * (criticalPairDensity γ Y : ℂ)) =
      ((∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) * integerPowerDensity r Y) -
        ∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) * integerPowerDensity (starRingEnd ℂ r) Y) /
          (2 * I * (γ : ℂ)) := by
    rw [← integral_sub (integrableOn_integerPowerDensity hr hs)
      (integrableOn_integerPowerDensity hrc hs), ← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro Y hY
    dsimp only
    rw [criticalPairDensity_cast hγ (le_trans (by norm_num : (0 : ℝ) ≤ 1) hY.le)]
    dsimp only [r]
    ring
  rw [hint, mellin_integerPowerDensity hr hs, mellin_integerPowerDensity hrc hs]
  have hd₁ : s - r ≠ 0 := by
    intro he
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    rw [hr] at he'
    linarith only [he', hs]
  have hd₂ : s - starRingEnd ℂ r ≠ 0 := by
    intro he
    have he' := congrArg Complex.re (sub_eq_zero.mp he)
    rw [hrc] at he'
    linarith only [he', hs]
  have hden : (s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 = (s - r) * (s - starRingEnd ℂ r) := by
    exact critical_pair_factorization γ s
  rw [hden]
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
  field_simp [hd₁, hd₂, hγc]
  dsimp only [r]
  simp only [map_add, map_div₀, map_one, map_ofNat, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The density of a normalized quartic correction. -/
def quartetDensity (γ₁ γ₂ c Y : ℝ) : ℝ :=
  c / (γ₂ ^ 2 - γ₁ ^ 2) *
    ((γ₂ ^ 2 + 1 / 4) * criticalPairDensity γ₂ Y -
      (γ₁ ^ 2 + 1 / 4) * criticalPairDensity γ₁ Y)

private theorem quartetDensity_integrand (γ₁ γ₂ c Y : ℝ) (s : ℂ) :
    (Y : ℂ) ^ (-s) * (quartetDensity γ₁ γ₂ c Y : ℂ) =
      (c : ℂ) / ((γ₂ : ℂ) ^ 2 - (γ₁ : ℂ) ^ 2) *
        (((γ₂ : ℂ) ^ 2 + 1 / 4) * ((Y : ℂ) ^ (-s) * (criticalPairDensity γ₂ Y : ℂ)) -
          ((γ₁ : ℂ) ^ 2 + 1 / 4) * ((Y : ℂ) ^ (-s) * (criticalPairDensity γ₁ Y : ℂ))) := by
  unfold quartetDensity
  push_cast
  ring

theorem integrableOn_quartetDensity {γ₁ γ₂ : ℝ}
    (hγ₁ : γ₁ ≠ 0) (hγ₂ : γ₂ ≠ 0) (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun Y : ℝ => (Y : ℂ) ^ (-s) * (quartetDensity γ₁ γ₂ c Y : ℂ)) (Set.Ioi 1) := by
  have h := (((integrableOn_criticalPairDensity hγ₂ hs).const_mul ((γ₂ : ℂ) ^ 2 + 1 / 4)).sub
    ((integrableOn_criticalPairDensity hγ₁ hs).const_mul ((γ₁ : ℂ) ^ 2 + 1 / 4))).const_mul
      ((c : ℂ) / ((γ₂ : ℂ) ^ 2 - (γ₁ : ℂ) ^ 2))
  exact h.congr (Filter.Eventually.of_forall fun Y => (quartetDensity_integrand γ₁ γ₂ c Y s).symm)

/-- The real quartet density realizes the normalized rational correction exactly. -/
theorem mellin_quartetDensity {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (c : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ Y in Set.Ioi (1 : ℝ), (Y : ℂ) ^ (-s) * (quartetDensity γ₁ γ₂ c Y : ℂ)) =
      riemannZeta s * (c : ℂ) * s * (s - 1) /
        (((s - 1 / 2) ^ 2 + (γ₁ : ℂ) ^ 2) * ((s - 1 / 2) ^ 2 + (γ₂ : ℂ) ^ 2)) := by
  have h₂ : 0 < γ₂ := hγ₁.trans hγ₂
  have hfun := funext (fun Y => quartetDensity_integrand γ₁ γ₂ c Y s)
  rw [hfun, integral_const_mul,
    integral_sub ((integrableOn_criticalPairDensity h₂.ne' hs).const_mul _)
      ((integrableOn_criticalPairDensity hγ₁.ne' hs).const_mul _),
    integral_const_mul, integral_const_mul, mellin_criticalPairDensity h₂.ne' hs,
    mellin_criticalPairDensity hγ₁.ne' hs]
  have hd : (γ₂ : ℂ) ^ 2 - (γ₁ : ℂ) ^ 2 ≠ 0 := by
    have hp := mul_pos (sub_pos.mpr hγ₂) (add_pos h₂ hγ₁)
    have hreal : γ₂ ^ 2 - γ₁ ^ 2 ≠ 0 := by nlinarith only [hp]
    exact_mod_cast hreal
  set d₁ : ℂ := (s - 1 / 2) ^ 2 + (γ₁ : ℂ) ^ 2
  set d₂ : ℂ := (s - 1 / 2) ^ 2 + (γ₂ : ℂ) ^ 2
  have hd₁ : d₁ ≠ 0 := critical_pair_den_ne_zero γ₁ hs
  have hd₂ : d₂ ≠ 0 := critical_pair_den_ne_zero γ₂ hs
  field_simp [hd, hd₁, hd₂]
  dsimp only [d₁, d₂]
  ring

#print axioms mellin_integerPowerDensity
#print axioms mellin_criticalPairDensity
#print axioms mellin_quartetDensity

end GaloisForLFunctions.ArithmeticPositiveDuality
