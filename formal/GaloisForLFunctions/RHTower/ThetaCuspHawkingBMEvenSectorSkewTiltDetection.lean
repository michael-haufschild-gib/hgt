import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewTrace

/-!
# Elementary tilt detection by the skew cut's horizon logarithm

For `s = σ − 2 + i t` (so `ρ = σ + i t`) put `w = −3 − conj s = −1 − σ + i t`. The reflection
oddness `skewLogCoeff (−3 − s) = −skewLogCoeff s` and the real coefficients give
`skewLogCoeff s + conj (skewLogCoeff s) = skewLogCoeff s − skewLogCoeff w`, and the difference
quotient `skewLogCoeff_sub` turns this into
`2·Re(skewLogCoeff s)·|s(s+3)|² = (2σ − 1)·skewTiltCofactor σ t` (`skewLogCoeff_re_tilt`), where
`skewTiltCofactor` is an explicit real polynomial (`skewLogCofactor_reflected`). Its leading term is
`−(675/2048)·t¹²` and on the strip `0 ≤ σ ≤ 1` it is negative for `t ≥ 35`
(`skewTiltCofactor_neg`). Hence for every point of the strip of height at least `35` the horizon
logarithm coefficient of the elementary skew cut has zero real part exactly on the critical line
(`skewLogCoeff_re_eq_zero_iff`): the leading term of the skew cut detects the tilt `Re ρ − 1/2`
linearly, with a sign-definite cofactor.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- The reflected-pair cofactor as a real polynomial in `σ = Re ρ` and `t = Im ρ`. -/
noncomputable def skewTiltCofactor (σ t : ℝ) : ℝ := (471 / 16 : ℝ) + (3015 / 128 : ℝ) * t ^ 2 + (-435 / 64 : ℝ) * t ^ 4 + (-29961 / 2048 : ℝ) * t ^ 6 + (-5925 / 2048 : ℝ) * t ^ 8 + (-2703 / 2048 : ℝ) * t ^ 10 + (-675 / 2048 : ℝ) * t ^ 12 + (1587 / 64 : ℝ) * σ + (-4773 / 128 : ℝ) * σ * t ^ 2 + (-46701 / 1024 : ℝ) * σ * t ^ 4 + (-10845 / 1024 : ℝ) * σ * t ^ 6 + (-17667 / 1024 : ℝ) * σ * t ^ 8 + (-2475 / 1024 : ℝ) * σ * t ^ 10 + (-2913 / 128 : ℝ) * σ ^ 2 + (891 / 128 : ℝ) * σ ^ 2 * t ^ 2 + (71877 / 2048 : ℝ) * σ ^ 2 * t ^ 4 + (-6399 / 256 : ℝ) * σ ^ 2 * t ^ 6 + (37809 / 2048 : ℝ) * σ ^ 2 * t ^ 8 + (2475 / 1024 : ℝ) * σ ^ 2 * t ^ 10 + (-897 / 128 : ℝ) * σ ^ 3 + (24933 / 512 : ℝ) * σ ^ 3 * t ^ 2 + (-3363 / 1024 : ℝ) * σ ^ 3 * t ^ 4 + (9729 / 128 : ℝ) * σ ^ 3 * t ^ 6 + (-2475 / 1024 : ℝ) * σ ^ 3 * t ^ 8 + (1269 / 128 : ℝ) * σ ^ 4 + (-387 / 2048 : ℝ) * σ ^ 4 * t ^ 2 + (61839 / 1024 : ℝ) * σ ^ 4 * t ^ 4 + (-51291 / 1024 : ℝ) * σ ^ 4 * t ^ 6 + (2475 / 2048 : ℝ) * σ ^ 4 * t ^ 8 + (-5433 / 1024 : ℝ) * σ ^ 5 + (-14511 / 1024 : ℝ) * σ ^ 5 * t ^ 2 + (-33207 / 512 : ℝ) * σ ^ 5 * t ^ 4 + (7425 / 512 : ℝ) * σ ^ 5 * t ^ 6 + (-3537 / 2048 : ℝ) * σ ^ 6 + (-2079 / 128 : ℝ) * σ ^ 6 * t ^ 2 + (12513 / 1024 : ℝ) * σ ^ 6 * t ^ 4 + (-2475 / 512 : ℝ) * σ ^ 6 * t ^ 6 + (2199 / 1024 : ℝ) * σ ^ 7 + (21 / 2 : ℝ) * σ ^ 7 * t ^ 2 + (4125 / 512 : ℝ) * σ ^ 7 * t ^ 4 + (543 / 2048 : ℝ) * σ ^ 8 + (13749 / 2048 : ℝ) * σ ^ 8 * t ^ 2 + (-4125 / 2048 : ℝ) * σ ^ 8 * t ^ 4 + (-135 / 1024 : ℝ) * σ ^ 9 + (-6375 / 1024 : ℝ) * σ ^ 9 * t ^ 2 + (-771 / 2048 : ℝ) * σ ^ 10 + (1275 / 1024 : ℝ) * σ ^ 10 * t ^ 2 + (225 / 1024 : ℝ) * σ ^ 11 + (-75 / 2048 : ℝ) * σ ^ 12

/-- The difference-quotient cofactor at the reflected pair `(s, −3 − conj s)` is the real polynomial. -/
theorem skewLogCofactor_reflected (σ t : ℝ) :
    skewLogCofactor ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) (-1 - (σ : ℂ) + (t : ℂ) * Complex.I) = (skewTiltCofactor σ t : ℂ) := by
  unfold skewLogCofactor skewTiltCofactor
  push_cast
  linear_combination ((-3015 / 128 : ℂ) * (t : ℂ) ^ 2 + (435 / 64 : ℂ) * (t : ℂ) ^ 4 + (-435 / 64 : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (29961 / 2048 : ℂ) * (t : ℂ) ^ 6 + (-29961 / 2048 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (29961 / 2048 : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (5925 / 2048 : ℂ) * (t : ℂ) ^ 8 + (-5925 / 2048 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (5925 / 2048 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-5925 / 2048 : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (2703 / 2048 : ℂ) * (t : ℂ) ^ 10 + (-2703 / 2048 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 2 + (2703 / 2048 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 4 + (-2703 / 2048 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 6 + (2703 / 2048 : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 8 + (675 / 2048 : ℂ) * (t : ℂ) ^ 12 + (-675 / 2048 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 2 + (675 / 2048 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 4 + (-675 / 2048 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 6 + (675 / 2048 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 8 + (-675 / 2048 : ℂ) * (t : ℂ) ^ 12 * Complex.I ^ 10 + (4773 / 128 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 2 + (46701 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 + (-46701 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 4 * Complex.I ^ 2 + (10845 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 + (-10845 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 2 + (10845 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 6 * Complex.I ^ 4 + (17667 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 + (-17667 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 2 + (17667 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-17667 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 8 * Complex.I ^ 6 + (2475 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 + (-2475 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 2 + (2475 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 4 + (-2475 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 6 + (2475 / 1024 : ℂ) * (σ : ℂ) * (t : ℂ) ^ 10 * Complex.I ^ 8 + (-891 / 128 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 2 + (-71877 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 + (71877 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (6399 / 256 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 + (-6399 / 256 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (6399 / 256 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-37809 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 + (37809 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-37809 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (37809 / 2048 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 + (2475 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 2 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 4 + (2475 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 6 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 2 * (t : ℂ) ^ 10 * Complex.I ^ 8 + (-24933 / 512 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 2 + (3363 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 + (-3363 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-9729 / 128 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 + (9729 / 128 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-9729 / 128 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (2475 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (2475 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (-2475 / 1024 : ℂ) * (σ : ℂ) ^ 3 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (387 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 2 + (-61839 / 1024 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 + (61839 / 1024 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (51291 / 1024 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 + (-51291 / 1024 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (51291 / 1024 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 2 + (-2475 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 4 + (2475 / 2048 : ℂ) * (σ : ℂ) ^ 4 * (t : ℂ) ^ 8 * Complex.I ^ 6 + (14511 / 1024 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 2 + (33207 / 512 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 4 + (-33207 / 512 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-7425 / 512 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 + (7425 / 512 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (-7425 / 512 : ℂ) * (σ : ℂ) ^ 5 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (2079 / 128 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 2 + (-12513 / 1024 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 4 + (12513 / 1024 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (2475 / 512 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 + (-2475 / 512 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 * Complex.I ^ 2 + (2475 / 512 : ℂ) * (σ : ℂ) ^ 6 * (t : ℂ) ^ 6 * Complex.I ^ 4 + (-21 / 2 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 2 + (-4125 / 512 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 4 + (4125 / 512 : ℂ) * (σ : ℂ) ^ 7 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (-13749 / 2048 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 2 + (4125 / 2048 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 4 + (-4125 / 2048 : ℂ) * (σ : ℂ) ^ 8 * (t : ℂ) ^ 4 * Complex.I ^ 2 + (6375 / 1024 : ℂ) * (σ : ℂ) ^ 9 * (t : ℂ) ^ 2 + (-1275 / 1024 : ℂ) * (σ : ℂ) ^ 10 * (t : ℂ) ^ 2) * Complex.I_sq

/-- The logarithm coefficient has real coefficients. -/
theorem skewLogCoeff_conj (s : ℂ) : skewLogCoeff (starRingEnd ℂ s) = starRingEnd ℂ (skewLogCoeff s) := by
  unfold skewLogCoeff
  simp only [map_div₀, map_add, map_mul, map_pow, map_neg, map_ofNat]

/-- The real part of the logarithm coefficient is the tilt times the cofactor. -/
theorem skewLogCoeff_re_tilt (σ t : ℝ) (hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0)
    (hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0) :
    2 * (skewLogCoeff ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re *
        Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) =
      (2 * σ - 1) * skewTiltCofactor σ t := by
  set s : ℂ := (σ : ℂ) - 2 + (t : ℂ) * Complex.I with hsdef
  set w : ℂ := -1 - (σ : ℂ) + (t : ℂ) * Complex.I with hwdef
  have hw : w ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp [hwdef] at h1 h2
    apply hs3; apply Complex.ext <;> simp [hsdef] <;> linarith
  have hw3 : w + 3 ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h; have h2 := congrArg Complex.im h
    simp [hwdef] at h1 h2
    apply hs; apply Complex.ext <;> simp [hsdef] <;> linarith
  have hconj : starRingEnd ℂ s = -3 - w := by
    apply Complex.ext <;> simp [hsdef, hwdef]
    ring
  have hodd : skewLogCoeff w = -(starRingEnd ℂ (skewLogCoeff s)) := by
    have hc := skewLogCoeff_conj s
    rw [hconj, skewLogCoeff_reflect w hw hw3] at hc
    rw [← hc]; ring
  have hsum : skewLogCoeff s - skewLogCoeff w = (2 * (skewLogCoeff s).re : ℂ) := by
    rw [hodd, sub_neg_eq_add, Complex.add_conj]; push_cast; ring
  have hsub := skewLogCoeff_sub s w hs hs3 hw hw3
  have hsw : s - w = ((2 * σ - 1 : ℝ) : ℂ) := by rw [hsdef, hwdef]; push_cast; ring
  have hden : s * (s + 3) * (w * (w + 3)) = (Complex.normSq (s * (s + 3)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : starRingEnd ℂ (s * (s + 3)) = w * (w + 3) := by
      apply Complex.ext <;> simp [hsdef, hwdef] <;> ring
    rw [this]; ring
  have hcof : skewLogCofactor s w = (skewTiltCofactor σ t : ℂ) := by
    rw [hsdef, hwdef]; exact skewLogCofactor_reflected σ t
  rw [hsw, hden, hcof] at hsub
  have hns : (Complex.normSq (s * (s + 3)) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr (mul_ne_zero hs hs3)).ne'
  have key : (2 * (skewLogCoeff s).re : ℂ) * (Complex.normSq (s * (s + 3)) : ℂ) = ((2 * σ - 1 : ℝ) : ℂ) * (skewTiltCofactor σ t : ℂ) := by
    rw [← hsum, hsub]; field_simp
  have key' : (2 * (skewLogCoeff s).re * Complex.normSq (s * (s + 3)) : ℝ) = (2 * σ - 1) * skewTiltCofactor σ t := by
    exact_mod_cast key
  exact key'

theorem skewMono_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) (a b : ℕ) (hb : b ≤ 10) :
    σ ^ a * t ^ b ≤ t ^ 10 := by
  calc σ ^ a * t ^ b ≤ 1 * t ^ 10 :=
        mul_le_mul (pow_le_one₀ h0 h1) (pow_le_pow_right₀ ht1 hb) (pow_nonneg (by linarith) b) zero_le_one
    _ = t ^ 10 := one_mul _

theorem skewMono_nonneg (σ t : ℝ) (h0 : 0 ≤ σ) (ht1 : 1 ≤ t) (a b : ℕ) : 0 ≤ σ ^ a * t ^ b :=
  mul_nonneg (pow_nonneg h0 a) (pow_nonneg (by linarith) b)

/-- Group 1 of the lower-order monomials of the cofactor. -/
noncomputable def skewTiltPart1 (σ t : ℝ) : ℝ := (471 / 16 : ℝ) * (σ ^ 0 * t ^ 0) + (-5925 / 2048 : ℝ) * (σ ^ 0 * t ^ 8) + (-46701 / 1024 : ℝ) * (σ ^ 1 * t ^ 4) + (-2913 / 128 : ℝ) * (σ ^ 2 * t ^ 0) + (37809 / 2048 : ℝ) * (σ ^ 2 * t ^ 8) + (-3363 / 1024 : ℝ) * (σ ^ 3 * t ^ 4) + (-387 / 2048 : ℝ) * (σ ^ 4 * t ^ 2) + (-5433 / 1024 : ℝ) * (σ ^ 5 * t ^ 0) + (-3537 / 2048 : ℝ) * (σ ^ 6 * t ^ 0) + (2199 / 1024 : ℝ) * (σ ^ 7 * t ^ 0) + (13749 / 2048 : ℝ) * (σ ^ 8 * t ^ 2) + (-771 / 2048 : ℝ) * (σ ^ 10 * t ^ 0)

theorem skewTiltPart1_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltPart1 σ t ≤ (29061 / 512 : ℝ) * t ^ 10 := by
  unfold skewTiltPart1
  have hb_0_0 : (471 / 16 : ℝ) * (σ ^ 0 * t ^ 0) ≤ (471 / 16 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 0 (by norm_num)) (show (0 : ℝ) ≤ (471 / 16 : ℝ) by norm_num)
  have hb_0_8 : (-5925 / 2048 : ℝ) * (σ ^ 0 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5925 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 8)
    rw [zero_mul] at this
    exact this
  have hb_1_4 : (-46701 / 1024 : ℝ) * (σ ^ 1 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-46701 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 4)
    rw [zero_mul] at this
    exact this
  have hb_2_0 : (-2913 / 128 : ℝ) * (σ ^ 2 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2913 / 128 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 0)
    rw [zero_mul] at this
    exact this
  have hb_2_8 : (37809 / 2048 : ℝ) * (σ ^ 2 * t ^ 8) ≤ (37809 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 8 (by norm_num)) (show (0 : ℝ) ≤ (37809 / 2048 : ℝ) by norm_num)
  have hb_3_4 : (-3363 / 1024 : ℝ) * (σ ^ 3 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-3363 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 4)
    rw [zero_mul] at this
    exact this
  have hb_4_2 : (-387 / 2048 : ℝ) * (σ ^ 4 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-387 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 2)
    rw [zero_mul] at this
    exact this
  have hb_5_0 : (-5433 / 1024 : ℝ) * (σ ^ 5 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-5433 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 0)
    rw [zero_mul] at this
    exact this
  have hb_6_0 : (-3537 / 2048 : ℝ) * (σ ^ 6 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-3537 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 0)
    rw [zero_mul] at this
    exact this
  have hb_7_0 : (2199 / 1024 : ℝ) * (σ ^ 7 * t ^ 0) ≤ (2199 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 0 (by norm_num)) (show (0 : ℝ) ≤ (2199 / 1024 : ℝ) by norm_num)
  have hb_8_2 : (13749 / 2048 : ℝ) * (σ ^ 8 * t ^ 2) ≤ (13749 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 8 2 (by norm_num)) (show (0 : ℝ) ≤ (13749 / 2048 : ℝ) by norm_num)
  have hb_10_0 : (-771 / 2048 : ℝ) * (σ ^ 10 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-771 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 10 0)
    rw [zero_mul] at this
    exact this
  linarith

/-- Group 2 of the lower-order monomials of the cofactor. -/
noncomputable def skewTiltPart2 (σ t : ℝ) : ℝ := (3015 / 128 : ℝ) * (σ ^ 0 * t ^ 2) + (-2703 / 2048 : ℝ) * (σ ^ 0 * t ^ 10) + (-10845 / 1024 : ℝ) * (σ ^ 1 * t ^ 6) + (891 / 128 : ℝ) * (σ ^ 2 * t ^ 2) + (2475 / 1024 : ℝ) * (σ ^ 2 * t ^ 10) + (9729 / 128 : ℝ) * (σ ^ 3 * t ^ 6) + (61839 / 1024 : ℝ) * (σ ^ 4 * t ^ 4) + (-14511 / 1024 : ℝ) * (σ ^ 5 * t ^ 2) + (-2079 / 128 : ℝ) * (σ ^ 6 * t ^ 2) + (21 / 2 : ℝ) * (σ ^ 7 * t ^ 2) + (-4125 / 2048 : ℝ) * (σ ^ 8 * t ^ 4) + (1275 / 1024 : ℝ) * (σ ^ 10 * t ^ 2)

theorem skewTiltPart2_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltPart2 σ t ≤ (185421 / 1024 : ℝ) * t ^ 10 := by
  unfold skewTiltPart2
  have hb_0_2 : (3015 / 128 : ℝ) * (σ ^ 0 * t ^ 2) ≤ (3015 / 128 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 0 2 (by norm_num)) (show (0 : ℝ) ≤ (3015 / 128 : ℝ) by norm_num)
  have hb_0_10 : (-2703 / 2048 : ℝ) * (σ ^ 0 * t ^ 10) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2703 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 10)
    rw [zero_mul] at this
    exact this
  have hb_1_6 : (-10845 / 1024 : ℝ) * (σ ^ 1 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-10845 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 6)
    rw [zero_mul] at this
    exact this
  have hb_2_2 : (891 / 128 : ℝ) * (σ ^ 2 * t ^ 2) ≤ (891 / 128 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 2 (by norm_num)) (show (0 : ℝ) ≤ (891 / 128 : ℝ) by norm_num)
  have hb_2_10 : (2475 / 1024 : ℝ) * (σ ^ 2 * t ^ 10) ≤ (2475 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 10 (by norm_num)) (show (0 : ℝ) ≤ (2475 / 1024 : ℝ) by norm_num)
  have hb_3_6 : (9729 / 128 : ℝ) * (σ ^ 3 * t ^ 6) ≤ (9729 / 128 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 6 (by norm_num)) (show (0 : ℝ) ≤ (9729 / 128 : ℝ) by norm_num)
  have hb_4_4 : (61839 / 1024 : ℝ) * (σ ^ 4 * t ^ 4) ≤ (61839 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 4 (by norm_num)) (show (0 : ℝ) ≤ (61839 / 1024 : ℝ) by norm_num)
  have hb_5_2 : (-14511 / 1024 : ℝ) * (σ ^ 5 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-14511 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 2)
    rw [zero_mul] at this
    exact this
  have hb_6_2 : (-2079 / 128 : ℝ) * (σ ^ 6 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2079 / 128 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 2)
    rw [zero_mul] at this
    exact this
  have hb_7_2 : (21 / 2 : ℝ) * (σ ^ 7 * t ^ 2) ≤ (21 / 2 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 2 (by norm_num)) (show (0 : ℝ) ≤ (21 / 2 : ℝ) by norm_num)
  have hb_8_4 : (-4125 / 2048 : ℝ) * (σ ^ 8 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-4125 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 8 4)
    rw [zero_mul] at this
    exact this
  have hb_10_2 : (1275 / 1024 : ℝ) * (σ ^ 10 * t ^ 2) ≤ (1275 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 10 2 (by norm_num)) (show (0 : ℝ) ≤ (1275 / 1024 : ℝ) by norm_num)
  linarith

/-- Group 3 of the lower-order monomials of the cofactor. -/
noncomputable def skewTiltPart3 (σ t : ℝ) : ℝ := (-435 / 64 : ℝ) * (σ ^ 0 * t ^ 4) + (1587 / 64 : ℝ) * (σ ^ 1 * t ^ 0) + (-17667 / 1024 : ℝ) * (σ ^ 1 * t ^ 8) + (71877 / 2048 : ℝ) * (σ ^ 2 * t ^ 4) + (-897 / 128 : ℝ) * (σ ^ 3 * t ^ 0) + (-2475 / 1024 : ℝ) * (σ ^ 3 * t ^ 8) + (-51291 / 1024 : ℝ) * (σ ^ 4 * t ^ 6) + (-33207 / 512 : ℝ) * (σ ^ 5 * t ^ 4) + (12513 / 1024 : ℝ) * (σ ^ 6 * t ^ 4) + (4125 / 512 : ℝ) * (σ ^ 7 * t ^ 4) + (-135 / 1024 : ℝ) * (σ ^ 9 * t ^ 0) + (225 / 1024 : ℝ) * (σ ^ 11 * t ^ 0)

theorem skewTiltPart3_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltPart3 σ t ≤ (164637 / 2048 : ℝ) * t ^ 10 := by
  unfold skewTiltPart3
  have hb_0_4 : (-435 / 64 : ℝ) * (σ ^ 0 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-435 / 64 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 4)
    rw [zero_mul] at this
    exact this
  have hb_1_0 : (1587 / 64 : ℝ) * (σ ^ 1 * t ^ 0) ≤ (1587 / 64 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 1 0 (by norm_num)) (show (0 : ℝ) ≤ (1587 / 64 : ℝ) by norm_num)
  have hb_1_8 : (-17667 / 1024 : ℝ) * (σ ^ 1 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-17667 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 8)
    rw [zero_mul] at this
    exact this
  have hb_2_4 : (71877 / 2048 : ℝ) * (σ ^ 2 * t ^ 4) ≤ (71877 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 2 4 (by norm_num)) (show (0 : ℝ) ≤ (71877 / 2048 : ℝ) by norm_num)
  have hb_3_0 : (-897 / 128 : ℝ) * (σ ^ 3 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-897 / 128 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 0)
    rw [zero_mul] at this
    exact this
  have hb_3_8 : (-2475 / 1024 : ℝ) * (σ ^ 3 * t ^ 8) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 3 8)
    rw [zero_mul] at this
    exact this
  have hb_4_6 : (-51291 / 1024 : ℝ) * (σ ^ 4 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-51291 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 4 6)
    rw [zero_mul] at this
    exact this
  have hb_5_4 : (-33207 / 512 : ℝ) * (σ ^ 5 * t ^ 4) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-33207 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 5 4)
    rw [zero_mul] at this
    exact this
  have hb_6_4 : (12513 / 1024 : ℝ) * (σ ^ 6 * t ^ 4) ≤ (12513 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 6 4 (by norm_num)) (show (0 : ℝ) ≤ (12513 / 1024 : ℝ) by norm_num)
  have hb_7_4 : (4125 / 512 : ℝ) * (σ ^ 7 * t ^ 4) ≤ (4125 / 512 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 7 4 (by norm_num)) (show (0 : ℝ) ≤ (4125 / 512 : ℝ) by norm_num)
  have hb_9_0 : (-135 / 1024 : ℝ) * (σ ^ 9 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-135 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 0)
    rw [zero_mul] at this
    exact this
  have hb_11_0 : (225 / 1024 : ℝ) * (σ ^ 11 * t ^ 0) ≤ (225 / 1024 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 11 0 (by norm_num)) (show (0 : ℝ) ≤ (225 / 1024 : ℝ) by norm_num)
  linarith

/-- Group 4 of the lower-order monomials of the cofactor. -/
noncomputable def skewTiltPart4 (σ t : ℝ) : ℝ := (-29961 / 2048 : ℝ) * (σ ^ 0 * t ^ 6) + (-4773 / 128 : ℝ) * (σ ^ 1 * t ^ 2) + (-2475 / 1024 : ℝ) * (σ ^ 1 * t ^ 10) + (-6399 / 256 : ℝ) * (σ ^ 2 * t ^ 6) + (24933 / 512 : ℝ) * (σ ^ 3 * t ^ 2) + (1269 / 128 : ℝ) * (σ ^ 4 * t ^ 0) + (2475 / 2048 : ℝ) * (σ ^ 4 * t ^ 8) + (7425 / 512 : ℝ) * (σ ^ 5 * t ^ 6) + (-2475 / 512 : ℝ) * (σ ^ 6 * t ^ 6) + (543 / 2048 : ℝ) * (σ ^ 8 * t ^ 0) + (-6375 / 1024 : ℝ) * (σ ^ 9 * t ^ 2) + (-75 / 2048 : ℝ) * (σ ^ 12 * t ^ 0)

theorem skewTiltPart4_le (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht1 : 1 ≤ t) :
    skewTiltPart4 σ t ≤ (76377 / 1024 : ℝ) * t ^ 10 := by
  unfold skewTiltPart4
  have hb_0_6 : (-29961 / 2048 : ℝ) * (σ ^ 0 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-29961 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 0 6)
    rw [zero_mul] at this
    exact this
  have hb_1_2 : (-4773 / 128 : ℝ) * (σ ^ 1 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-4773 / 128 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 2)
    rw [zero_mul] at this
    exact this
  have hb_1_10 : (-2475 / 1024 : ℝ) * (σ ^ 1 * t ^ 10) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 1 10)
    rw [zero_mul] at this
    exact this
  have hb_2_6 : (-6399 / 256 : ℝ) * (σ ^ 2 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-6399 / 256 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 2 6)
    rw [zero_mul] at this
    exact this
  have hb_3_2 : (24933 / 512 : ℝ) * (σ ^ 3 * t ^ 2) ≤ (24933 / 512 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 3 2 (by norm_num)) (show (0 : ℝ) ≤ (24933 / 512 : ℝ) by norm_num)
  have hb_4_0 : (1269 / 128 : ℝ) * (σ ^ 4 * t ^ 0) ≤ (1269 / 128 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 0 (by norm_num)) (show (0 : ℝ) ≤ (1269 / 128 : ℝ) by norm_num)
  have hb_4_8 : (2475 / 2048 : ℝ) * (σ ^ 4 * t ^ 8) ≤ (2475 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 4 8 (by norm_num)) (show (0 : ℝ) ≤ (2475 / 2048 : ℝ) by norm_num)
  have hb_5_6 : (7425 / 512 : ℝ) * (σ ^ 5 * t ^ 6) ≤ (7425 / 512 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 5 6 (by norm_num)) (show (0 : ℝ) ≤ (7425 / 512 : ℝ) by norm_num)
  have hb_6_6 : (-2475 / 512 : ℝ) * (σ ^ 6 * t ^ 6) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-2475 / 512 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 6 6)
    rw [zero_mul] at this
    exact this
  have hb_8_0 : (543 / 2048 : ℝ) * (σ ^ 8 * t ^ 0) ≤ (543 / 2048 : ℝ) * t ^ 10 :=
    mul_le_mul_of_nonneg_left (skewMono_le σ t h0 h1 ht1 8 0 (by norm_num)) (show (0 : ℝ) ≤ (543 / 2048 : ℝ) by norm_num)
  have hb_9_2 : (-6375 / 1024 : ℝ) * (σ ^ 9 * t ^ 2) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-6375 / 1024 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 9 2)
    rw [zero_mul] at this
    exact this
  have hb_12_0 : (-75 / 2048 : ℝ) * (σ ^ 12 * t ^ 0) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right (show (-75 / 2048 : ℝ) ≤ (0 : ℝ) by norm_num) (skewMono_nonneg σ t h0 ht1 12 0)
    rw [zero_mul] at this
    exact this
  linarith

theorem skewTiltCofactor_split (σ t : ℝ) :
    skewTiltCofactor σ t = (-(675 / 2048 : ℝ)) * t ^ 12 + skewTiltPart1 σ t + skewTiltPart2 σ t + skewTiltPart3 σ t + skewTiltPart4 σ t := by
  unfold skewTiltCofactor skewTiltPart1 skewTiltPart2 skewTiltPart3 skewTiltPart4
  ring

/-- On the strip and above height 35 the cofactor is negative. -/
theorem skewTiltCofactor_neg (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (35 : ℝ) ≤ t) : skewTiltCofactor σ t < 0 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  rw [skewTiltCofactor_split]
  have p1 := skewTiltPart1_le σ t h0 h1 ht1
  have p2 := skewTiltPart2_le σ t h0 h1 ht1
  have p3 := skewTiltPart3_le σ t h0 h1 ht1
  have p4 := skewTiltPart4_le σ t h0 h1 ht1
  have hbig : (804477 / 2048 : ℝ) * t ^ 10 < (675 / 2048) * t ^ 12 := by
    have : t ^ 12 = t ^ 10 * t ^ 2 := by ring
    rw [this]
    have h10 : 0 < t ^ 10 := pow_pos (by linarith) 10
    have hsq : (35 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  linarith

/-- Elementary tilt detection: above height `35` the real part of the horizon logarithm coefficient
vanishes exactly on the critical line. -/
theorem skewLogCoeff_re_eq_zero_iff (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (ht : (35 : ℝ) ≤ t) :
    (skewLogCoeff ((σ : ℂ) - 2 + (t : ℂ) * Complex.I)).re = 0 ↔ σ = 1 / 2 := by
  have hs : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hs3 : ((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have key := skewLogCoeff_re_tilt σ t hs hs3
  have hpos : 0 < Complex.normSq (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) * (((σ : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) :=
    Complex.normSq_pos.mpr (mul_ne_zero hs hs3)
  have hneg := skewTiltCofactor_neg σ t h0 h1 ht
  constructor
  · intro hre
    rw [hre] at key
    have : (2 * σ - 1) * skewTiltCofactor σ t = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hneg.ne
  · intro hσ
    subst hσ
    have : 2 * (skewLogCoeff (((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I)).re * Complex.normSq ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) * ((((1 / 2 : ℝ) : ℂ) - 2 + (t : ℂ) * Complex.I) + 3)) = 0 := by
      rw [key]; ring
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hpos.ne'

end RHTower.D4BMScalarStream
