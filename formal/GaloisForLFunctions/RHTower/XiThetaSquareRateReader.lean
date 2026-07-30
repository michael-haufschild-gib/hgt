import GaloisForLFunctions.RHTower.ThetaBlaschkeProbe
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# An explicit infinite square-rate reader symbol

The compactified heat-node obstruction forces an exact infinite reader out of the holomorphic
moment-symbol category at `x = 0`. In the uncompactified rate variable, the square spectrum admits
the canonical quotient `B(z) = sin (pi * sqrt z) / sinh (pi * sqrt z)`.

Its positive zeros are exactly the square nodes. Normalizing the removable difference quotient at
the selected zero gives a single explicit symbol interpolating `1` at that square and `0` at every
other square. This constructs the infinite interpolation symbol without a reader-existence
proposition. Hardy-space membership and the source-side Paley-Wiener representative remain separate
analytic steps.
-/

open Complex Set

noncomputable section

namespace RHTower

lemma sqrt_thetaSquare (n : ℕ) : Complex.sqrt (thetaSquare n) = (n : ℂ) := by
  rw [show thetaSquare n = (((n : ℝ) ^ 2 : ℝ) : ℂ) by simp [thetaSquare]]
  rw [Complex.sqrt_of_nonneg]
  · norm_cast
    rw [Nat.cast_pow]
    exact Real.sqrt_sq (Nat.cast_nonneg n)
  · rw [Complex.nonneg_iff]
    simp [pow_two, Complex.mul_re]
    positivity

lemma thetaSquare_mem_slitPlane {n : ℕ} (hn : 1 ≤ n) :
    thetaSquare n ∈ Complex.slitPlane := by
  rw [show thetaSquare n = (((n : ℝ) ^ 2 : ℝ) : ℂ) by simp [thetaSquare]]
  rw [ofReal_mem_slitPlane]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  exact sq_pos_of_pos hnR

/-- The canonical square-zero Blaschke symbol in the scaled rate variable. -/
def thetaSquareBlaschkeSymbol (z : ℂ) : ℂ :=
  Complex.sin ((Real.pi : ℂ) * Complex.sqrt z) /
    Complex.sinh ((Real.pi : ℂ) * Complex.sqrt z)

lemma thetaSquareBlaschkeSymbol_zero (n : ℕ) :
    thetaSquareBlaschkeSymbol (thetaSquare n) = 0 := by
  rw [thetaSquareBlaschkeSymbol, sqrt_thetaSquare]
  rw [show (Real.pi : ℂ) * (n : ℂ) = (n : ℂ) * Real.pi by ring]
  rw [Complex.sin_nat_mul_pi, zero_div]

lemma thetaSquareBlaschkeDen_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    Complex.sinh ((Real.pi : ℂ) * Complex.sqrt (thetaSquare n)) ≠ 0 := by
  rw [sqrt_thetaSquare]
  rw [show (Real.pi : ℂ) * (n : ℂ) = (((Real.pi * n : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_sinh, Complex.ofReal_ne_zero]
  rw [Real.sinh_ne_zero]
  exact mul_ne_zero Real.pi_ne_zero (by positivity)

lemma thetaSquareBlaschkeNodeDen_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    Complex.sinh ((Real.pi : ℂ) * (n : ℂ)) ≠ 0 := by
  rw [show (Real.pi : ℂ) * (n : ℂ) = (((Real.pi * n : ℝ)) : ℂ) by push_cast; ring]
  rw [← Complex.ofReal_sinh, Complex.ofReal_ne_zero, Real.sinh_ne_zero]
  exact mul_ne_zero Real.pi_ne_zero (by positivity)

/-- The explicit derivative of the square-zero symbol at the selected positive node. -/
def thetaSquareBlaschkeNodeSlope (n : ℕ) : ℂ :=
  (Complex.cos ((Real.pi : ℂ) * (n : ℂ)) *
      ((Real.pi : ℂ) * (thetaSquare n ^ ((-1 : ℂ) / 2) / 2))) /
    Complex.sinh ((Real.pi : ℂ) * (n : ℂ))

lemma hasDerivAt_thetaSquareBlaschkeSymbol {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt thetaSquareBlaschkeSymbol (thetaSquareBlaschkeNodeSlope n) (thetaSquare n) := by
  have hsqrt := Complex.hasDerivAt_sqrt (thetaSquare_mem_slitPlane hn)
  have harg : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * Complex.sqrt z)
      ((Real.pi : ℂ) * (thetaSquare n ^ ((-1 : ℂ) / 2) / 2)) (thetaSquare n) :=
    hsqrt.const_mul (Real.pi : ℂ)
  have hquot := harg.csin.div harg.csinh (thetaSquareBlaschkeDen_ne_zero hn)
  convert! hquot using 1
  simp only [thetaSquareBlaschkeNodeSlope, sqrt_thetaSquare]
  rw [show (Real.pi : ℂ) * (n : ℂ) = (n : ℂ) * Real.pi by ring]
  rw [Complex.sin_nat_mul_pi, zero_mul, sub_zero]
  rw [show (n : ℂ) * Real.pi = (Real.pi : ℂ) * n by ring]
  field_simp [thetaSquareBlaschkeNodeDen_ne_zero hn]

lemma thetaSquareBlaschkeNodeSlope_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    thetaSquareBlaschkeNodeSlope n ≠ 0 := by
  unfold thetaSquareBlaschkeNodeSlope
  apply div_ne_zero
  · apply mul_ne_zero
    · rw [show (Real.pi : ℂ) * (n : ℂ) = (((Real.pi * n : ℝ)) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_cos, Complex.ofReal_ne_zero]
      rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring, Real.cos_nat_mul_pi]
      exact pow_ne_zero n (by norm_num)
    · apply mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      apply div_ne_zero
      · intro h
        rw [Complex.cpow_eq_zero_iff] at h
        have hsq : thetaSquare n ≠ 0 := by
          unfold thetaSquare
          exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega))
        exact hsq h.1
      · norm_num
  · rw [show (Real.pi : ℂ) * (n : ℂ) = (((Real.pi * n : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_sinh, Complex.ofReal_ne_zero, Real.sinh_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero (by positivity)

/-- The removable-difference-quotient normalization selecting the `n`-th square node. -/
def thetaSquareBlaschkeReaderSymbol (n : ℕ) (z : ℂ) : ℂ :=
  (thetaSquareBlaschkeNodeSlope n)⁻¹ *
    dslope thetaSquareBlaschkeSymbol (thetaSquare n) z

lemma thetaSquare_ne_of_ne {n m : ℕ} (hnm : n ≠ m) : thetaSquare n ≠ thetaSquare m := by
  intro h
  have hreal : (n : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
    have hncast : thetaSquare n = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by simp [thetaSquare]
    have hmcast : thetaSquare m = (((m : ℝ) ^ 2 : ℝ) : ℂ) := by simp [thetaSquare]
    rw [hncast, hmcast] at h
    exact_mod_cast h
  have heq : (n : ℝ) = (m : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    nlinarith
  exact hnm (by exact_mod_cast heq)

/-- The infinite reader symbol is normalized to one at its selected square. -/
theorem thetaSquareBlaschkeReaderSymbol_self {n : ℕ} (hn : 1 ≤ n) :
    thetaSquareBlaschkeReaderSymbol n (thetaSquare n) = 1 := by
  rw [thetaSquareBlaschkeReaderSymbol, dslope_same,
    (hasDerivAt_thetaSquareBlaschkeSymbol hn).deriv,
    inv_mul_cancel₀ (thetaSquareBlaschkeNodeSlope_ne_zero hn)]

/-- The same symbol annihilates every other square, with no finite cutoff. -/
theorem thetaSquareBlaschkeReaderSymbol_other {n m : ℕ} (hmn : m ≠ n) :
    thetaSquareBlaschkeReaderSymbol n (thetaSquare m) = 0 := by
  rw [thetaSquareBlaschkeReaderSymbol, dslope_of_ne _ (thetaSquare_ne_of_ne hmn),
    slope_def_field, thetaSquareBlaschkeSymbol_zero, thetaSquareBlaschkeSymbol_zero,
    sub_zero, zero_div, mul_zero]

/-- The physical heat rate appearing after logarithmic source reparametrization. -/
def thetaHeatRate (m : ℕ) : ℝ := Real.pi * (m : ℝ) ^ 2

/-- The square reader rescaled from the dimensionless variable to the physical heat rate. -/
def thetaHeatRateReaderSymbol (n : ℕ) (s : ℂ) : ℂ :=
  thetaSquareBlaschkeReaderSymbol n (s / (Real.pi : ℂ))

private lemma thetaHeatRate_div_pi (m : ℕ) :
    (thetaHeatRate m : ℂ) / (Real.pi : ℂ) = thetaSquare m := by
  rw [thetaHeatRate]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  simp [thetaSquare]

/-- The physical-rate symbol is one at the selected heat rate. -/
theorem thetaHeatRateReaderSymbol_self {n : ℕ} (hn : 1 ≤ n) :
    thetaHeatRateReaderSymbol n (thetaHeatRate n) = 1 := by
  rw [thetaHeatRateReaderSymbol, thetaHeatRate_div_pi,
    thetaSquareBlaschkeReaderSymbol_self hn]

/-- The physical-rate symbol annihilates every other theta heat rate. -/
theorem thetaHeatRateReaderSymbol_other {n m : ℕ} (hmn : m ≠ n) :
    thetaHeatRateReaderSymbol n (thetaHeatRate m) = 0 := by
  rw [thetaHeatRateReaderSymbol, thetaHeatRate_div_pi,
    thetaSquareBlaschkeReaderSymbol_other hmn]

end RHTower
