import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Fourier decay of an exponential piece

The Fourier integral of a real exponential over a subinterval of one period decays like
`1/(1 + |j|)`:

`‖∫_a^b e^{αx} e^{-2π i j x} dx‖ ≤ 2 e^{|α|} / (1 + |j|)`   for `0 ≤ a ≤ b ≤ 1`.

For `j = 0` this is the trivial length bound; for `j ≠ 0` the antiderivative is explicit and the
denominator `α - 2π i j` has modulus at least `2π|j|`.

Piecewise-exponential amplitudes — the class produced by finitely many products of translates of
`p^{±(1-x)}` — are finite sums of such pieces, so this is the decay estimate their Fourier
coefficients inherit.
-/

open intervalIntegral

namespace GaloisForLFunctions

/-- **Decay of an exponential piece.** -/
theorem norm_intervalIntegral_exp_fourier_le {α a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (j : ℤ) :
    ‖∫ x in a..b, Complex.exp ((α : ℂ) * (x : ℂ)) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ)))‖
      ≤ 2 * Real.exp |α| / (1 + (j.natAbs : ℝ)) := by
  have hexpb : ∀ x : ℝ, a ≤ x → x ≤ b → Real.exp (α * x) ≤ Real.exp |α| := by
    intro x hx hx'
    refine Real.exp_le_exp.mpr ?_
    rcases le_or_gt 0 α with hα | hα
    · have hx1 : x ≤ 1 := le_trans hx' hb
      have : α * x ≤ α * 1 := mul_le_mul_of_nonneg_left hx1 hα
      simpa [abs_of_nonneg hα] using this
    · have hx0 : 0 ≤ x := le_trans ha hx
      have : α * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα.le hx0
      have habs : 0 ≤ |α| := abs_nonneg α
      linarith
  have hmerge : ∀ x : ℝ,
      Complex.exp ((α : ℂ) * (x : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ)))
        = Complex.exp (((α : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ)) * (x : ℂ)) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    ring
  by_cases hj : j = 0
  · -- the length bound
    subst hj
    have hconst : ∀ x ∈ Set.uIoc a b,
        ‖Complex.exp ((α : ℂ) * (x : ℂ)) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((0 : ℤ) : ℂ) * (x : ℂ)))‖
          ≤ Real.exp |α| := by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      rw [hmerge x]
      have hre : (((α : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * ((0 : ℤ) : ℂ)) * (x : ℂ)).re
          = α * x := by
        simp
      rw [Complex.norm_exp, hre]
      exact hexpb x hx.1.le hx.2
    have hlen := intervalIntegral.norm_integral_le_of_norm_le_const hconst
    have hba : |b - a| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hexp0 : (0 : ℝ) ≤ Real.exp |α| := (Real.exp_pos _).le
    simp only [Int.natAbs_zero, Nat.cast_zero, add_zero, div_one]
    calc ‖∫ x in a..b, Complex.exp ((α : ℂ) * (x : ℂ)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((0 : ℤ) : ℂ) * (x : ℂ)))‖
        ≤ Real.exp |α| * |b - a| := hlen
      _ ≤ Real.exp |α| * 1 := by exact mul_le_mul_of_nonneg_left hba hexp0
      _ ≤ 2 * Real.exp |α| := by linarith
  · -- the explicit antiderivative
    have hjabs : 1 ≤ (j.natAbs : ℝ) := by
      have : 1 ≤ j.natAbs := by omega
      exact_mod_cast this
    set c : ℂ := (α : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) with hc
    have hcim : c.im = -(2 * Real.pi * (j : ℝ)) := by
      rw [hc]
      simp
    have hcnorm : 2 * Real.pi * (j.natAbs : ℝ) ≤ ‖c‖ := by
      have habs := Complex.abs_im_le_norm c
      rw [hcim, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
      have hjc : |(j : ℝ)| = (j.natAbs : ℝ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
      rwa [hjc] at habs
    have hcpos : 0 < ‖c‖ := by
      have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      nlinarith
    have hcne : c ≠ 0 := by
      intro h
      rw [h] at hcpos
      simp at hcpos
    rw [intervalIntegral.integral_congr (fun x _ => hmerge x), integral_exp_mul_complex hcne]
    have hnum : ‖Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))‖
        ≤ 2 * Real.exp |α| := by
      have hb' : ‖Complex.exp (c * (b : ℂ))‖ ≤ Real.exp |α| := by
        rw [Complex.norm_exp]
        have hre : (c * (b : ℂ)).re = α * b := by
          rw [hc]; simp
        rw [hre]
        exact hexpb b hab le_rfl
      have ha' : ‖Complex.exp (c * (a : ℂ))‖ ≤ Real.exp |α| := by
        rw [Complex.norm_exp]
        have hre : (c * (a : ℂ)).re = α * a := by
          rw [hc]; simp
        rw [hre]
        exact hexpb a le_rfl hab
      calc ‖Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))‖
          ≤ ‖Complex.exp (c * (b : ℂ))‖ + ‖Complex.exp (c * (a : ℂ))‖ := norm_sub_le _ _
        _ ≤ Real.exp |α| + Real.exp |α| := add_le_add hb' ha'
        _ = 2 * Real.exp |α| := by ring
    rw [norm_div]
    rw [div_le_div_iff₀ hcpos (by positivity)]
    have hexp0 : (0 : ℝ) < Real.exp |α| := Real.exp_pos _
    have hstep : (1 + (j.natAbs : ℝ)) ≤ 2 * Real.pi * (j.natAbs : ℝ) := by
      nlinarith [Real.two_le_pi, hjabs]
    nlinarith [hnum, hcnorm, hexp0, hstep, hcpos]

end GaloisForLFunctions
