import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The 3-4-1 inequality and the pole bound for ζ

The quantitative Mertens product inequality specialized to ζ:

`1 ≤ ‖ζ(1+x)³ · ζ(1+x+iy)⁴ · ζ(1+x+2iy)‖`  (x > 0),

and the elementary pole estimate `‖ζ(1+x)‖ ≤ 1/x + 2` from the
truncated representation at `N = 1` — the two ingredients of the
de la Vallée Poussin zero-free region that live at `Re > 1`.
-/

noncomputable section

namespace RHTower

open Set

/-- **The 3-4-1 product inequality for ζ**. -/
theorem norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x) ^ 3
        * riemannZeta (1 + x + Complex.I * y) ^ 4
        * riemannZeta (1 + x + 2 * Complex.I * y)‖ := by
  have h := DirichletCharacter.norm_LSeries_product_ge_one
    (1 : DirichletCharacter ℂ 1) hx y
  rw [one_pow] at h
  simp only [DirichletCharacter.modOne_eq_one] at h
  have hre1 : (1 < ((1 : ℂ) + x).re) := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hre2 : (1 < ((1 : ℂ) + x + Complex.I * y).re) := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    linarith
  have hre3 : (1 < ((1 : ℂ) + x + 2 * Complex.I * y).re) := by
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    linarith
  rw [LSeries_one_eq_riemannZeta hre1, LSeries_one_eq_riemannZeta hre2,
    LSeries_one_eq_riemannZeta hre3] at h
  exact h

/-- **Pole bound**: `‖ζ(1+x)‖ ≤ 1/x + 2` for `x > 0`. -/
theorem abs_riemannZeta_one_add_le {x : ℝ} (hx0 : 0 < x) :
    ‖riemannZeta (1 + x)‖ ≤ 1 / x + 2 := by
  have hre : ((1 : ℂ) + x).re = 1 + x := by
    simp [Complex.add_re]
  have hs0 : 0 < ((1 : ℂ) + x).re := by rw [hre]; linarith
  have hs1 : (1 : ℂ) + x ≠ 1 := by
    intro h
    have h2 := congrArg Complex.re h
    rw [hre] at h2
    simp at h2
    linarith
  rw [zeta_eq_truncated_of_re_pos le_rfl hs0 hs1, zetaTruncated]
  -- the three pieces at `N = 1`
  have hsum : (∑ n ∈ Finset.Icc (1 : ℕ) 1, (n : ℂ) ^ (-((1 : ℂ) + x)))
      = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    simp [Complex.one_cpow]
  have hNpow : ((1 : ℕ) : ℂ) ^ ((1 : ℂ) - ((1 : ℂ) + x)) = 1 := by
    simp [Complex.one_cpow]
  have hden : ((1 : ℂ) + x) - 1 = (x : ℂ) := by ring
  rw [hsum, hNpow, hden]
  have htail := norm_zetaSawtoothTail_le (s := (1 : ℂ) + x) hs0 le_rfl
  rw [hre] at htail
  have htail2 : ‖zetaSawtoothTail 1 ((1 : ℂ) + x)‖ ≤ 1 / (1 + x) := by
    refine le_trans htail ?_
    rw [Nat.cast_one, Real.one_rpow]
  have hnorms : ‖(1 : ℂ) + x‖ = 1 + x := by
    rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  calc ‖1 + 1 / (x : ℂ) - ((1 : ℂ) + x)
        * zetaSawtoothTail 1 ((1 : ℂ) + x)‖
      ≤ ‖1 + 1 / (x : ℂ)‖ + ‖((1 : ℂ) + x)
          * zetaSawtoothTail 1 ((1 : ℂ) + x)‖ := norm_sub_le _ _
    _ ≤ (1 + 1 / x) + 1 := by
        have h1 : ‖1 + 1 / (x : ℂ)‖ ≤ 1 + 1 / x := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_one, norm_div, norm_one]
          rw [show ((x : ℂ)) = ((x : ℝ) : ℂ) from rfl, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hx0]
        have h2 : ‖((1 : ℂ) + x) * zetaSawtoothTail 1 ((1 : ℂ) + x)‖
            ≤ 1 := by
          rw [norm_mul, hnorms]
          calc (1 + x) * ‖zetaSawtoothTail 1 ((1 : ℂ) + x)‖
              ≤ (1 + x) * (1 / (1 + x)) :=
                mul_le_mul_of_nonneg_left htail2 (by linarith)
            _ = 1 := by field_simp
        linarith
    _ = 1 / x + 2 := by ring

end RHTower
