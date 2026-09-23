/-
# Slice obstruction instances along `arg b` at modulus ≈ 3 — the P1 side

Six exact-rational obstructed parameters sweeping `arg b` from ≈ 155.94° to 180°, each an
instance of the `s`-parameterized P1 Cassini region (`U0CurveSectors.obstructed_of_s`) with
`b = (1−s²)/4` for a Gaussian-RATIONAL `s` — so every condition is pure rational arithmetic.
Data from `computations/rho_curve_recon/grid_design.py`.
-/
import GaloisForLFunctions.U0.U0CurveSectors

open Complex Set Bottcher

namespace U0DichotomySlice

/-- Rational-arithmetic form of the P1 Cassini condition. -/
theorem obstructed_of_s_sq {s : ℂ}
    (h : ((s - 3).re ^ (2 : ℕ) + (s - 3).im ^ (2 : ℕ)) * ((s + 1).re ^ (2 : ℕ) + (s + 1).im ^ (2 : ℕ)) ≤ 16) :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia ((1 - s ^ (2 : ℕ)) / 4) := by
  refine U0CurveSectors.obstructed_of_s ?_
  have h1 : ‖s - 3‖ ^ (2 : ℕ) = (s - 3).re ^ (2 : ℕ) + (s - 3).im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : ‖s + 1‖ ^ (2 : ℕ) = (s + 1).re ^ (2 : ℕ) + (s + 1).im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h' : (‖s - 3‖ * ‖s + 1‖) ^ (2 : ℕ) ≤ 16 := by
    rw [mul_pow, h1, h2]; exact h
  nlinarith [mul_nonneg (norm_nonneg (s - 3)) (norm_nonneg (s + 1)),
    sq_nonneg (‖s - 3‖ * ‖s + 1‖ - 4)]

/-- Obstructed slice point: `arg b ≈ 155.94°`, `‖b‖² ≈ 8.7070` — P1 pattern, exact rationals. -/
theorem slice_obstructed_156 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-(2759/1024), (77/64)⟩ : ℂ) := by
  have hb : ((⟨-(2759/1024), (77/64)⟩ : ℂ)) = (1 - (⟨(7/2), -(11/16)⟩ : ℂ) ^ (2 : ℕ)) / 4 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h4, Complex.ext_iff]
    constructor
    · norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re]
    · norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im]
  rw [hb]
  exact obstructed_of_s_sq (by
    norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im])

/-- Obstructed slice point: `arg b ≈ 160.59°`, `‖b‖² ≈ 9.0908` — P1 pattern, exact rationals. -/
theorem slice_obstructed_161 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-(91/32), (513/512)⟩ : ℂ) := by
  have hb : ((⟨-(91/32), (513/512)⟩ : ℂ)) = (1 - (⟨(57/16), -(9/16)⟩ : ℂ) ^ (2 : ℕ)) / 4 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h4, Complex.ext_iff]
    constructor
    · norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re]
    · norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im]
  rw [hb]
  exact obstructed_of_s_sq (by
    norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im])

/-- Obstructed slice point: `arg b ≈ 164.83°`, `‖b‖² ≈ 8.8729` — P1 pattern, exact rationals. -/
theorem slice_obstructed_165 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-(23/8), (399/512)⟩ : ℂ) := by
  have hb : ((⟨-(23/8), (399/512)⟩ : ℂ)) = (1 - (⟨(57/16), -(7/16)⟩ : ℂ) ^ (2 : ℕ)) / 4 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h4, Complex.ext_iff]
    constructor
    · norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re]
    · norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im]
  rw [hb]
  exact obstructed_of_s_sq (by
    norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im])

/-- Obstructed slice point: `arg b ≈ 169.13°`, `‖b‖² ≈ 8.7108` — P1 pattern, exact rationals. -/
theorem slice_obstructed_169 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-(371/128), (285/512)⟩ : ℂ) := by
  have hb : ((⟨-(371/128), (285/512)⟩ : ℂ)) = (1 - (⟨(57/16), -(5/16)⟩ : ℂ) ^ (2 : ℕ)) / 4 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h4, Complex.ext_iff]
    constructor
    · norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re]
    · norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im]
  rw [hb]
  exact obstructed_of_s_sq (by
    norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im])

/-- Obstructed slice point: `arg b ≈ 175.73°`, `‖b‖² ≈ 9.2398` — P1 pattern, exact rationals. -/
theorem slice_obstructed_176 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-(97/32), (29/128)⟩ : ℂ) := by
  have hb : ((⟨-(97/32), (29/128)⟩ : ℂ)) = (1 - (⟨(29/8), -(1/8)⟩ : ℂ) ^ (2 : ℕ)) / 4 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h4, Complex.ext_iff]
    constructor
    · norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re]
    · norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im]
  rw [hb]
  exact obstructed_of_s_sq (by
    norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im])

/-- Obstructed slice point: `arg b ≈ 180.00°`, `‖b‖² ≈ 9.2122` — P1 pattern, exact rationals. -/
theorem slice_obstructed_180 :
    ∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia (⟨-(777/256), 0⟩ : ℂ) := by
  have hb : ((⟨-(777/256), 0⟩ : ℂ)) = (1 - (⟨(29/8), 0⟩ : ℂ) ^ (2 : ℕ)) / 4 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    rw [eq_div_iff h4, Complex.ext_iff]
    constructor
    · norm_num [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re]
    · norm_num [pow_two, Complex.mul_im, Complex.sub_im, Complex.one_im]
  rw [hb]
  exact obstructed_of_s_sq (by
    norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im])

end U0DichotomySlice
