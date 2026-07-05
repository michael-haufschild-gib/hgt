/-
The finite Hardy identity for the certificate carrier on the critical line.

On the line `s = ½+iτ` one has `1 − s = conj s`, so the χ-factor is unimodular (`‖zetaChi s‖ = 1`) and
the carrier reflects onto its own conjugate: `zetaChi·conj(gN) = gN` (the finite analog of `ξ`'s
reality). Writing `D = dirichletPoly N(½+iτ)`, the carrier is `gN = D + zetaChi·conj D`, i.e. a
unimodular phase `w` (a square root of `zetaChi`) times a REAL amplitude:
`conj(w)·gN = 2·Re(conj(w)·D) =: H_N(τ)`, the finite Hardy carrier. Hence `‖gN(½+iτ)‖ = |H_N(τ)|`, so
the on-line zeros of `gN` are exactly the sign changes of the real function `H_N` — the object the
sign-based counting gates consume, and the honest correction to the impossible on-line modulus floor
(the two AFE halves have equal modulus on the line, `‖zetaChi·conj D‖ = ‖D‖`, so no single term
dominates).
-/
import GaloisForLFunctions.RHTower.ZetaCarrier
open Complex
namespace RHTower

noncomputable def linePt (τ : ℝ) : ℂ := ((1/2 : ℝ) : ℂ) + (τ : ℂ) * I

theorem conj_linePt (τ : ℝ) : (starRingEnd ℂ) (linePt τ) = 1 - linePt τ := by
  unfold linePt; apply Complex.ext
  · simp; norm_num
  · simp

theorem linePt_re (τ : ℝ) : (linePt τ).re = 1/2 := by unfold linePt; simp
theorem linePt_re_pos (τ : ℝ) : 0 < (linePt τ).re := by rw [linePt_re]; norm_num
theorem linePt_re_lt_one (τ : ℝ) : (linePt τ).re < 1 := by rw [linePt_re]; norm_num

theorem norm_zetaChi_line (τ : ℝ) : ‖zetaChi (linePt τ)‖ = 1 := by
  have hstrip : zetaChi (linePt τ) * zetaChi (1 - linePt τ) = 1 :=
    zetaChi_mul_one_sub_of_mem_strip (linePt_re_pos τ) (linePt_re_lt_one τ)
  rw [← conj_linePt, zetaChi_conj, Complex.mul_conj] at hstrip
  have hns : normSq (zetaChi (linePt τ)) = 1 := by exact_mod_cast hstrip
  have h1 : ‖zetaChi (linePt τ)‖ ^ 2 = 1 := (Complex.normSq_eq_norm_sq _).symm.trans hns
  rw [← Real.sqrt_one, ← h1, Real.sqrt_sq (norm_nonneg _)]

theorem zetaChi_line_ne_zero (τ : ℝ) : zetaChi (linePt τ) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_zetaChi_line]; norm_num

theorem gN_line_conjForm (N : ℕ) (τ : ℝ) :
    gN N (linePt τ)
      = dirichletPoly N (linePt τ)
        + zetaChi (linePt τ) * (starRingEnd ℂ) (dirichletPoly N (linePt τ)) := by
  unfold gN chiSymmetrize; rw [← conj_linePt, dirichletPoly_conj]

/-- **The finite functional equation of the carrier on the line.** `gN` satisfies
`zetaChi·conj(gN) = gN` on the critical line: Schwarz reflection `conj(gN s) = gN(1−s)` combined with
the carrier FE `gN(1−s) = zetaChi(1−s)·gN s` and the χ-identity `zetaChi s·zetaChi(1−s) = 1`. This is
the finite analog of `ξ`'s reality on the line, and it forces `gN(½+iτ)` onto the ray at angle
`½·arg(zetaChi)`. -/
theorem zetaChi_mul_conj_gN_line (N : ℕ) (τ : ℝ) :
    zetaChi (linePt τ) * (starRingEnd ℂ) (gN N (linePt τ)) = gN N (linePt τ) := by
  have hconj : (starRingEnd ℂ) (gN N (linePt τ)) = gN N (1 - linePt τ) := by
    rw [← conj_linePt, gN_conj]
  rw [hconj, gN_one_sub (linePt_re_pos τ) (linePt_re_lt_one τ), ← mul_assoc,
    zetaChi_mul_one_sub_of_mem_strip (linePt_re_pos τ) (linePt_re_lt_one τ), one_mul]

/-- The unimodular square-root of the χ-phase: `w = exp(½ log zetaChi)`, so `w² = zetaChi` and
`‖w‖ = 1` on the line. -/
noncomputable def hardyPhase (τ : ℝ) : ℂ := Complex.exp (Complex.log (zetaChi (linePt τ)) / 2)

theorem hardyPhase_sq (τ : ℝ) : hardyPhase τ * hardyPhase τ = zetaChi (linePt τ) := by
  rw [hardyPhase, ← Complex.exp_add,
    show Complex.log (zetaChi (linePt τ)) / 2 + Complex.log (zetaChi (linePt τ)) / 2
      = Complex.log (zetaChi (linePt τ)) by ring,
    Complex.exp_log (zetaChi_line_ne_zero τ)]

theorem norm_hardyPhase (τ : ℝ) : ‖hardyPhase τ‖ = 1 := by
  rw [hardyPhase, Complex.norm_exp]
  have hre : (Complex.log (zetaChi (linePt τ)) / 2).re = 0 := by
    rw [Complex.div_re]
    simp only [Complex.log_re, norm_zetaChi_line, Real.log_one]
    norm_num
  rw [hre, Real.exp_zero]

theorem conj_hardyPhase_mul_self (τ : ℝ) : (starRingEnd ℂ) (hardyPhase τ) * hardyPhase τ = 1 := by
  rw [mul_comm, Complex.mul_conj]
  have hns : normSq (hardyPhase τ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_hardyPhase]; norm_num
  rw [hns]; norm_num

/-- **The finite Hardy carrier** `H_N(τ) := Re(conj(w)·gN(½+iτ))`, the real amplitude whose sign
changes are the on-line zeros of `gN`. -/
noncomputable def hardyCarrier (N : ℕ) (τ : ℝ) : ℝ :=
  ((starRingEnd ℂ) (hardyPhase τ) * gN N (linePt τ)).re

/-- **Reality + amplitude of the carrier on the line.** `conj(w)·gN(½+iτ) = 2·Re(conj(w)·D)`, a real
number: the carrier is a unimodular phase times the real Hardy amplitude `H_N(τ) = 2 Re(conj(w)·D)`. -/
theorem conj_hardyPhase_mul_gN_eq (N : ℕ) (τ : ℝ) :
    (starRingEnd ℂ) (hardyPhase τ) * gN N (linePt τ)
      = ((2 * ((starRingEnd ℂ) (hardyPhase τ) * dirichletPoly N (linePt τ)).re : ℝ) : ℂ) := by
  set w := hardyPhase τ with hw
  set D := dirichletPoly N (linePt τ) with hD
  have hcw : (starRingEnd ℂ) w * w = 1 := conj_hardyPhase_mul_self τ
  have hw2 : w * w = zetaChi (linePt τ) := hardyPhase_sq τ
  have key : (starRingEnd ℂ) w * gN N (linePt τ)
      = ((starRingEnd ℂ) w * D) + (starRingEnd ℂ) ((starRingEnd ℂ) w * D) := by
    rw [gN_line_conjForm, ← hw2]
    rw [map_mul, Complex.conj_conj]
    ring_nf
    linear_combination ((starRingEnd ℂ) D * w) * hcw
  rw [key, Complex.add_conj]

/-- **The carrier modulus is the Hardy amplitude.** `‖gN(½+iτ)‖ = |H_N(τ)|`. In particular the
on-line zeros of `gN` are exactly the sign changes of the real Hardy carrier `H_N`. -/
theorem norm_gN_line_eq_abs_hardyCarrier (N : ℕ) (τ : ℝ) :
    ‖gN N (linePt τ)‖ = |hardyCarrier N τ| := by
  have hconj := conj_hardyPhase_mul_gN_eq N τ
  have hHC : hardyCarrier N τ
      = 2 * ((starRingEnd ℂ) (hardyPhase τ) * dirichletPoly N (linePt τ)).re := by
    rw [hardyCarrier, hconj, Complex.ofReal_re]
  have h1 : ‖gN N (linePt τ)‖ = ‖(starRingEnd ℂ) (hardyPhase τ) * gN N (linePt τ)‖ := by
    rw [norm_mul, Complex.norm_conj, norm_hardyPhase, one_mul]
  rw [h1, hconj, Complex.norm_real, Real.norm_eq_abs, hHC]

theorem gN_line_eq_zero_iff (N : ℕ) (τ : ℝ) :
    gN N (linePt τ) = 0 ↔ hardyCarrier N τ = 0 := by
  rw [← norm_eq_zero, norm_gN_line_eq_abs_hardyCarrier, abs_eq_zero]

end RHTower

