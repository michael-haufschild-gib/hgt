import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Holomorphy of the explicit theta square-rate reader

`XiThetaSquareRateBoundary` computes the reader's exact boundary `L²` energy.  This module supplies
the other half of its Hardy certificate directly: the dimensionless reader and its physical-rate
rescaling are holomorphic on the open right half-plane, including the selected removable node.
No Hardy-membership proposition is introduced.
-/

open Complex Real Set

noncomputable section

namespace RHTower

private lemma sinh_pi_sqrt_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh ((Real.pi : ℂ) * Complex.sqrt z) ≠ 0 := by
  intro hsinh
  let w := (Real.pi : ℂ) * Complex.sqrt z
  have hsin : Complex.sin (w * I) = 0 := by
    rw [Complex.sin_mul_I, show Complex.sinh w = 0 by exact hsinh, zero_mul]
  rcases Complex.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
  have him := congrArg Complex.im hk
  have hwre : w.re = 0 := by
    simp only [mul_im, I_re, I_im, mul_zero, mul_one] at him
    simp at him
    exact him
  have hsqrtRe : (Complex.sqrt z).re = 0 := by
    dsimp [w] at hwre
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hwre
    exact (mul_eq_zero.mp hwre).resolve_left Real.pi_ne_zero
  have hsquare := congrArg Complex.re (complex_sqrt_sq z)
  simp [pow_two, Complex.mul_re, hsqrtRe] at hsquare
  nlinarith [sq_nonneg (Complex.sqrt z).im]

/-- The canonical square-zero quotient is holomorphic on the open right half-plane. -/
theorem thetaSquareBlaschkeSymbol_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ thetaSquareBlaschkeSymbol {z : ℂ | 0 < z.re} := by
  intro z hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hsqrt : DifferentiableAt ℂ Complex.sqrt z :=
    Complex.differentiableAt_sqrt hslit
  have harg : DifferentiableAt ℂ (fun q : ℂ => (Real.pi : ℂ) * Complex.sqrt q) z :=
    (differentiableAt_const (c := (Real.pi : ℂ))).mul hsqrt
  exact (harg.csin.div harg.csinh
    (sinh_pi_sqrt_ne_zero_of_re_pos hz)).differentiableWithinAt

/-- The normalized removable difference quotient selecting a positive square remains holomorphic
on the whole right half-plane, including its selected node. -/
theorem thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (thetaSquareBlaschkeReaderSymbol n) {z : ℂ | 0 < z.re} := by
  let S : Set ℂ := {z : ℂ | 0 < z.re}
  have hopen : IsOpen S := isOpen_lt continuous_const continuous_re
  have hnode : thetaSquare n ∈ S := by
    dsimp [S]
    norm_num [thetaSquare, pow_two, Complex.mul_re]
    omega
  have hsymbol : DifferentiableOn ℂ thetaSquareBlaschkeSymbol S :=
    thetaSquareBlaschkeSymbol_differentiableOn_rightHalfPlane
  have hdslope : DifferentiableOn ℂ
      (dslope thetaSquareBlaschkeSymbol (thetaSquare n)) S :=
    (differentiableOn_dslope (hopen.mem_nhds hnode)).2 hsymbol
  change DifferentiableOn ℂ
    (fun z => (thetaSquareBlaschkeNodeSlope n)⁻¹ *
      dslope thetaSquareBlaschkeSymbol (thetaSquare n) z) S
  exact (differentiableOn_const (c := (thetaSquareBlaschkeNodeSlope n)⁻¹)).mul hdslope

/-- After restoring the physical heat-rate scale, the explicit infinite reader is holomorphic on
the open right half-plane. -/
theorem thetaHeatRateReaderSymbol_differentiableOn_rightHalfPlane {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (thetaHeatRateReaderSymbol n) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / (Real.pi : ℂ)) s := by
    fun_prop
  have hre : 0 < (s / (Real.pi : ℂ)).re := by
    rw [div_re]
    simp only [ofReal_re, ofReal_im, mul_zero, normSq_ofReal]
    have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    simpa [pow_two] using div_pos (mul_pos hs Real.pi_pos) hp2
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hreader :=
    (thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane hn)
      (s / (Real.pi : ℂ)) hre
  have hat : DifferentiableAt ℂ (thetaSquareBlaschkeReaderSymbol n)
      (s / (Real.pi : ℂ)) := hreader.differentiableAt (hopen.mem_nhds hre)
  exact (hat.comp s hdiv).differentiableWithinAt

end RHTower
