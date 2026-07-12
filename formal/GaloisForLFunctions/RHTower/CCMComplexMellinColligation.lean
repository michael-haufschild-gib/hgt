import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect

/-!
# Complex CCM polar--prime Mellin colligation

The real-ray polar--prime identity extends to the complete right half-plane.  The continuous
polar density has the two elementary Laplace coordinates `1 / s` and `1 / (s + 1)`, while the
resolved von Mangoldt channel is the Euler-region logarithmic derivative of zeta.  Their signed
defect therefore gives an exact complex Cauchy colligation, entrywise on every finite packet of
right-half-plane nodes.

No zero-location hypothesis or positivity assumption enters this module.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open Finset MeasureTheory ArithmeticFunction Complex Matrix Set Filter

noncomputable section

namespace RHTower

/-- The continuous polar half-line channel on the complex right half-plane. -/
def continuousPolarLaplaceChannelComplex (s : ℂ) : ℂ :=
  ∫ h : ℝ in Ioi 0,
    Complex.exp (-(s + 1 / 2) * (h : ℂ)) *
      (2 * Real.cosh (h / 2) : ℝ)

/-- The complex polar channel splits exactly into its two elementary Cauchy coordinates. -/
theorem continuousPolarLaplaceChannelComplex_eq {s : ℂ} (hs : 0 < s.re) :
    continuousPolarLaplaceChannelComplex s = 1 / s + 1 / (s + 1) := by
  rw [continuousPolarLaplaceChannelComplex]
  have hs0 : (-s).re < 0 := by simp; linarith
  have hs1 : (-(s + 1)).re < 0 := by simp; linarith
  have hfun : (fun h : ℝ =>
      Complex.exp (-(s + 1 / 2) * (h : ℂ)) *
        (2 * Real.cosh (h / 2) : ℝ)) =
      fun h : ℝ => Complex.exp ((-s) * h) + Complex.exp (-(s + 1) * h) := by
    funext h
    rw [Real.cosh_eq]
    push_cast
    ring_nf
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> ring
  rw [hfun, integral_add]
  · rw [integral_exp_mul_complex_Ioi hs0 0,
      integral_exp_mul_complex_Ioi hs1 0]
    norm_num
    rw [show (-1 : ℂ) + -s = -(s + 1) by ring, div_neg]
    ring
  · exact integrableOn_exp_mul_complex_Ioi hs0 0
  · exact integrableOn_exp_mul_complex_Ioi hs1 0

/-- The resolved von Mangoldt prime-power channel at a complex right-half-plane coordinate. -/
def vonMangoldtPrimeLaplaceChannelComplex (s : ℂ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 1)

/-- The complex signed critical Mellin-defect channel. -/
def criticalMellinDefectLaplaceChannelComplex (s : ℂ) : ℂ :=
  continuousPolarLaplaceChannelComplex s - vonMangoldtPrimeLaplaceChannelComplex s

/-- The complex prime channel is the Euler-region negative logarithmic derivative of zeta. -/
theorem vonMangoldtPrimeLaplaceChannelComplex_eq_logDeriv
    {s : ℂ} (hs : 0 < s.re) :
    vonMangoldtPrimeLaplaceChannelComplex s =
      -deriv riemannZeta (s + 1) / riemannZeta (s + 1) := by
  rw [vonMangoldtPrimeLaplaceChannelComplex]
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
    simpa using hs)

/-- **Complex polar--prime critical Mellin colligation.**  On the whole right half-plane, the
universal Cauchy coordinate is the resolved prime channel minus the shifted polar coordinate plus
the signed critical Mellin defect. -/
theorem cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex
    {s : ℂ} (hs : 0 < s.re) :
    1 / s = vonMangoldtPrimeLaplaceChannelComplex s - 1 / (s + 1) +
      criticalMellinDefectLaplaceChannelComplex s := by
  rw [criticalMellinDefectLaplaceChannelComplex,
    continuousPolarLaplaceChannelComplex_eq hs]
  ring

/-- The universal Cauchy Gram on a finite packet of complex right-half-plane nodes. -/
def cauchyRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => 1 / (w i + star (w j))

/-- The resolved von Mangoldt Gram on the same complex packet. -/
def vonMangoldtPrimeRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => vonMangoldtPrimeLaplaceChannelComplex (w i + star (w j))

/-- The shifted elementary polar Gram on the same complex packet. -/
def shiftedPolarRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => 1 / (w i + star (w j) + 1)

/-- The critical Mellin-defect matrix on the same complex packet. -/
def criticalMellinDefectRightHalfPlaneGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => criticalMellinDefectLaplaceChannelComplex (w i + star (w j))

/-- **Finite complex source incidence.**  Every finite right-half-plane Cauchy Gram is exactly the
resolved prime Gram minus the shifted polar Gram plus the critical Mellin-defect matrix. -/
theorem cauchyRightHalfPlaneGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    cauchyRightHalfPlaneGram w = vonMangoldtPrimeRightHalfPlaneGram w -
      shiftedPolarRightHalfPlaneGram w + criticalMellinDefectRightHalfPlaneGram w := by
  ext i j
  exact cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect_complex (by
    change 0 < (w i + conj (w j)).re
    rw [Complex.add_re, Complex.conj_re]
    linarith [hw i, hw j])

end RHTower
