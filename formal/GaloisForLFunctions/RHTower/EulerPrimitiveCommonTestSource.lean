import GaloisForLFunctions.RHTower.CCMComplexMellinColligation
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyNonexpansive
import GaloisForLFunctions.RHTower.VonMangoldtGammaDepthOneCauchy

/-!
# Primitive Euler common-test source

This module constructs a literal source object for Route R before divisor
scalarization.  Its coordinates are pairs `(n,t)`: `n` retains the complete
prime-power label and `t > 0` is one common Hardy/Laplace test coordinate.
The amplitude is the unsquared critical primitive mass `Λ(n)/n`; it is not a
post-divisor zero coordinate.

The label-time pairing is proved absolutely summable and identified exactly
with the tensor product of the resolved von-Mangoldt Gram and the universal
right-half-plane Hardy Gram.  Hence every finite spectral packet is positive
semidefinite.  This supplies the critical tail object required for the
singular head/tail horizon construction; it does not assert the unresolved
Gamma/polar-to-Ward comparison.
-/

open Complex MeasureTheory Set Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Literal label-time common-test coordinate of the critical primitive
Euler current.  The natural-number coordinate retains the prime-power label;
the half-line coordinate is the common Hardy test. -/
def eulerPrimitiveCommonTestFeature
    (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  finiteVonMangoldtDepthOneAmplitude n *
    ((n : ℂ) ^ w)⁻¹ *
    Complex.exp (-w * (t : ℂ))

theorem integral_eulerPrimitiveCommonTestFeature
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0,
        eulerPrimitiveCommonTestFeature w n t *
          star (eulerPrimitiveCommonTestFeature v n t)) =
      (finiteVonMangoldtDepthOneAmplitude n *
          ((n : ℂ) ^ w)⁻¹) *
        star (finiteVonMangoldtDepthOneAmplitude n *
          ((n : ℂ) ^ v)⁻¹) *
        (1 / (w + star v)) := by
  have hrate : 0 < (w + star v).re := by
    change 0 < w.re + v.re
    linarith
  have hfun :
      (fun t : ℝ =>
        eulerPrimitiveCommonTestFeature w n t *
          star (eulerPrimitiveCommonTestFeature v n t)) =
      fun t : ℝ =>
        ((finiteVonMangoldtDepthOneAmplitude n *
            ((n : ℂ) ^ w)⁻¹) *
          star (finiteVonMangoldtDepthOneAmplitude n *
            ((n : ℂ) ^ v)⁻¹)) *
          Complex.exp (-(w + star v) * (t : ℂ)) := by
    funext t
    have hstarExp :
        star (Complex.exp (-v * (t : ℂ))) =
          Complex.exp (-(star v) * (t : ℂ)) := by
      change (starRingEnd ℂ) (Complex.exp (-v * (t : ℂ))) =
        Complex.exp (-(starRingEnd ℂ) v * (t : ℂ))
      rw [← Complex.exp_conj]
      congr 1
      simp
    have hstarMul :
        star
          ((finiteVonMangoldtDepthOneAmplitude n *
            ((n : ℂ) ^ v)⁻¹) * Complex.exp (-v * (t : ℂ))) =
        star
            (finiteVonMangoldtDepthOneAmplitude n *
              ((n : ℂ) ^ v)⁻¹) *
          star (Complex.exp (-v * (t : ℂ))) := by
      exact map_mul (starRingEnd ℂ) _ _
    change
      ((finiteVonMangoldtDepthOneAmplitude n *
          ((n : ℂ) ^ w)⁻¹) * Complex.exp (-w * (t : ℂ))) *
        star
          ((finiteVonMangoldtDepthOneAmplitude n *
            ((n : ℂ) ^ v)⁻¹) * Complex.exp (-v * (t : ℂ))) = _
    rw [hstarMul, hstarExp]
    rw [show
      (finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ w)⁻¹) *
            Complex.exp (-w * (t : ℂ)) *
          (star (finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ v)⁻¹) *
            Complex.exp (-(star v) * (t : ℂ))) =
        ((finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ w)⁻¹) *
          star (finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ v)⁻¹)) *
          (Complex.exp (-w * (t : ℂ)) *
            Complex.exp (-(star v) * (t : ℂ))) by ring,
      ← Complex.exp_add]
    congr 1
    ring
  rw [hfun, integral_const_mul, integral_cauchyFeaturePair hrate]

theorem star_natCast_cpow_commonTest
    (n : ℕ) (w : ℂ) (hn : n ≠ 0) :
    star (((n : ℂ) ^ w)) = (n : ℂ) ^ star w := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have harg : ((n : ℂ).arg ≠ Real.pi) := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg hnpos.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (n : ℂ) w harg
  simpa using h.symm

theorem star_eulerPrimitivePrimeFeature
    (w : ℂ) (n : ℕ) (hn : n ≠ 0) :
    star (((n : ℂ) ^ w)⁻¹) =
      ((n : ℂ) ^ star w)⁻¹ := by
  rw [star_inv₀, star_natCast_cpow_commonTest n w hn]

theorem eulerPrimitiveCommonTestLabelWeight_eq_term
    (w v : ℂ) (n : ℕ) :
    (finiteVonMangoldtDepthOneAmplitude n *
          ((n : ℂ) ^ w)⁻¹) *
        star (finiteVonMangoldtDepthOneAmplitude n *
          ((n : ℂ) ^ v)⁻¹) =
      LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (w + star v + 1) n := by
  by_cases hn : n = 0
  · subst n
    simp [finiteVonMangoldtDepthOneAmplitude, LSeries.term]
  · have hampStar :
        star (finiteVonMangoldtDepthOneAmplitude n) =
          finiteVonMangoldtDepthOneAmplitude n := by
      simp [finiteVonMangoldtDepthOneAmplitude]
    have hstarMul :
        star (finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ v)⁻¹) =
          star (finiteVonMangoldtDepthOneAmplitude n) *
            star (((n : ℂ) ^ v)⁻¹) := by
      exact map_mul (starRingEnd ℂ) _ _
    rw [hstarMul, hampStar, star_eulerPrimitivePrimeFeature v n hn]
    rw [show
      (finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ w)⁻¹) *
          (finiteVonMangoldtDepthOneAmplitude n * ((n : ℂ) ^ star v)⁻¹) =
        finiteVonMangoldtDepthOneAmplitude n ^ (2 : ℕ) *
          (((n : ℂ) ^ w)⁻¹ * ((n : ℂ) ^ star v)⁻¹) by ring,
      finiteVonMangoldtDepthOneAmplitude_sq hn]
    rw [finiteVonMangoldtWeight, LSeries.term_of_ne_zero hn,
      LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add (w + star v) 1 (Nat.cast_ne_zero.mpr hn),
      Complex.cpow_add w (star v) (Nat.cast_ne_zero.mpr hn)]
    simp only [div_eq_mul_inv]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    ring

theorem integral_eulerPrimitiveCommonTestFeature_eq_term
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) (n : ℕ) :
    (∫ t : ℝ in Ioi 0,
        eulerPrimitiveCommonTestFeature w n t *
          star (eulerPrimitiveCommonTestFeature v n t)) =
      LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (w + star v + 1) n *
        (1 / (w + star v)) := by
  rw [integral_eulerPrimitiveCommonTestFeature hw hv,
    eulerPrimitiveCommonTestLabelWeight_eq_term]

/-- Literal infinite label-time source kernel.  The sum over `n` is taken
only after the common half-line test has been paired inside each retained
prime-power fibre. -/
def eulerPrimitiveCommonTestSourceKernel (w v : ℂ) : ℂ :=
  ∑' n : ℕ, ∫ t : ℝ in Ioi 0,
    eulerPrimitiveCommonTestFeature w n t *
      star (eulerPrimitiveCommonTestFeature v n t)

/-- Analytic value of the source-pointed critical common-test kernel. -/
def eulerPrimitiveCommonTestKernel (w v : ℂ) : ℂ :=
  vonMangoldtPrimeLaplaceChannelComplex (w + star v) *
    (1 / (w + star v))

theorem summable_integral_eulerPrimitiveCommonTestFeature
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      eulerPrimitiveCommonTestFeature w n t *
        star (eulerPrimitiveCommonTestFeature v n t)) := by
  have hs :
      Summable (LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (w + star v + 1)) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    change 1 < w.re + v.re + 1
    linarith
  exact (hs.mul_right (1 / (w + star v))).congr
    (fun n => (integral_eulerPrimitiveCommonTestFeature_eq_term hw hv n).symm)

/-- Exact source realization: the infinite label-time pairing is the
von-Mangoldt channel tensored with the common Hardy Cauchy test. -/
theorem eulerPrimitiveCommonTestSourceKernel_eq
    {w v : ℂ} (hw : 0 < w.re) (hv : 0 < v.re) :
    eulerPrimitiveCommonTestSourceKernel w v =
      eulerPrimitiveCommonTestKernel w v := by
  rw [eulerPrimitiveCommonTestSourceKernel,
    eulerPrimitiveCommonTestKernel]
  have hs :
      Summable (LSeries.term
        (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        (w + star v + 1)) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    change 1 < w.re + v.re + 1
    linarith
  rw [show
    (fun n : ℕ => ∫ t : ℝ in Ioi 0,
        eulerPrimitiveCommonTestFeature w n t *
          star (eulerPrimitiveCommonTestFeature v n t)) =
      fun n : ℕ =>
        LSeries.term
            (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
            (w + star v + 1) n *
          (1 / (w + star v)) by
    funext n
    exact integral_eulerPrimitiveCommonTestFeature_eq_term hw hv n,
    hs.tsum_mul_right]
  rfl

/-- Finite packet of the source-pointed critical common-test kernel. -/
def eulerPrimitiveCommonTestGram
    {N : ℕ} (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (vonMangoldtPrimeRightHalfPlaneGram w) ⊙
    (rightHalfPlaneHardyCauchyGram w)

theorem eulerPrimitiveCommonTestGram_apply
    {N : ℕ} (w : Fin N → ℂ) (i j : Fin N) :
    eulerPrimitiveCommonTestGram w i j =
      eulerPrimitiveCommonTestKernel (w i) (w j) := by
  rfl

/-- The infinite prime-power label and the common Hardy test coexist in one
positive tensor Gram. -/
theorem eulerPrimitiveCommonTestGram_posSemidef
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    (eulerPrimitiveCommonTestGram w).PosSemidef := by
  exact
    (vonMangoldtPrimeRightHalfPlaneGram_posSemidef w hw).hadamard
      (rightHalfPlaneHardyCauchyGram_posSemidef hw)

end

end RHTower
