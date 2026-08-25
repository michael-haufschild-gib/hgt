import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedClassicalDerivativeTruncation
import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear

/-!
# Finite displaced Levinson detector as Dirichlet polynomials

The finite classical Gaussian AFE and its height derivative combine into
Levinson's detector `zeta + lambda zeta'`.  This file rewrites both finite
Dirichlet heads as literal `Sieve.dirPoly` values.  Pole terms are retained.
-/

noncomputable section

namespace RHTower

open Complex

/-- Finite classical two-head approximation to zeta on a displaced line. -/
def smoothAFEZetaDisplacedFiniteClassicalValue
    (d x tau : ℝ) (L : ℕ) : ℂ :=
  (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDirectTerm d x tau n) +
    (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedReflectedMainTerm d tau n) -
    smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x

/-- Finite approximation to `zeta + lambda zeta'`; height differentiation is
`i zeta'`, hence the factor `-i` on the differentiated AFE. -/
def smoothAFEZetaDisplacedFiniteClassicalDetector
    (lam d x tau : ℝ) (L : ℕ) : ℂ :=
  smoothAFEZetaDisplacedFiniteClassicalValue d x tau L +
    (lam : ℂ) * (-I) *
      smoothAFEZetaDisplacedFiniteClassicalHeightDerivative d x tau L

/-- Direct-head coefficient of the finite Levinson detector. -/
def smoothAFEZetaDisplacedDirectDetectorCoeff
    (lam d x : ℝ) (n : ℕ) : ℂ :=
  ((n + 1 : ℂ) ^ (-displacedLinePt d 0) *
      smoothAFECutoff ((n + 1 : ℝ) / x)) *
    (1 - (lam : ℂ) * Complex.log (n + 1 : ℂ))

/-- Base coefficient of the reflected finite Dirichlet head. -/
def smoothAFEZetaDisplacedReflectedBaseCoeff
    (d : ℝ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (displacedLinePt d 0 - 1)

/-- Reflected coefficient carrying the `1 + lambda log n` detector factor. -/
def smoothAFEZetaDisplacedReflectedDetectorCoeff
    (lam d : ℝ) (n : ℕ) : ℂ :=
  smoothAFEZetaDisplacedReflectedBaseCoeff d n *
    (1 + (lam : ℂ) * Complex.log (n + 1 : ℂ))

theorem natSucc_cpow_neg_displacedLinePt_eq_phase
    (d tau : ℝ) (n : ℕ) :
    (n + 1 : ℂ) ^ (-displacedLinePt d tau) =
      (n + 1 : ℂ) ^ (-displacedLinePt d 0) *
        Complex.exp (((-tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hnR : (0 : ℝ) < n + 1 := by positivity
  rw [show -displacedLinePt d tau =
      -displacedLinePt d 0 + (((-tau : ℝ) : ℂ) * I) by
    unfold displacedLinePt
    push_cast
    ring]
  rw [Complex.cpow_add _ _ hn]
  have hphase : (n + 1 : ℂ) ^ (((-tau : ℝ) : ℂ) * I) =
      Complex.exp (((-tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hn]
    congr 1
    have hlog : Complex.log (n + 1 : ℂ) =
        ((Real.log (n + 1 : ℝ) : ℝ) : ℂ) := by
      rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_log hnR.le).symm
    rw [hlog]
    push_cast
    ring
  rw [hphase]

theorem natSucc_cpow_displacedLinePt_sub_one_eq_phase
    (d tau : ℝ) (n : ℕ) :
    (n + 1 : ℂ) ^ (displacedLinePt d tau - 1) =
      (n + 1 : ℂ) ^ (displacedLinePt d 0 - 1) *
        Complex.exp (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hnR : (0 : ℝ) < n + 1 := by positivity
  rw [show displacedLinePt d tau - 1 =
      (displacedLinePt d 0 - 1) + (((tau : ℝ) : ℂ) * I) by
    unfold displacedLinePt
    push_cast
    ring]
  rw [Complex.cpow_add _ _ hn]
  have hphase : (n + 1 : ℂ) ^ (((tau : ℝ) : ℂ) * I) =
      Complex.exp (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hn]
    congr 1
    have hlog : Complex.log (n + 1 : ℂ) =
        ((Real.log (n + 1 : ℝ) : ℝ) : ℂ) := by
      rw [show (n + 1 : ℂ) = ((n + 1 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_log hnR.le).symm
    rw [hlog]
    push_cast
    ring
  rw [hphase]

/-- Natural-index form of a finite Dirichlet polynomial. -/
theorem sieveDirPoly_nat_eq_sum_range
    (L : ℕ) (a : ℕ → ℂ) (tau : ℝ) :
    Sieve.dirPoly L (fun n => a n) tau =
      ∑ n ∈ Finset.range L,
        a n * Complex.exp (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I) := by
  rw [Sieve.dirPoly]
  let F : ℕ → ℂ := fun n =>
    a n * Complex.exp (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I)
  change (∑ n : Fin L, F n) = _
  rw [Fin.sum_univ_eq_sum_range]

/-- Direct value and derivative heads combine into one Dirichlet polynomial. -/
theorem sum_smoothAFEZetaDisplacedDirect_detector_eq_dirPoly
    (lam d x tau : ℝ) (L : ℕ) :
    (∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedDirectTerm d x tau n) +
      (lam : ℂ) * (-I) *
        (∑ n ∈ Finset.range L,
          smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n) =
      Sieve.dirPoly L
        (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-tau) := by
  rw [Sieve.dirPoly]
  let F : ℕ → ℂ := fun n =>
    smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n *
      Complex.exp (((-tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I)
  change _ = ∑ n : Fin L, F n
  rw [Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [smoothAFEZetaDisplacedDirectTerm,
    smoothAFEZetaDisplacedDirectHeightDerivativeTerm,
    natSucc_cpow_neg_displacedLinePt_eq_phase]
  dsimp only [F, smoothAFEZetaDisplacedDirectDetectorCoeff]
  ring_nf
  rw [pow_two, I_mul_I]
  ring

/-- Reflected value and derivative heads split into the base and
`1 + lambda log n` Dirichlet polynomials. -/
theorem sum_smoothAFEZetaDisplacedReflected_detector_eq_dirPoly
    (lam d tau : ℝ) (L : ℕ) :
    (∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedReflectedMainTerm d tau n) +
      (lam : ℂ) * (-I) *
        (∑ n ∈ Finset.range L,
          smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n) =
      (lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
          Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau +
        zetaChi (displacedLinePt d tau) *
          Sieve.dirPoly L
            (fun n =>
              smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau := by
  rw [sieveDirPoly_nat_eq_sum_range,
    sieveDirPoly_nat_eq_sum_range]
  calc
    (∑ n ∈ Finset.range L,
          smoothAFEZetaDisplacedReflectedMainTerm d tau n) +
        (lam : ℂ) * (-I) *
          (∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d tau n) =
        ∑ n ∈ Finset.range L,
          (smoothAFEZetaDisplacedReflectedMainTerm d tau n +
            (lam : ℂ) * (-I) *
              smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
                d tau n) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ n ∈ Finset.range L,
          ((lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
              (smoothAFEZetaDisplacedReflectedBaseCoeff d n *
                Complex.exp
                  (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I)) +
            zetaChi (displacedLinePt d tau) *
              (smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n *
                Complex.exp
                  (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [smoothAFEZetaDisplacedReflectedMainTerm,
        smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm,
        natSucc_cpow_displacedLinePt_sub_one_eq_phase]
      dsimp only [smoothAFEZetaDisplacedReflectedBaseCoeff,
        smoothAFEZetaDisplacedReflectedDetectorCoeff]
      ring_nf
      rw [pow_two, I_mul_I]
      ring
    _ = (lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
          (∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedBaseCoeff d n *
              Complex.exp
                (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I)) +
        zetaChi (displacedLinePt d tau) *
          (∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n *
              Complex.exp
                (((tau * Real.log (n + 1 : ℝ) : ℝ) : ℂ) * I)) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

/-- Exact Dirichlet-polynomial normal form of the finite displaced Levinson
detector.  Both reflected `chi` factors and both pole terms remain explicit. -/
theorem smoothAFEZetaDisplacedFiniteClassicalDetector_eq_dirPoly
    (lam d x tau : ℝ) (L : ℕ) :
    smoothAFEZetaDisplacedFiniteClassicalDetector lam d x tau L =
      Sieve.dirPoly L
          (fun n =>
            smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) (-tau) +
        (lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
          Sieve.dirPoly L
            (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau +
        zetaChi (displacedLinePt d tau) *
          Sieve.dirPoly L
            (fun n =>
              smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x +
        (lam : ℂ) * I *
          smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau := by
  have hdecomp :
      smoothAFEZetaDisplacedFiniteClassicalDetector lam d x tau L =
        ((∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectTerm d x tau n) +
          (lam : ℂ) * (-I) *
            (∑ n ∈ Finset.range L,
              smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n)) +
        ((∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedReflectedMainTerm d tau n) +
          (lam : ℂ) * (-I) *
            (∑ n ∈ Finset.range L,
              smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
                d tau n)) -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x +
        (lam : ℂ) * I *
          smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau := by
    unfold smoothAFEZetaDisplacedFiniteClassicalDetector
      smoothAFEZetaDisplacedFiniteClassicalValue
      smoothAFEZetaDisplacedFiniteClassicalHeightDerivative
    ring
  rw [hdecomp,
    sum_smoothAFEZetaDisplacedDirect_detector_eq_dirPoly,
    sum_smoothAFEZetaDisplacedReflected_detector_eq_dirPoly]
  ring

/-- Multiplication by an arbitrary finite mollifier.  The direct same-frequency
product becomes a Dirichlet convolution; the two reflected opposite-frequency
products are retained for the twisted mean-value theorem. -/
theorem smoothAFEZetaDisplacedFiniteClassicalDetector_mul_dirPoly
    (lam d x tau : ℝ) (L M : ℕ) (a : Fin M → ℂ) :
    smoothAFEZetaDisplacedFiniteClassicalDetector lam d x tau L *
        Sieve.dirPoly M a (-tau) =
      Sieve.dirPoly (L * M)
          (Sieve.dirConv L M
            (fun n =>
              smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) a) (-tau) +
        (lam : ℂ) * deriv zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n => smoothAFEZetaDisplacedReflectedBaseCoeff d n) tau *
            Sieve.dirPoly M a (-tau)) +
        zetaChi (displacedLinePt d tau) *
          (Sieve.dirPoly L
              (fun n =>
                smoothAFEZetaDisplacedReflectedDetectorCoeff lam d n) tau *
            Sieve.dirPoly M a (-tau)) -
        smoothAFEZetaShiftedPoleResidue (displacedLinePt d tau) x *
          Sieve.dirPoly M a (-tau) +
        (lam : ℂ) * I *
          smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau *
            Sieve.dirPoly M a (-tau) := by
  rw [smoothAFEZetaDisplacedFiniteClassicalDetector_eq_dirPoly]
  rw [← Sieve.dirPoly_mul_eq_dirPoly L M
    (fun n => smoothAFEZetaDisplacedDirectDetectorCoeff lam d x n) a (-tau)]
  ring

end RHTower
