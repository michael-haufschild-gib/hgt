import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedReflectedMovingMeanSquare
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedPoleResidueDerivative

/-!
# Gaussian decay for displaced mollified pole remainders

The two elementary pole terms in the differentiated displaced smooth AFE are packaged exactly
and bounded before any dyadic integration.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Pointwise `ell^(1 : ℕ)` envelope for the literal linear Levinson mollifier. -/
theorem norm_levinsonLinearMollifier_le
    {M : ℕ} (hM : 1 < M) (t : ℝ) :
    ‖Sieve.levinsonLinearMollifier M t‖ ≤ 2 * Real.sqrt M := by
  rw [Sieve.levinsonLinearMollifier_eq_sum]
  calc
    ‖∑ n ∈ Finset.Icc 1 M,
        Sieve.levinsonLinearMollifierCoeff M n *
          Complex.exp (((-(Real.log (n : ℝ)) * t : ℝ) : ℂ) * I)‖ ≤
      ∑ n ∈ Finset.Icc 1 M,
        ‖Sieve.levinsonLinearMollifierCoeff M n *
          Complex.exp (((-(Real.log (n : ℝ)) * t : ℝ) : ℂ) * I)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 M,
        ‖Sieve.levinsonLinearMollifierCoeff M n‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul]
      let phase : ℝ := -(Real.log (n : ℝ)) * t
      have hphase :
          ‖Complex.exp (((-(Real.log (n : ℝ)) * t : ℝ) : ℂ) * I)‖ = 1 := by
        change ‖Complex.exp ((phase : ℂ) * I)‖ = 1
        rw [Complex.norm_exp]
        have hre : ((phase : ℂ) * I).re = 0 := by
          simp [Complex.mul_re]
        rw [hre, Real.exp_zero]
      rw [hphase, mul_one]
    _ ≤ 2 * Real.sqrt M := Sieve.sum_norm_levinsonLinearMollifierCoeff_le hM

/-- Gaussian decay of the shifted pole residue on the displaced Levinson line. -/
theorem norm_smoothAFEZetaShiftedPoleResidue_displaced_le
    {d x t : ℝ} (_hd : 0 < d) (hx : 0 < x) (ht : 1 ≤ |t|) :
    ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x‖ ≤
      x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2) *
        Real.exp (-(t ^ 2)) := by
  have hden : 1 ≤ ‖1 - displacedLinePt d t‖ := by
    have hcoord : 1 - displacedLinePt d t =
        smoothAFEZetaDisplacedPoleCoordinate d t := by
      rfl
    rw [hcoord]
    exact ht.trans (abs_le_norm_smoothAFEZetaDisplacedPoleCoordinate d t)
  rw [smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (1 - displacedLinePt d t).re = 1 / 2 + d := by
    rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
    ring
  have hexp : ‖Complex.exp ((1 - displacedLinePt d t) ^ 2)‖ =
      Real.exp ((1 / 2 + d) ^ 2 - t ^ 2) := by
    simpa only [smoothAFEZetaDisplacedPoleCoordinate] using
      norm_smoothAFEZetaDisplacedPoleCoordinate_exp_sq d t
  rw [hre, hexp]
  calc
    x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2 - t ^ 2) /
        ‖1 - displacedLinePt d t‖ ≤
      x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2 - t ^ 2) := by
        apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
        exact le_mul_of_one_le_right (by positivity) hden
    _ = x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2) *
        Real.exp (-(t ^ 2)) := by
      rw [show (1 / 2 + d) ^ 2 - t ^ 2 =
        (1 / 2 + d) ^ 2 + (-(t ^ 2)) by ring, Real.exp_add]
      ring

/-- Exact sum of the two mollified pole terms in the finite displaced detector normal form. -/
def smoothAFEZetaDisplacedMollifiedPoleRemainder
    (lam d x : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  -smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x *
      Sieve.levinsonLinearMollifier M t +
    (lam : ℂ) * I *
      smoothAFEZetaDisplacedPoleResidueHeightDerivative d x t *
        Sieve.levinsonLinearMollifier M t

/-- Pointwise Gaussian envelope for both literal mollified pole terms together. -/
theorem norm_smoothAFEZetaDisplacedMollifiedPoleRemainder_le
    {lam d x t : ℝ} (hd : 0 < d) (hx : 0 < x) (ht : 1 ≤ |t|)
    {M : ℕ} (hM : 1 < M) :
    ‖smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t‖ ≤
      (2 * Real.sqrt M) *
        (x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2)) *
        (1 + |lam| * (|Real.log x| + 3)) * Real.exp (-(t ^ 2)) := by
  have hres := norm_smoothAFEZetaShiftedPoleResidue_displaced_le hd hx ht
  have hder := norm_smoothAFEZetaDisplacedPoleResidueHeightDerivative_le hd hx ht
  have hmoll := norm_levinsonLinearMollifier_le hM t
  rw [smoothAFEZetaDisplacedMollifiedPoleRemainder]
  calc
    ‖-smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x *
          Sieve.levinsonLinearMollifier M t +
        (lam : ℂ) * I * smoothAFEZetaDisplacedPoleResidueHeightDerivative d x t *
          Sieve.levinsonLinearMollifier M t‖ ≤
      ‖-smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x *
          Sieve.levinsonLinearMollifier M t‖ +
        ‖(lam : ℂ) * I * smoothAFEZetaDisplacedPoleResidueHeightDerivative d x t *
          Sieve.levinsonLinearMollifier M t‖ := norm_add_le _ _
    _ = ‖smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x‖ *
          ‖Sieve.levinsonLinearMollifier M t‖ +
        |lam| * ‖smoothAFEZetaDisplacedPoleResidueHeightDerivative d x t‖ *
          ‖Sieve.levinsonLinearMollifier M t‖ := by
      rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one]
    _ ≤ (x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2) *
          Real.exp (-(t ^ 2))) * (2 * Real.sqrt M) +
        |lam| *
          (x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2) *
            (|Real.log x| + 3) * Real.exp (-(t ^ 2))) *
          (2 * Real.sqrt M) := by
      gcongr
    _ = (2 * Real.sqrt M) *
        (x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2)) *
        (1 + |lam| * (|Real.log x| + 3)) * Real.exp (-(t ^ 2)) := by ring

end RHTower
