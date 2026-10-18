import GaloisForLFunctions.RHTower.XiThetaHermiteMixedLimit

/-!
# Exact identity for the normalized actual Xi Jensen polynomials

The coefficient sequence is the existing theta-integral sequence
`xiJensenCoeff`. The normalization is an affine change in its literal Jensen
polynomial, not a model sequence.
-/

open Polynomial Filter Topology Finset
open GaloisForLFunctions.SignAlternation

noncomputable section

namespace RHTower

theorem xiJensenCoeff_add (n j : ℕ) :
    xiJensenCoeff (n + j) = xiJensenCoeff n *
      (thetaCuspRawEvenMoment (n + j) / thetaCuspRawEvenMoment n) /
        (4 ^ j * ScaledHypergeometric.rising ((n : ℝ) + 1 / 2) j) := by
  induction j with
  | zero =>
    have hm := thetaCuspRawEvenMoment_pos n
    simp [hm.ne']
  | succ j ih =>
    have hm := thetaCuspRawEvenMoment_pos n
    have hmj := thetaCuspRawEvenMoment_pos (n + j)
    have hr := ScaledHypergeometric.rising_pos (by positivity : 0 < (n : ℝ) + 1 / 2) j
    have hnj : 0 < (n : ℝ) + 1 / 2 + j := by positivity
    rw [show n + (j + 1) = n + j + 1 by omega, xiJensenCoeff_succ, ih,
      ScaledHypergeometric.rising_succ, pow_succ]
    push_cast
    field_simp
    ring

theorem xiJensenCoeff_scaled_moment (n j : ℕ) :
    xiJensenCoeff (n + j) / xiJensenScale n ^ j =
      xiJensenCoeff n * laguerreJensenRatio ((n : ℝ) + 1 / 2) j *
        xiThetaExpectation n (X ^ j) / (thetaJensenSaddle n ^ 2) ^ j := by
  have hm := thetaCuspRawEvenMoment_pos n
  have hs := thetaJensenSaddle_pos n
  have hr := ScaledHypergeometric.rising_pos (by positivity : 0 < (n : ℝ) + 1 / 2) j
  rw [xiJensenCoeff_add, xiJensenScale, laguerreJensenRatio, xiThetaExpectation_X_pow]
  simp only [div_pow, mul_pow]
  field_simp

def xiJensenHermitePolynomial (n d : ℕ) : ℝ[X] :=
  C ((xiJensenCoeff n * xiJensenDelta n ^ d)⁻¹) *
    (jensenPoly xiJensenCoeff d n).comp
      (C ((xiJensenScale n)⁻¹) * (C (xiJensenDelta n) * X - 1))

theorem xiThetaExpectation_laguerre (n d : ℕ) (a : ℝ) :
    xiThetaExpectation n ((laguerreJensen ((n : ℝ) + 1 / 2) d).comp (C a * X)) =
      ∑ j ∈ range (d + 1), (d.choose j : ℝ) * laguerreJensenRatio ((n : ℝ) + 1 / 2) j *
        a ^ j * xiThetaExpectation n (X ^ j) := by
  simp only [laguerreJensen, Polynomial.sum_comp, monomial_comp, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_pow, ← map_pow, mul_assoc, xiThetaExpectation_C_mul, xiThetaExpectation_C_mul]

theorem eval_jensenPoly_xi_eq_laguerre_expectation (n d : ℕ) (x : ℝ) :
    (jensenPoly xiJensenCoeff d n).eval ((xiJensenDelta n * x - 1) / xiJensenScale n) =
      xiJensenCoeff n * xiThetaExpectation n
        ((laguerreJensen ((n : ℝ) + 1 / 2) d).comp
          (C ((xiJensenDelta n * x - 1) / thetaJensenSaddle n ^ 2) * X)) := by
  rw [xiThetaExpectation_laguerre, jensenPoly]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (d.choose j : ℝ) * xiJensenCoeff (n + j) *
        ((xiJensenDelta n * x - 1) / xiJensenScale n) ^ j =
      ((d.choose j : ℝ) * (xiJensenDelta n * x - 1) ^ j) *
        (xiJensenCoeff (n + j) / xiJensenScale n ^ j) := by rw [div_pow]; ring
    _ = _ := by rw [xiJensenCoeff_scaled_moment, div_pow]; ring

theorem xiThetaHermiteArgument_affine (n : ℕ) (x y : ℝ) :
    xiJensenDelta n * (xiThetaHermiteArgument n x).eval y - 1 =
      ((xiJensenDelta n * x - 1) / thetaJensenSaddle n ^ 2) * y := by
  have hs := thetaJensenSaddle_pos n
  have hr : 0 < Real.sqrt ((n : ℝ) + 1 / 2) := by positivity
  simp only [xiThetaHermiteArgument, xiThetaFluctuation, eval_add, eval_mul, eval_C,
    eval_sub, eval_X, xiJensenDelta]
  field_simp
  ring

theorem xiThetaHermite_polynomial_identity (n d : ℕ) (x : ℝ) :
    C (xiJensenDelta n ^ d) *
      (laguerreHermite (xiJensenDelta n) d).comp (xiThetaHermiteArgument n x) =
        (laguerreJensen ((n : ℝ) + 1 / 2) d).comp
          (C ((xiJensenDelta n * x - 1) / thetaJensenSaddle n ^ 2) * X) := by
  apply Polynomial.funext
  intro y
  simp only [eval_mul, eval_C, eval_comp, eval_X]
  rw [laguerreHermite_eval_eq_laguerre (by positivity) (xiJensenDelta_sq n),
    xiThetaHermiteArgument_affine]

theorem eval_xiJensenHermitePolynomial (n d : ℕ) (x : ℝ) :
    (xiJensenHermitePolynomial n d).eval x = xiThetaExpectation n
      ((laguerreHermite (xiJensenDelta n) d).comp (xiThetaHermiteArgument n x)) := by
  have hγ := xiJensenCoeff_pos n
  have hδ := xiJensenDelta_pos n
  have hE := congrArg (xiThetaExpectation n) (xiThetaHermite_polynomial_identity n d x)
  rw [xiThetaExpectation_C_mul] at hE
  simp only [xiJensenHermitePolynomial, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one]
  rw [show (xiJensenScale n)⁻¹ * (xiJensenDelta n * x - 1) =
      (xiJensenDelta n * x - 1) / xiJensenScale n by ring,
    eval_jensenPoly_xi_eq_laguerre_expectation, ← hE]
  field_simp

end RHTower
