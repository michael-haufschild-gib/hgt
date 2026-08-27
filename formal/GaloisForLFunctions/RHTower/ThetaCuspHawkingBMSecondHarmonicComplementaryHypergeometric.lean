import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicHorizonWronskianMonodromy

/-!
# BM complementary second-harmonic hypergeometric series

The nonresonant complementary `++` Frobenius solution needs the convergent factor
`₂F₁(a-c+1,b-c+1;2-c;z)`, not only its leading power. This module computes its exact BM
parameters and proves that none is a nonpositive integer whenever `χ.re ≠ 0`. Mathlib's
ordinary-hypergeometric theorem then gives radius one, in particular on every Xi fibre.

The module also proves the exact Pochhammer coefficient recurrence that is the coefficientwise
engine for the missing analytic hypergeometric ODE theorem.
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries Polynomial

namespace RHTower

noncomputable section

/-- First transformed parameter `a-c+1` of the complementary `++` solution. -/
def d4BMPlusPlusComplementaryHypergeometricA
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi -
    d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) + 1

/-- Second transformed parameter `b-c+1` of the complementary `++` solution. -/
def d4BMPlusPlusComplementaryHypergeometricB
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi -
    d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) + 1

/-- Transformed denominator parameter `2-c` of the complementary `++` solution. -/
def d4BMPlusPlusComplementaryHypergeometricC
    (n : ℕ) (chi : ℂ) : ℂ :=
  2 - d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)

/-- Exact affine form of complementary parameter `a-c+1`. -/
theorem d4BMPlusPlusComplementaryHypergeometricA_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusComplementaryHypergeometricA n chi =
      2 * (n : ℂ) + 7 / 4 + 3 * Complex.I * chi / 2 := by
  rw [d4BMPlusPlusComplementaryHypergeometricA,
    d4BMCausalHypergeometricA_plusPlus]
  have h := d4BMPlusPlusComplementaryFrobeniusExponent_eq n chi
  rw [d4BMPlusPlusComplementaryFrobeniusExponent] at h
  linear_combination h

/-- Exact affine form of complementary parameter `b-c+1`. -/
theorem d4BMPlusPlusComplementaryHypergeometricB_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusComplementaryHypergeometricB n chi =
      2 * (n : ℂ) + 7 / 4 + Complex.I * chi / 2 := by
  rw [d4BMPlusPlusComplementaryHypergeometricB,
    d4BMCausalHypergeometricB_plusPlus]
  have h := d4BMPlusPlusComplementaryFrobeniusExponent_eq n chi
  rw [d4BMPlusPlusComplementaryFrobeniusExponent] at h
  linear_combination h

/-- Exact affine form of complementary parameter `2-c`. -/
theorem d4BMPlusPlusComplementaryHypergeometricC_eq
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusComplementaryHypergeometricC n chi =
      4 * (n : ℂ) + 4 + 2 * Complex.I * chi := by
  rw [d4BMPlusPlusComplementaryHypergeometricC]
  have h := d4BMPlusPlusComplementaryFrobeniusExponent_eq n chi
  rw [d4BMPlusPlusComplementaryFrobeniusExponent] at h
  linear_combination h

/-- Imaginary part of complementary parameter `a-c+1`. -/
theorem d4BMPlusPlusComplementaryHypergeometricA_im
    (n : ℕ) (chi : ℂ) :
    (d4BMPlusPlusComplementaryHypergeometricA n chi).im =
      3 * chi.re / 2 := by
  rw [d4BMPlusPlusComplementaryHypergeometricA_eq]
  norm_num [Complex.mul_im]

/-- Imaginary part of complementary parameter `b-c+1`. -/
theorem d4BMPlusPlusComplementaryHypergeometricB_im
    (n : ℕ) (chi : ℂ) :
    (d4BMPlusPlusComplementaryHypergeometricB n chi).im =
      chi.re / 2 := by
  rw [d4BMPlusPlusComplementaryHypergeometricB_eq]
  norm_num [Complex.mul_im]

/-- Imaginary part of complementary denominator parameter `2-c`. -/
theorem d4BMPlusPlusComplementaryHypergeometricC_im
    (n : ℕ) (chi : ℂ) :
    (d4BMPlusPlusComplementaryHypergeometricC n chi).im =
      2 * chi.re := by
  rw [d4BMPlusPlusComplementaryHypergeometricC_eq]
  norm_num [Complex.mul_im]

/-- Nonzero momentum excludes every nonpositive-integral collision of all transformed parameters. -/
theorem d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠ -d4BMPlusPlusComplementaryHypergeometricA n chi ∧
      (j : ℂ) ≠ -d4BMPlusPlusComplementaryHypergeometricB n chi ∧
      (j : ℂ) ≠ -d4BMPlusPlusComplementaryHypergeometricC n chi := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [Complex.natCast_im, Complex.neg_im,
      d4BMPlusPlusComplementaryHypergeometricA_im] at him
    norm_num at him
    exact hchi (by linarith)
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [Complex.natCast_im, Complex.neg_im,
      d4BMPlusPlusComplementaryHypergeometricB_im] at him
    norm_num at him
    exact hchi (by linarith)
  · intro h
    have him := congrArg Complex.im h
    rw [Complex.natCast_im, Complex.neg_im,
      d4BMPlusPlusComplementaryHypergeometricC_im] at him
    norm_num at him
    exact hchi (by linarith)

/-- Conventional nonpositive-integral exclusion for transformed denominator parameter `2-c`. -/
theorem d4BMPlusPlusComplementaryHypergeometricC_ne_negNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    d4BMPlusPlusComplementaryHypergeometricC n chi ≠ -(j : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  rw [d4BMPlusPlusComplementaryHypergeometricC_im,
    Complex.neg_im, Complex.natCast_im] at him
  norm_num at him
  exact hchi (by linarith)

/-- Formal multilinear series for the complementary `++` hypergeometric factor. -/
def d4BMPlusPlusComplementaryHypergeometricSeries
    (n : ℕ) (chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ
    (d4BMPlusPlusComplementaryHypergeometricA n chi)
    (d4BMPlusPlusComplementaryHypergeometricB n chi)
    (d4BMPlusPlusComplementaryHypergeometricC n chi)

/-- Complementary `++` hypergeometric series has exact convergence radius one. -/
theorem d4BMPlusPlusComplementaryHypergeometricSeries_radius_eq_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (d4BMPlusPlusComplementaryHypergeometricSeries n chi).radius = 1 := by
  rw [d4BMPlusPlusComplementaryHypergeometricSeries]
  apply ordinaryHypergeometricSeries_radius_eq_one
  exact d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat n chi hchi

/-- Convergent `₂F₁(a-c+1,b-c+1;2-c;z)` factor of the complementary `++` branch. -/
def d4BMPlusPlusComplementaryHypergeometricFactor
    (n : ℕ) (chi z : ℂ) : ℂ :=
  ordinaryHypergeometric
    (d4BMPlusPlusComplementaryHypergeometricA n chi)
    (d4BMPlusPlusComplementaryHypergeometricB n chi)
    (d4BMPlusPlusComplementaryHypergeometricC n chi) z

/-- Complementary hypergeometric factor has unit horizon value. -/
@[simp] theorem d4BMPlusPlusComplementaryHypergeometricFactor_zero
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusComplementaryHypergeometricFactor n chi 0 = 1 := by
  simp [d4BMPlusPlusComplementaryHypergeometricFactor]

/-- Complementary hypergeometric factor is continuous at the horizon. -/
theorem continuousAt_d4BMPlusPlusComplementaryHypergeometricFactor_zero
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ContinuousAt (d4BMPlusPlusComplementaryHypergeometricFactor n chi) 0 := by
  change ContinuousAt
    (d4BMPlusPlusComplementaryHypergeometricSeries n chi).sum 0
  have hr : 0 < (d4BMPlusPlusComplementaryHypergeometricSeries n chi).radius := by
    rw [d4BMPlusPlusComplementaryHypergeometricSeries_radius_eq_one n chi hchi]
    norm_num
  exact ((d4BMPlusPlusComplementaryHypergeometricSeries n chi).hasFPowerSeriesOnBall
    hr).analyticAt.continuousAt

/-- Successor recurrence for ordinary hypergeometric coefficients away from denominator poles. -/
theorem ordinaryHypergeometricCoefficient_succ_recurrence
    (a b c : ℂ) (j : ℕ)
    (hc : (ascPochhammer ℂ j).eval c ≠ 0)
    (hcj : c + (j : ℂ) ≠ 0) :
    ((j + 1 : ℕ) : ℂ) * (c + (j : ℂ)) *
        ordinaryHypergeometricCoefficient a b c (j + 1) =
      (a + (j : ℂ)) * (b + (j : ℂ)) *
        ordinaryHypergeometricCoefficient a b c j := by
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, ascPochhammer_succ_eval]
  field_simp [hc, hcj, Nat.factorial_ne_zero]

/-- Exact coefficient recurrence for the BM complementary `++` hypergeometric series. -/
theorem d4BMPlusPlusComplementaryHypergeometricCoefficient_succ_recurrence
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    ((j + 1 : ℕ) : ℂ) *
        (d4BMPlusPlusComplementaryHypergeometricC n chi + (j : ℂ)) *
        ordinaryHypergeometricCoefficient
          (d4BMPlusPlusComplementaryHypergeometricA n chi)
          (d4BMPlusPlusComplementaryHypergeometricB n chi)
          (d4BMPlusPlusComplementaryHypergeometricC n chi) (j + 1) =
      (d4BMPlusPlusComplementaryHypergeometricA n chi + (j : ℂ)) *
        (d4BMPlusPlusComplementaryHypergeometricB n chi + (j : ℂ)) *
        ordinaryHypergeometricCoefficient
          (d4BMPlusPlusComplementaryHypergeometricA n chi)
          (d4BMPlusPlusComplementaryHypergeometricB n chi)
          (d4BMPlusPlusComplementaryHypergeometricC n chi) j := by
  apply ordinaryHypergeometricCoefficient_succ_recurrence
  · rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
    push Not
    intro k hk hkC
    exact
      (d4BMPlusPlusComplementaryHypergeometricParameters_ne_negNat
        n chi hchi k).2.2 hkC
  · intro hcj
    apply d4BMPlusPlusComplementaryHypergeometricC_ne_negNat n chi hchi j
    linear_combination hcj

/-- Every Xi-fibre complementary `++` hypergeometric series has radius one. -/
theorem d4BMXiPlusPlusComplementaryHypergeometricSeries_radius_eq_one
    (n : ℕ) (q : XiZeroCopy) :
    (d4BMPlusPlusComplementaryHypergeometricSeries
      n (d4BMXiMixedHorizonAngularMomentum q)).radius = 1 := by
  exact d4BMPlusPlusComplementaryHypergeometricSeries_radius_eq_one n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

/-- Every Xi-fibre complementary `++` hypergeometric factor is continuous at the horizon. -/
theorem continuousAt_d4BMXiPlusPlusComplementaryHypergeometricFactor_zero
    (n : ℕ) (q : XiZeroCopy) :
    ContinuousAt
      (d4BMPlusPlusComplementaryHypergeometricFactor
        n (d4BMXiMixedHorizonAngularMomentum q)) 0 := by
  exact continuousAt_d4BMPlusPlusComplementaryHypergeometricFactor_zero n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)

end

end RHTower
