import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg

/-!
# Sign alignment of the squared-Xi radial source jets

The squared-coordinate radial operator has positive reverse-Bessel magnitudes and alternating jet
signs.  This module packages those magnitudes recursively and proves the source identity needed by
the first unprotected squared-Xi derivative: after the formal Xi jet split is substituted, every
von Mangoldt jet occurs with the same negative sign.

The analytic theorem identifying this finite jet polynomial with the iterated radial derivative is
separate.  No RH assumption, zero location, or numerical input occurs here.
-/

noncomputable section

namespace RHTower

open Complex LSeries ArithmeticFunction
open scoped LSeries.notation

/-- Positive reverse-Bessel magnitudes forced by repeated application of
`(2*w)⁻¹ d/dw` to `L(1/2+w)/w`.

Inside the triangular range they satisfy
`b(n+1,j)=(2*n+1-j)*b(n,j)+b(n,j-1)`, with `b(0,0)=1`. -/
def squaredRadialJetWeight : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (2 * n + 1) * squaredRadialJetWeight n 0
  | n + 1, j + 1 =>
      (2 * n - j) * squaredRadialJetWeight n (j + 1) +
        squaredRadialJetWeight n j

@[simp] theorem squaredRadialJetWeight_zero_zero :
    squaredRadialJetWeight 0 0 = 1 := rfl

@[simp] theorem squaredRadialJetWeight_zero_succ (j : ℕ) :
    squaredRadialJetWeight 0 (j + 1) = 0 := rfl

@[simp] theorem squaredRadialJetWeight_succ_zero (n : ℕ) :
    squaredRadialJetWeight (n + 1) 0 =
      (2 * n + 1) * squaredRadialJetWeight n 0 := rfl

@[simp] theorem squaredRadialJetWeight_succ_succ (n j : ℕ) :
    squaredRadialJetWeight (n + 1) (j + 1) =
      (2 * n - j) * squaredRadialJetWeight n (j + 1) +
        squaredRadialJetWeight n j := rfl

/-- The rational and half-argument digamma portions of the `j`th Xi logarithmic jet. -/
def xiRationalGammaJet (j : ℕ) (s : ℂ) : ℂ :=
  iteratedDeriv j
      (fun z : ℂ => 1 / z + 1 / (z - 1) - (Real.log Real.pi) / 2) s +
    (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma (s / 2)

/-- Alternating, positively rescaled squared-radial Xi jet polynomial. -/
def squaredXiAlternatingJetPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
      iteratedDeriv j xiLogDeriv (1 / 2 + w)

/-- Rational--Gamma part of the alternating squared-radial jet polynomial. -/
def squaredXiAlternatingRationalGammaJetPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
      xiRationalGammaJet j (1 / 2 + w)

/-- Positive-coefficient von Mangoldt part of the alternating squared-radial jet polynomial. -/
def squaredXiPrimeJetPolynomial (n : ℕ) (w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (squaredRadialJetWeight n j : ℂ) * w ^ j *
      LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w)

/-- **Exact source sign alignment.**  On the half-plane of absolute Euler convergence, the
alternating squared-radial Xi jet is its rational--Gamma jet minus a prime jet whose finite
reverse-Bessel coefficients carry no alternating signs. -/
theorem squaredXiAlternatingJetPolynomial_eq_rationalGamma_sub_prime
    (n : ℕ) {w : ℂ} (hw : 1 < (1 / 2 + w).re) :
    squaredXiAlternatingJetPolynomial n w =
      squaredXiAlternatingRationalGammaJetPolynomial n w -
        squaredXiPrimeJetPolynomial n w := by
  rw [squaredXiAlternatingJetPolynomial,
    squaredXiAlternatingRationalGammaJetPolynomial,
    squaredXiPrimeJetPolynomial, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_xiLogDeriv_split j hw]
  have hsign : (-1 : ℂ) ^ j * (-1 : ℂ) ^ (j + 1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  rw [xiRationalGammaJet]
  calc
    (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
          (iteratedDeriv j
              (fun z : ℂ => 1 / z + 1 / (z - 1) - (Real.log Real.pi) / 2)
              (1 / 2 + w) +
            (1 / 2 : ℂ) ^ (j + 1) *
              iteratedDeriv j Complex.digamma ((1 / 2 + w) / 2) +
            (-1 : ℂ) ^ (j + 1) *
              LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w)) =
        (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
            xiRationalGammaJet j (1 / 2 + w) +
          (squaredRadialJetWeight n j : ℂ) * w ^ j *
            ((-1 : ℂ) ^ j * (-1 : ℂ) ^ (j + 1)) *
              LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w) := by
          rw [xiRationalGammaJet]
          ring
    _ = (squaredRadialJetWeight n j : ℂ) * w ^ j * (-1 : ℂ) ^ j *
            xiRationalGammaJet j (1 / 2 + w) -
          (squaredRadialJetWeight n j : ℂ) * w ^ j *
            LSeries (LSeries.logMul^[j] ↗Λ) (1 / 2 + w) := by
          rw [hsign]
          ring

end RHTower
