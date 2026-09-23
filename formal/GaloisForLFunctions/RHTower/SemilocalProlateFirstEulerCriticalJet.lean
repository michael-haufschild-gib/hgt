import GaloisForLFunctions.RHTower.SemilocalProlateCriticalPotential
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiRecurrence
import GaloisForLFunctions.RHTower.GammaOddJacobiCapacity
import GaloisForLFunctions.HTGeometry.CentralBinomialWallisAsymptotic
import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet

/-!
# First Euler jet of the semilocal prolate critical potential

The one-prime semilocal moment matrix has an exact rank-two first Euler tangent at `q = 0`.
In the archimedean orthonormal basis it is the difference of the even and odd rank-one
central-binomial blocks.  This file carries that literal determinant tangent through the Hankel
quotient for the Jacobi radii and then through the four-radius Route-J critical residual.

The resulting critical-residual tangent is not bounded in Jacobi degree.  Its sharp growth is

`criticalJet n / sqrt (2n) -> 4 * sqrt (2 / pi)`.

Thus the first Euler correction becomes order one at the boundary scale `n ≍ p²`.  This is a
statement about the fully orthogonalized Jacobi radii, not the earlier ground-row coefficient.
No claim about uniform control of the complete higher-order `q`-series is made.
-/

noncomputable section

open Filter Matrix Real
open scoped BigOperators Topology

namespace RHTower

namespace FirstEulerCriticalJet

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HilbertMetric

/-- Signed central-binomial coefficient
`αₙ = (-1)ⁿ binom(2n,n) / 4ⁿ` in the local-factor `q`-series. -/
def signedCentralBinom (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * normalizedCentralBinom n

/-- Positive square root of the unsigned central-binomial weight. -/
def tangentVectorEntry (n : ℕ) : ℝ :=
  Real.sqrt (normalizedCentralBinom n)

/-- Exact first Euler tangent in the archimedean orthonormal polynomial basis.  Equal parities
form two rank-one blocks; the odd block has the opposite sign. -/
def normalizedHankelTangent (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    if i.val % 2 = j.val % 2 then
      2 * Real.sqrt 2 * (-1 : ℝ) ^ i.val *
        tangentVectorEntry i.val * tangentVectorEntry j.val
    else 0

/-- Normalized Hankel determinant path having the literal first Euler tangent. -/
def normalizedHankelDeterminantPath (n : ℕ) (q : ℝ) : ℝ :=
  (1 + q • normalizedHankelTangent n).det

/-- First Euler coefficient of the normalized Hankel determinant. -/
def normalizedHankelDeterminantJet (n : ℕ) : ℝ :=
  2 * Real.sqrt 2 * ∑ j ∈ Finset.range (n + 1), signedCentralBinom j

theorem normalizedCentralBinom_nonneg (n : ℕ) :
    0 ≤ normalizedCentralBinom n := by
  unfold normalizedCentralBinom
  positivity

theorem tangentVectorEntry_sq (n : ℕ) :
    tangentVectorEntry n ^ (2 : ℕ) = normalizedCentralBinom n := by
  unfold tangentVectorEntry
  exact Real.sq_sqrt (normalizedCentralBinom_nonneg n)

/-- Literal coefficient of `q` in the published one-prime semilocal moment `c(2k,q)`.  It is the
`ℓ = 0` Lambert atom: `2 (-1)^k (1/2)^(2k)`. -/
def semilocalFirstEulerEvenMomentCoefficient (k : ℕ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k)

/-- First Euler Hankel entry in the monomial basis.  Odd total degree vanishes because the source
measure is even. -/
def semilocalFirstEulerMonomialHankelEntry (i j : ℕ) : ℝ :=
  if (i + j) % 2 = 0 then
    semilocalFirstEulerEvenMomentCoefficient ((i + j) / 2)
  else 0

@[simp]
theorem semilocalFirstEulerMonomialHankelEntry_even_even (i j : ℕ) :
    semilocalFirstEulerMonomialHankelEntry (2 * i) (2 * j) =
      semilocalFirstEulerEvenMomentCoefficient (i + j) := by
  unfold semilocalFirstEulerMonomialHankelEntry
  rw [if_pos (by omega)]
  congr 1
  omega

@[simp]
theorem semilocalFirstEulerMonomialHankelEntry_even_odd (i j : ℕ) :
    semilocalFirstEulerMonomialHankelEntry (2 * i) (2 * j + 1) = 0 := by
  unfold semilocalFirstEulerMonomialHankelEntry
  rw [if_neg (by omega)]

@[simp]
theorem semilocalFirstEulerMonomialHankelEntry_odd_even (i j : ℕ) :
    semilocalFirstEulerMonomialHankelEntry (2 * i + 1) (2 * j) = 0 := by
  unfold semilocalFirstEulerMonomialHankelEntry
  rw [if_neg (by omega)]

@[simp]
theorem semilocalFirstEulerMonomialHankelEntry_odd_odd (i j : ℕ) :
    semilocalFirstEulerMonomialHankelEntry (2 * i + 1) (2 * j + 1) =
      semilocalFirstEulerEvenMomentCoefficient (i + j + 1) := by
  unfold semilocalFirstEulerMonomialHankelEntry
  rw [if_pos (by omega)]
  congr 1
  omega

/-- Rank-one even monomial ray in the literal first source tangent. -/
def semilocalFirstEulerEvenMonomialRay (i : ℕ) : ℝ :=
  (-1 / 4 : ℝ) ^ i

/-- Rank-one odd monomial ray in the literal first source tangent. -/
def semilocalFirstEulerOddMonomialRay (i : ℕ) : ℝ :=
  (-1 / 4 : ℝ) ^ i

theorem semilocalFirstEulerMonomialHankelEntry_even_rankOne (i j : ℕ) :
    semilocalFirstEulerMonomialHankelEntry (2 * i) (2 * j) =
      2 * semilocalFirstEulerEvenMonomialRay i *
        semilocalFirstEulerEvenMonomialRay j := by
  rw [semilocalFirstEulerMonomialHankelEntry_even_even]
  unfold semilocalFirstEulerEvenMomentCoefficient
    semilocalFirstEulerEvenMonomialRay
  have hpow (k : ℕ) :
      (-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k) =
        (-1 / 4 : ℝ) ^ k := by
    calc
      (-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k) =
          (-1 : ℝ) ^ k * ((1 / 2 : ℝ) ^ (2 : ℕ)) ^ k := by
            rw [← pow_mul]
      _ = ((-1 : ℝ) * (1 / 2 : ℝ) ^ (2 : ℕ)) ^ k := by
            rw [mul_pow]
      _ = (-1 / 4 : ℝ) ^ k := by norm_num
  rw [show 2 * (i + j) = 2 * i + 2 * j by omega, pow_add, pow_add]
  calc
    2 * ((-1 : ℝ) ^ i * (-1 : ℝ) ^ j) *
        ((1 / 2 : ℝ) ^ (2 * i) * (1 / 2 : ℝ) ^ (2 * j)) =
      2 * ((-1 : ℝ) ^ i * (1 / 2 : ℝ) ^ (2 * i)) *
        ((-1 : ℝ) ^ j * (1 / 2 : ℝ) ^ (2 * j)) := by ring
    _ = _ := by rw [hpow, hpow]

theorem semilocalFirstEulerMonomialHankelEntry_odd_rankOne (i j : ℕ) :
    semilocalFirstEulerMonomialHankelEntry (2 * i + 1) (2 * j + 1) =
      -(1 / 2 : ℝ) * semilocalFirstEulerOddMonomialRay i *
        semilocalFirstEulerOddMonomialRay j := by
  rw [semilocalFirstEulerMonomialHankelEntry_odd_odd]
  unfold semilocalFirstEulerEvenMomentCoefficient
    semilocalFirstEulerOddMonomialRay
  have hpow (k : ℕ) :
      (-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k) =
        (-1 / 4 : ℝ) ^ k := by
    calc
      (-1 : ℝ) ^ k * (1 / 2 : ℝ) ^ (2 * k) =
          (-1 : ℝ) ^ k * ((1 / 2 : ℝ) ^ (2 : ℕ)) ^ k := by
            rw [← pow_mul]
      _ = ((-1 : ℝ) * (1 / 2 : ℝ) ^ (2 : ℕ)) ^ k := by
            rw [mul_pow]
      _ = (-1 / 4 : ℝ) ^ k := by norm_num
  calc
    2 * (-1 : ℝ) ^ (i + j + 1) *
        (1 / 2 : ℝ) ^ (2 * (i + j + 1)) =
      2 * ((-1 : ℝ) ^ (i + j + 1) *
        (1 / 2 : ℝ) ^ (2 * (i + j + 1))) := by ring
    _ = 2 * (-1 / 4 : ℝ) ^ (i + j + 1) := by rw [hpow]
    _ = _ := by rw [pow_add, pow_succ]; ring

/-- The published `ℓ = 0` orthonormal evaluation vector
`η₀(m) = 2⁻ᵐ √((2m)!)/m!`. -/
def semilocalFirstEulerOrthonormalEvaluation (m : ℕ) : ℝ :=
  semilocalArchimedeanJacobiNormalization m

theorem semilocalFirstEulerOrthonormalEvaluation_sq (m : ℕ) :
    semilocalFirstEulerOrthonormalEvaluation m ^ (2 : ℕ) =
      normalizedCentralBinom m := by
  exact semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom m

theorem tangentVectorEntry_eq_orthonormalEvaluation (m : ℕ) :
    tangentVectorEntry m =
      semilocalFirstEulerOrthonormalEvaluation m := by
  have hleft := Real.sqrt_nonneg (normalizedCentralBinom m)
  have hright := (semilocalArchimedeanJacobiNormalization_pos m).le
  have hsquareLeft := tangentVectorEntry_sq m
  have hsquareRight := semilocalFirstEulerOrthonormalEvaluation_sq m
  unfold tangentVectorEntry semilocalFirstEulerOrthonormalEvaluation at *
  nlinarith

/-- Published similarity-coordinate form of the source tangent: the even and odd `ℓ = 0`
evaluation rays occur with coefficients `+2√2` and `-2√2`. -/
def semilocalPublishedFirstEulerOrthonormalTangent (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j =>
    if i.val % 2 = j.val % 2 then
      2 * Real.sqrt 2 * (-1 : ℝ) ^ i.val *
        semilocalFirstEulerOrthonormalEvaluation i.val *
        semilocalFirstEulerOrthonormalEvaluation j.val
    else 0

theorem normalizedHankelTangent_eq_publishedSourceTangent (n : ℕ) :
    normalizedHankelTangent n =
      semilocalPublishedFirstEulerOrthonormalTangent n := by
  funext i j
  unfold normalizedHankelTangent semilocalPublishedFirstEulerOrthonormalTangent
  rw [tangentVectorEntry_eq_orthonormalEvaluation,
    tangentVectorEntry_eq_orthonormalEvaluation]

theorem trace_normalizedHankelTangent (n : ℕ) :
    (normalizedHankelTangent n).trace =
      normalizedHankelDeterminantJet n := by
  have hdiag (i : Fin (n + 1)) :
      normalizedHankelTangent n i i =
        2 * Real.sqrt 2 * signedCentralBinom i.val := by
    unfold normalizedHankelTangent signedCentralBinom
    rw [if_pos rfl]
    calc
      2 * Real.sqrt 2 * (-1 : ℝ) ^ i.val *
            tangentVectorEntry i.val * tangentVectorEntry i.val =
          2 * Real.sqrt 2 * (-1 : ℝ) ^ i.val *
            (tangentVectorEntry i.val ^ (2 : ℕ)) := by ring
      _ = 2 * Real.sqrt 2 * ((-1 : ℝ) ^ i.val *
            normalizedCentralBinom i.val) := by
              rw [tangentVectorEntry_sq]
              ring
  calc
    (normalizedHankelTangent n).trace
        = ∑ i : Fin (n + 1), 2 * Real.sqrt 2 *
            signedCentralBinom i.val := by
              rw [Matrix.trace]
              exact Finset.sum_congr rfl (fun i _ => hdiag i)
    _ = ∑ j ∈ Finset.range (n + 1), 2 * Real.sqrt 2 *
          signedCentralBinom j := by
            exact Fin.sum_univ_eq_sum_range
              (fun j : ℕ => 2 * Real.sqrt 2 * signedCentralBinom j) (n + 1)
    _ = normalizedHankelDeterminantJet n := by
          unfold normalizedHankelDeterminantJet
          rw [Finset.mul_sum]

/-- Any genuine normalized source matrix path with the published entrywise first Euler tangent has
the same determinant jet.  Higher `q`-coefficients are irrelevant; this is the bridge from the
literal semilocal moment matrix to the first-order determinant model used below. -/
theorem hasDerivAt_det_of_publishedSourceTangent
    (n : ℕ)
    (A : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hzero : A 0 = 1)
    (hentry : ∀ i j,
      HasDerivAt (fun q => A q i j) (normalizedHankelTangent n i j) 0) :
    HasDerivAt (fun q => (A q).det)
      (normalizedHankelDeterminantJet n) 0 := by
  have hdet := hasDerivAt_matrixDet A (normalizedHankelTangent n) 0 hentry
  refine hdet.congr_deriv ?_
  rw [hzero, detFirstJet_eq_det_mul_trace_inv_mul
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (normalizedHankelTangent n) (by simp)]
  simp [trace_normalizedHankelTangent]

/-- Determinant provenance of the source jet: the derivative is the trace of the exact rank-two
Euler tangent, hence the signed central-binomial partial sum. -/
theorem hasDerivAt_normalizedHankelDeterminantPath (n : ℕ) :
    HasDerivAt (normalizedHankelDeterminantPath n)
      (normalizedHankelDeterminantJet n) 0 := by
  change HasDerivAt
    (fun q : ℝ => (1 + q • normalizedHankelTangent n).det)
    (normalizedHankelDeterminantJet n) 0
  rw [← trace_normalizedHankelTangent]
  exact hasDerivAt_det_one_add_smul (normalizedHankelTangent n)

@[simp]
theorem normalizedHankelDeterminantPath_zero (n : ℕ) :
    normalizedHankelDeterminantPath n 0 = 1 := by
  simp [normalizedHankelDeterminantPath]

/-- The formal predecessor determinant `Δ₋₁ = 1`, followed by the actual determinants. -/
def previousNormalizedHankelDeterminantPath : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, q => normalizedHankelDeterminantPath n q

/-- First jet of the predecessor determinant, with the formal `Δ₋₁` jet equal to zero. -/
def previousNormalizedHankelDeterminantJet : ℕ → ℝ
  | 0 => 0
  | n + 1 => normalizedHankelDeterminantJet n

@[simp]
theorem previousNormalizedHankelDeterminantPath_zero (n : ℕ) :
    previousNormalizedHankelDeterminantPath n 0 = 1 := by
  cases n <;> simp [previousNormalizedHankelDeterminantPath]

theorem hasDerivAt_previousNormalizedHankelDeterminantPath (n : ℕ) :
    HasDerivAt (previousNormalizedHankelDeterminantPath n)
      (previousNormalizedHankelDeterminantJet n) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0
      exact hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))
  | succ n =>
      change HasDerivAt (normalizedHankelDeterminantPath n)
        (normalizedHankelDeterminantJet n) 0
      exact hasDerivAt_normalizedHankelDeterminantPath n

theorem normalizedHankelDeterminantJet_succ_sub (n : ℕ) :
    normalizedHankelDeterminantJet (n + 1) -
        normalizedHankelDeterminantJet n =
      2 * Real.sqrt 2 * signedCentralBinom (n + 1) := by
  unfold normalizedHankelDeterminantJet
  rw [Finset.sum_range_succ]
  ring

theorem normalizedHankelDeterminantJet_sub_previous (n : ℕ) :
    normalizedHankelDeterminantJet n -
        previousNormalizedHankelDeterminantJet n =
      2 * Real.sqrt 2 * signedCentralBinom n := by
  cases n with
  | zero =>
      norm_num [normalizedHankelDeterminantJet,
        previousNormalizedHankelDeterminantJet, signedCentralBinom,
        normalizedCentralBinom]
  | succ n =>
      simpa [previousNormalizedHankelDeterminantJet] using
        normalizedHankelDeterminantJet_succ_sub n

/-- Archimedean squared Jacobi radius. -/
def archimedeanSquaredRadius (n : ℕ) : ℝ :=
  ((n : ℝ) + 1 / 2) * ((n : ℝ) + 1)

theorem archimedeanSquaredRadius_pos (n : ℕ) :
    0 < archimedeanSquaredRadius n := by
  unfold archimedeanSquaredRadius
  positivity

theorem archimedeanSquaredRadius_eq_coefficient_sq (n : ℕ) :
    archimedeanSquaredRadius n =
      semilocalArchimedeanJacobiCoefficient n ^ (2 : ℕ) := by
  rw [semilocalArchimedeanJacobiCoefficient_sq]
  rfl

/-- Literal determinant-quotient path for the squared Jacobi radius:
`aₙ(q)² = aₙ(0)² Δₙ₋₁(q) Δₙ₊₁(q) / Δₙ(q)²`. -/
def squaredJacobiRadiusPath (n : ℕ) (q : ℝ) : ℝ :=
  archimedeanSquaredRadius n *
    (previousNormalizedHankelDeterminantPath n q *
      normalizedHankelDeterminantPath (n + 1) q /
        normalizedHankelDeterminantPath n q ^ (2 : ℕ))

/-- Exact first Euler jet of the squared Jacobi radius. -/
def squaredJacobiRadiusJet (n : ℕ) : ℝ :=
  archimedeanSquaredRadius n * 2 * Real.sqrt 2 *
    (signedCentralBinom (n + 1) - signedCentralBinom n)

@[simp]
theorem squaredJacobiRadiusPath_zero (n : ℕ) :
    squaredJacobiRadiusPath n 0 = archimedeanSquaredRadius n := by
  simp [squaredJacobiRadiusPath]

theorem hasDerivAt_squaredJacobiRadiusPath (n : ℕ) :
    HasDerivAt (squaredJacobiRadiusPath n)
      (squaredJacobiRadiusJet n) 0 := by
  have hprev := hasDerivAt_previousNormalizedHankelDeterminantPath n
  have hnext := hasDerivAt_normalizedHankelDeterminantPath (n + 1)
  have hcurrent := hasDerivAt_normalizedHankelDeterminantPath n
  have hquot := (hprev.mul hnext).div (hcurrent.pow 2) (by
    simp [normalizedHankelDeterminantPath_zero])
  have hscaled := hquot.const_mul (archimedeanSquaredRadius n)
  change HasDerivAt
    (fun q : ℝ => archimedeanSquaredRadius n *
      ((previousNormalizedHankelDeterminantPath n *
        normalizedHankelDeterminantPath (n + 1) /
          normalizedHankelDeterminantPath n ^ (2 : ℕ)) q))
    (squaredJacobiRadiusJet n) 0
  refine hscaled.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply,
    previousNormalizedHankelDeterminantPath_zero,
    normalizedHankelDeterminantPath_zero, one_pow, mul_one, one_mul,
    Nat.cast_ofNat, div_one]
  rw [show previousNormalizedHankelDeterminantJet n +
        normalizedHankelDeterminantJet (n + 1) -
        2 * normalizedHankelDeterminantJet n =
      (normalizedHankelDeterminantJet (n + 1) -
        normalizedHankelDeterminantJet n) -
      (normalizedHankelDeterminantJet n -
        previousNormalizedHankelDeterminantJet n) by ring,
    normalizedHankelDeterminantJet_succ_sub,
    normalizedHankelDeterminantJet_sub_previous]
  unfold squaredJacobiRadiusJet
  ring

/-- Positive square-root path for the Jacobi radius. -/
def jacobiRadiusPath (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (squaredJacobiRadiusPath n q)

/-- Exact first Euler jet of the positive Jacobi radius. -/
def jacobiRadiusJet (n : ℕ) : ℝ :=
  squaredJacobiRadiusJet n /
    (2 * semilocalArchimedeanJacobiCoefficient n)

@[simp]
theorem jacobiRadiusPath_zero (n : ℕ) :
    jacobiRadiusPath n 0 = semilocalArchimedeanJacobiCoefficient n := by
  unfold jacobiRadiusPath semilocalArchimedeanJacobiCoefficient
  rw [squaredJacobiRadiusPath_zero]
  rfl

theorem hasDerivAt_jacobiRadiusPath (n : ℕ) :
    HasDerivAt (jacobiRadiusPath n) (jacobiRadiusJet n) 0 := by
  have hpos : 0 < squaredJacobiRadiusPath n 0 := by
    rw [squaredJacobiRadiusPath_zero]
    exact archimedeanSquaredRadius_pos n
  have hsqrt := (hasDerivAt_squaredJacobiRadiusPath n).sqrt
    hpos.ne'
  change HasDerivAt (fun q : ℝ => Real.sqrt (squaredJacobiRadiusPath n q))
    (jacobiRadiusJet n) 0
  refine hsqrt.congr_deriv ?_
  unfold jacobiRadiusJet
  rw [show Real.sqrt (squaredJacobiRadiusPath n 0) =
      semilocalArchimedeanJacobiCoefficient n by
    simpa [jacobiRadiusPath] using jacobiRadiusPath_zero n]

theorem jacobiRadiusJet_eq (n : ℕ) :
    jacobiRadiusJet n =
      Real.sqrt 2 * semilocalArchimedeanJacobiCoefficient n *
        (signedCentralBinom (n + 1) - signedCentralBinom n) := by
  have hr := (semilocalArchimedeanJacobiCoefficient_pos n).ne'
  unfold jacobiRadiusJet squaredJacobiRadiusJet
  rw [archimedeanSquaredRadius_eq_coefficient_sq]
  field_simp

/-- Four-radius Route-J critical residual along the determinant-provenance Euler path. -/
def criticalResidualPath (n : ℕ) (q : ℝ) : ℝ :=
  routeJProlateSourceCriticalResidual
    (jacobiRadiusPath (2 * n) q)
    (jacobiRadiusPath (2 * n + 1) q)
    (jacobiRadiusPath (2 * n + 2) q)
    (jacobiRadiusPath (2 * n + 3) q)

/-- Exact first Euler jet of the four-radius Route-J critical residual. -/
def criticalResidualJet (n : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  jacobiRadiusJet (2 * n) * r (2 * n + 1) +
      r (2 * n) * jacobiRadiusJet (2 * n + 1) -
      2 * r (2 * n + 1) * jacobiRadiusJet (2 * n + 1) -
      2 * r (2 * n + 2) * jacobiRadiusJet (2 * n + 2) +
      jacobiRadiusJet (2 * n + 2) * r (2 * n + 3) +
      r (2 * n + 2) * jacobiRadiusJet (2 * n + 3)

theorem hasDerivAt_criticalResidualPath (n : ℕ) :
    HasDerivAt (criticalResidualPath n) (criticalResidualJet n) 0 := by
  have h₀ := hasDerivAt_jacobiRadiusPath (2 * n)
  have h₁ := hasDerivAt_jacobiRadiusPath (2 * n + 1)
  have h₂ := hasDerivAt_jacobiRadiusPath (2 * n + 2)
  have h₃ := hasDerivAt_jacobiRadiusPath (2 * n + 3)
  have h := (((h₀.mul h₁).sub (h₁.pow 2)).sub (h₂.pow 2)).add (h₂.mul h₃)
  change HasDerivAt
    (jacobiRadiusPath (2 * n) * jacobiRadiusPath (2 * n + 1) -
      jacobiRadiusPath (2 * n + 1) ^ (2 : ℕ) -
      jacobiRadiusPath (2 * n + 2) ^ (2 : ℕ) +
      jacobiRadiusPath (2 * n + 2) * jacobiRadiusPath (2 * n + 3))
    (criticalResidualJet n) 0
  refine h.congr_deriv ?_
  simp only [jacobiRadiusPath_zero, Nat.cast_ofNat]
  unfold criticalResidualJet
  ring

/-- Formal predecessor for an arbitrary normalized determinant family. -/
def previousDeterminantPathOf (Δ : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, q => Δ n q

/-- Squared Jacobi-radius quotient attached to an arbitrary normalized determinant family. -/
def squaredJacobiRadiusPathOf (Δ : ℕ → ℝ → ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  archimedeanSquaredRadius n *
    (previousDeterminantPathOf Δ n q * Δ (n + 1) q / Δ n q ^ (2 : ℕ))

/-- Positive Jacobi-radius path attached to an arbitrary normalized determinant family. -/
def jacobiRadiusPathOf (Δ : ℕ → ℝ → ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (squaredJacobiRadiusPathOf Δ n q)

/-- Four-radius critical residual attached to an arbitrary normalized determinant family. -/
def criticalResidualPathOf (Δ : ℕ → ℝ → ℝ) (n : ℕ) (q : ℝ) : ℝ :=
  routeJProlateSourceCriticalResidual
    (jacobiRadiusPathOf Δ (2 * n) q)
    (jacobiRadiusPathOf Δ (2 * n + 1) q)
    (jacobiRadiusPathOf Δ (2 * n + 2) q)
    (jacobiRadiusPathOf Δ (2 * n + 3) q)

theorem hasDerivAt_previousDeterminantPathOf
    (Δ : ℕ → ℝ → ℝ)
    (hΔ : ∀ n, HasDerivAt (Δ n) (normalizedHankelDeterminantJet n) 0)
    (n : ℕ) :
    HasDerivAt (previousDeterminantPathOf Δ n)
      (previousNormalizedHankelDeterminantJet n) 0 := by
  cases n with
  | zero =>
      change HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0
      exact hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))
  | succ n =>
      change HasDerivAt (Δ n) (normalizedHankelDeterminantJet n) 0
      exact hΔ n

@[simp]
theorem previousDeterminantPathOf_zero
    (Δ : ℕ → ℝ → ℝ) (hzero : ∀ n, Δ n 0 = 1) (n : ℕ) :
    previousDeterminantPathOf Δ n 0 = 1 := by
  cases n with
  | zero => rfl
  | succ n =>
      change Δ n 0 = 1
      exact hzero n

theorem hasDerivAt_squaredJacobiRadiusPathOf
    (Δ : ℕ → ℝ → ℝ)
    (hzero : ∀ n, Δ n 0 = 1)
    (hΔ : ∀ n, HasDerivAt (Δ n) (normalizedHankelDeterminantJet n) 0)
    (n : ℕ) :
    HasDerivAt (squaredJacobiRadiusPathOf Δ n)
      (squaredJacobiRadiusJet n) 0 := by
  have hprev := hasDerivAt_previousDeterminantPathOf Δ hΔ n
  have hnext := hΔ (n + 1)
  have hcurrent := hΔ n
  have hquot := (hprev.mul hnext).div (hcurrent.pow 2) (by
    simp [hzero])
  have hscaled := hquot.const_mul (archimedeanSquaredRadius n)
  change HasDerivAt
    (fun q : ℝ => archimedeanSquaredRadius n *
      ((previousDeterminantPathOf Δ n * Δ (n + 1) / Δ n ^ (2 : ℕ)) q))
    (squaredJacobiRadiusJet n) 0
  refine hscaled.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply,
    previousDeterminantPathOf_zero Δ hzero, hzero, one_pow, mul_one,
    one_mul, Nat.cast_ofNat, div_one]
  rw [show previousNormalizedHankelDeterminantJet n +
        normalizedHankelDeterminantJet (n + 1) -
        2 * normalizedHankelDeterminantJet n =
      (normalizedHankelDeterminantJet (n + 1) -
        normalizedHankelDeterminantJet n) -
      (normalizedHankelDeterminantJet n -
        previousNormalizedHankelDeterminantJet n) by ring,
    normalizedHankelDeterminantJet_succ_sub,
    normalizedHankelDeterminantJet_sub_previous]
  unfold squaredJacobiRadiusJet
  ring

@[simp]
theorem squaredJacobiRadiusPathOf_zero
    (Δ : ℕ → ℝ → ℝ) (hzero : ∀ n, Δ n 0 = 1) (n : ℕ) :
    squaredJacobiRadiusPathOf Δ n 0 = archimedeanSquaredRadius n := by
  simp [squaredJacobiRadiusPathOf, hzero]

@[simp]
theorem jacobiRadiusPathOf_zero
    (Δ : ℕ → ℝ → ℝ) (hzero : ∀ n, Δ n 0 = 1) (n : ℕ) :
    jacobiRadiusPathOf Δ n 0 =
      semilocalArchimedeanJacobiCoefficient n := by
  unfold jacobiRadiusPathOf semilocalArchimedeanJacobiCoefficient
  rw [squaredJacobiRadiusPathOf_zero Δ hzero]
  rfl

theorem hasDerivAt_jacobiRadiusPathOf
    (Δ : ℕ → ℝ → ℝ)
    (hzero : ∀ n, Δ n 0 = 1)
    (hΔ : ∀ n, HasDerivAt (Δ n) (normalizedHankelDeterminantJet n) 0)
    (n : ℕ) :
    HasDerivAt (jacobiRadiusPathOf Δ n) (jacobiRadiusJet n) 0 := by
  have hpos : 0 < squaredJacobiRadiusPathOf Δ n 0 := by
    rw [squaredJacobiRadiusPathOf_zero Δ hzero]
    exact archimedeanSquaredRadius_pos n
  have hsqrt := (hasDerivAt_squaredJacobiRadiusPathOf Δ hzero hΔ n).sqrt hpos.ne'
  change HasDerivAt
    (fun q : ℝ => Real.sqrt (squaredJacobiRadiusPathOf Δ n q))
    (jacobiRadiusJet n) 0
  refine hsqrt.congr_deriv ?_
  unfold jacobiRadiusJet
  rw [show Real.sqrt (squaredJacobiRadiusPathOf Δ n 0) =
      semilocalArchimedeanJacobiCoefficient n by
    simpa [jacobiRadiusPathOf] using jacobiRadiusPathOf_zero Δ hzero n]

/-- Universal first-order transfer theorem.  Every normalized determinant family with the literal
published source jets has the same Route-J critical jet, regardless of all higher Euler terms. -/
theorem hasDerivAt_criticalResidualPathOf
    (Δ : ℕ → ℝ → ℝ)
    (hzero : ∀ n, Δ n 0 = 1)
    (hΔ : ∀ n, HasDerivAt (Δ n) (normalizedHankelDeterminantJet n) 0)
    (n : ℕ) :
    HasDerivAt (criticalResidualPathOf Δ n) (criticalResidualJet n) 0 := by
  have h₀ := hasDerivAt_jacobiRadiusPathOf Δ hzero hΔ (2 * n)
  have h₁ := hasDerivAt_jacobiRadiusPathOf Δ hzero hΔ (2 * n + 1)
  have h₂ := hasDerivAt_jacobiRadiusPathOf Δ hzero hΔ (2 * n + 2)
  have h₃ := hasDerivAt_jacobiRadiusPathOf Δ hzero hΔ (2 * n + 3)
  have h := (((h₀.mul h₁).sub (h₁.pow 2)).sub (h₂.pow 2)).add (h₂.mul h₃)
  change HasDerivAt
    (jacobiRadiusPathOf Δ (2 * n) * jacobiRadiusPathOf Δ (2 * n + 1) -
      jacobiRadiusPathOf Δ (2 * n + 1) ^ (2 : ℕ) -
      jacobiRadiusPathOf Δ (2 * n + 2) ^ (2 : ℕ) +
      jacobiRadiusPathOf Δ (2 * n + 2) * jacobiRadiusPathOf Δ (2 * n + 3))
    (criticalResidualJet n) 0
  refine h.congr_deriv ?_
  simp only [jacobiRadiusPathOf_zero Δ hzero, Nat.cast_ofNat]
  unfold criticalResidualJet
  ring

/-- One-step ratio `cₙ₊₁/cₙ` of the unsigned normalized central-binomial coefficients. -/
def centralBinomRatio (n : ℕ) : ℝ :=
  (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)

/-- Sum `1 + cₙ₊₁/cₙ`, which controls the signed first Euler radius jet. -/
def centralBinomJumpFactor (n : ℕ) : ℝ :=
  (4 * (n : ℝ) + 3) / (2 * (n : ℝ) + 2)

theorem normalizedCentralBinom_succ_eq_ratio (n : ℕ) :
    normalizedCentralBinom (n + 1) =
      normalizedCentralBinom n * centralBinomRatio n := by
  unfold normalizedCentralBinom centralBinomRatio
  rw [pow_succ]
  have hcb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [h4, hn]
  linear_combination 2 * hcb

theorem signedCentralBinom_succ_sub (n : ℕ) :
    signedCentralBinom (n + 1) - signedCentralBinom n =
      (-1 : ℝ) ^ (n + 1) * centralBinomJumpFactor n *
        normalizedCentralBinom n := by
  rw [signedCentralBinom, signedCentralBinom,
    normalizedCentralBinom_succ_eq_ratio, pow_succ]
  unfold centralBinomRatio centralBinomJumpFactor
  have hn : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn]
  ring

/-- Positive amplitude of the alternating first Euler radius jet. -/
def positiveEulerRadiusJet (n : ℕ) : ℝ :=
  Real.sqrt 2 * semilocalArchimedeanJacobiCoefficient n *
    centralBinomJumpFactor n * normalizedCentralBinom n

theorem jacobiRadiusJet_eq_signed_positive (n : ℕ) :
    jacobiRadiusJet n = (-1 : ℝ) ^ (n + 1) *
      positiveEulerRadiusJet n := by
  rw [jacobiRadiusJet_eq, signedCentralBinom_succ_sub]
  unfold positiveEulerRadiusJet
  ring

theorem jacobiRadiusJet_even (n : ℕ) :
    jacobiRadiusJet (2 * n) = -positiveEulerRadiusJet (2 * n) := by
  rw [jacobiRadiusJet_eq_signed_positive]
  norm_num [pow_add, pow_mul]

theorem jacobiRadiusJet_odd (n : ℕ) :
    jacobiRadiusJet (2 * n + 1) = positiveEulerRadiusJet (2 * n + 1) := by
  rw [jacobiRadiusJet_eq_signed_positive]
  norm_num [pow_add, pow_mul]

/-- Exact coefficient left after factoring `√2 cₘ` from the even-start four-radius jet. -/
def criticalBracket (m : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  r m * r (m + 1) *
      (centralBinomRatio m * centralBinomJumpFactor (m + 1) -
        centralBinomJumpFactor m) +
    r (m + 2) * r (m + 3) *
      centralBinomRatio m * centralBinomRatio (m + 1) *
      (centralBinomRatio (m + 2) * centralBinomJumpFactor (m + 3) -
        centralBinomJumpFactor (m + 2)) +
    2 * (r (m + 2) ^ (2 : ℕ) * centralBinomRatio m *
        centralBinomRatio (m + 1) * centralBinomJumpFactor (m + 2) -
      r (m + 1) ^ (2 : ℕ) * centralBinomRatio m *
        centralBinomJumpFactor (m + 1))

/-- Determinant-provenance factorization of the full critical residual jet. -/
theorem criticalResidualJet_eq_centralBinom_mul_bracket (n : ℕ) :
    criticalResidualJet n =
      Real.sqrt 2 * normalizedCentralBinom (2 * n) *
        criticalBracket (2 * n) := by
  have heven : 2 * n + 2 = 2 * (n + 1) := by omega
  have hodd : 2 * n + 3 = 2 * (n + 1) + 1 := by omega
  have hc₁ :
      normalizedCentralBinom (2 * n + 1) =
        normalizedCentralBinom (2 * n) * centralBinomRatio (2 * n) := by
    simpa using normalizedCentralBinom_succ_eq_ratio (2 * n)
  have hc₂ :
      normalizedCentralBinom (2 * n + 2) =
        normalizedCentralBinom (2 * n) * centralBinomRatio (2 * n) *
          centralBinomRatio (2 * n + 1) := by
    calc
      normalizedCentralBinom (2 * n + 2) =
          normalizedCentralBinom (2 * n + 1) *
            centralBinomRatio (2 * n + 1) := by
              simpa using normalizedCentralBinom_succ_eq_ratio (2 * n + 1)
      _ = _ := by rw [hc₁]
  have hc₃ :
      normalizedCentralBinom (2 * n + 3) =
        normalizedCentralBinom (2 * n) * centralBinomRatio (2 * n) *
          centralBinomRatio (2 * n + 1) *
          centralBinomRatio (2 * n + 2) := by
    calc
      normalizedCentralBinom (2 * n + 3) =
          normalizedCentralBinom (2 * n + 2) *
            centralBinomRatio (2 * n + 2) := by
              simpa using normalizedCentralBinom_succ_eq_ratio (2 * n + 2)
      _ = _ := by rw [hc₂]
  unfold criticalResidualJet
  rw [jacobiRadiusJet_even n, jacobiRadiusJet_odd n, heven, hodd,
    jacobiRadiusJet_even (n + 1), jacobiRadiusJet_odd (n + 1)]
  rw [← hodd, ← heven]
  unfold positiveEulerRadiusJet criticalBracket
  rw [hc₁, hc₂, hc₃]
  ring

/-- Closed form of the bracket: two square-root cross terms and one rational curvature term. -/
def criticalBracketClosed (m : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  0 - (r m * r (m + 1) * (4 * (m : ℝ) + 5) /
      ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 4))) -
    r (m + 2) * r (m + 3) *
      centralBinomRatio m * centralBinomRatio (m + 1) *
      (4 * (m : ℝ) + 13) /
        ((2 * (m : ℝ) + 6) * (2 * (m : ℝ) + 8)) +
    3 * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3) *
      (4 * (m : ℝ) + 9) /
        (2 * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 4))

theorem criticalBracket_eq_closed (m : ℕ) :
    criticalBracket m = criticalBracketClosed m := by
  unfold criticalBracket criticalBracketClosed centralBinomRatio
    centralBinomJumpFactor
  dsimp only
  push_cast
  rw [semilocalArchimedeanJacobiCoefficient_sq,
    semilocalArchimedeanJacobiCoefficient_sq]
  push_cast
  have h₂ : 2 * (m : ℝ) + 2 ≠ 0 := by positivity
  have h₄ : 2 * (m : ℝ) + 4 ≠ 0 := by positivity
  have h₆ : 2 * (m : ℝ) + 6 ≠ 0 := by positivity
  have h₈ : 2 * (m : ℝ) + 8 ≠ 0 := by positivity
  field_simp [h₂, h₄, h₆, h₈]
  ring

/-- Archimedean Jacobi radius divided by its natural affine scale. -/
theorem semilocalArchimedeanJacobiCoefficient_div_succ (n : ℕ) :
    semilocalArchimedeanJacobiCoefficient n / ((n : ℝ) + 1) =
      Real.sqrt ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) := by
  have hleft : 0 ≤ semilocalArchimedeanJacobiCoefficient n / ((n : ℝ) + 1) :=
    div_nonneg (semilocalArchimedeanJacobiCoefficient_pos n).le (by positivity)
  have hratio : 0 ≤ (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by positivity
  have hright : 0 ≤ Real.sqrt ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) :=
    Real.sqrt_nonneg _
  have hsquareLeft :
      (semilocalArchimedeanJacobiCoefficient n / ((n : ℝ) + 1)) ^ (2 : ℕ) =
        (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
    rw [div_pow, semilocalArchimedeanJacobiCoefficient_sq]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
  have hsquareRight :
      Real.sqrt ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) ^ (2 : ℕ) =
        (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) :=
    Real.sq_sqrt hratio
  nlinarith

theorem tendsto_semilocalArchimedeanJacobiCoefficient_div_succ :
    Tendsto
      (fun n : ℕ =>
        semilocalArchimedeanJacobiCoefficient n / ((n : ℝ) + 1))
      atTop (nhds 1) := by
  have hratio :
      Tendsto
        (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))
        atTop (nhds 1) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (1 : ℝ) 2 2 (by norm_num : (2 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  convert hsqrt using 1
  · funext n
    rw [semilocalArchimedeanJacobiCoefficient_div_succ]
    rfl
  · norm_num

theorem tendsto_centralBinomRatio :
    Tendsto centralBinomRatio atTop (nhds 1) := by
  unfold centralBinomRatio
  convert
    (tendsto_add_mul_div_add_mul_atTop_nhds
      (1 : ℝ) 2 2 (by norm_num : (2 : ℝ) ≠ 0)) using 1
  · funext n
    ring
  · norm_num

/-- First negative cross contribution to the closed critical bracket. -/
def criticalBracketFirstCross (m : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  0 - r m * r (m + 1) * (4 * (m : ℝ) + 5) /
    ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 4))

/-- Second negative cross contribution to the closed critical bracket. -/
def criticalBracketSecondCross (m : ℕ) : ℝ :=
  let r := semilocalArchimedeanJacobiCoefficient
  0 - r (m + 2) * r (m + 3) *
    centralBinomRatio m * centralBinomRatio (m + 1) *
    (4 * (m : ℝ) + 13) /
      ((2 * (m : ℝ) + 6) * (2 * (m : ℝ) + 8))

/-- Positive rational curvature contribution to the closed critical bracket. -/
def criticalBracketCurvature (m : ℕ) : ℝ :=
  3 * (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 3) *
    (4 * (m : ℝ) + 9) /
      (2 * (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 4))

theorem criticalBracket_eq_three_contributions (m : ℕ) :
    criticalBracket m =
      criticalBracketFirstCross m +
        criticalBracketSecondCross m +
        criticalBracketCurvature m := by
  rw [criticalBracket_eq_closed]
  unfold criticalBracketClosed criticalBracketFirstCross
    criticalBracketSecondCross criticalBracketCurvature
  dsimp only
  ring

theorem criticalBracket_div_eq_three_contributions (m : ℕ) :
    criticalBracket m / (m : ℝ) =
      criticalBracketFirstCross m / (m : ℝ) +
        criticalBracketSecondCross m / (m : ℝ) +
        criticalBracketCurvature m / (m : ℝ) := by
  rw [criticalBracket_eq_three_contributions]
  ring

theorem tendsto_criticalBracketFirstCross_div :
    Tendsto
      (fun n : ℕ =>
        criticalBracketFirstCross (n + 1) / ((n : ℝ) + 1))
      atTop (nhds (-1)) := by
  have hr₀ :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (tendsto_add_atTop_nat 1)
  have hr₁ :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (tendsto_add_atTop_nat 2)
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (4 * ((n : ℝ) + 1) + 5) / (4 * ((n : ℝ) + 1)))
        atTop (nhds 1) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (9 : ℝ) 4 4 (by norm_num : (4 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hproduct := ((hr₀.mul hr₁).mul hratio).neg
  apply Filter.Tendsto.congr' _ (by simpa only [one_mul] using hproduct)
  exact Filter.Eventually.of_forall (fun n => by
    simp only [Function.comp_apply]
    unfold criticalBracketFirstCross
    dsimp only
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn₂ : (n : ℝ) + 2 ≠ 0 := by positivity
    have hn₃ : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hn, hn₂, hn₃]
    ring)

theorem tendsto_criticalBracketSecondCross_div :
    Tendsto
      (fun n : ℕ =>
        criticalBracketSecondCross (n + 1) / ((n : ℝ) + 1))
      atTop (nhds (-1)) := by
  have hr₂ :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (tendsto_add_atTop_nat 3)
  have hr₃ :=
    tendsto_semilocalArchimedeanJacobiCoefficient_div_succ.comp
      (tendsto_add_atTop_nat 4)
  have hq₀ := tendsto_centralBinomRatio.comp (tendsto_add_atTop_nat 1)
  have hq₁ := tendsto_centralBinomRatio.comp (tendsto_add_atTop_nat 2)
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (4 * ((n : ℝ) + 1) + 13) / (4 * ((n : ℝ) + 1)))
        atTop (nhds 1) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (17 : ℝ) 4 4 (by norm_num : (4 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hproduct := ((((hr₂.mul hr₃).mul hq₀).mul hq₁).mul hratio).neg
  apply Filter.Tendsto.congr' _ (by simpa only [one_mul] using hproduct)
  exact Filter.Eventually.of_forall (fun n => by
    simp only [Function.comp_apply]
    unfold criticalBracketSecondCross
    dsimp only
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn₄ : (n : ℝ) + 4 ≠ 0 := by positivity
    have hn₅ : (n : ℝ) + 5 ≠ 0 := by positivity
    field_simp [hn, hn₄, hn₅]
    ring)

theorem tendsto_criticalBracketCurvature_div :
    Tendsto
      (fun n : ℕ =>
        criticalBracketCurvature (n + 1) / ((n : ℝ) + 1))
      atTop (nhds 6) := by
  have hq₀ := tendsto_centralBinomRatio.comp (tendsto_add_atTop_nat 1)
  have hq₁ := tendsto_centralBinomRatio.comp (tendsto_add_atTop_nat 2)
  have hlast :
      Tendsto
        (fun n : ℕ =>
          (4 * ((n : ℝ) + 1) + 9) / ((n : ℝ) + 1))
        atTop (nhds 4) := by
    convert
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (13 : ℝ) 1 4 (by norm_num : (1 : ℝ) ≠ 0)) using 1
    · funext n
      ring
    · norm_num
  have hproduct := ((hq₀.mul hq₁).mul hlast).const_mul (3 / 2 : ℝ)
  norm_num at hproduct
  apply Filter.Tendsto.congr' _ hproduct
  exact Filter.Eventually.of_forall (fun n => by
    unfold criticalBracketCurvature centralBinomRatio
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn₂ : (n : ℝ) + 2 ≠ 0 := by positivity
    have hn₃ : (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hn, hn₂, hn₃]
    ring)

/-- Sharp net bracket law: the two cross terms contribute `-1` each and curvature contributes
`+6`, leaving the exact coefficient `4`. -/
theorem tendsto_criticalBracket_div :
    Tendsto
      (fun n : ℕ => criticalBracket (n + 1) / ((n : ℝ) + 1))
      atTop (nhds 4) := by
  have hsum :=
    (tendsto_criticalBracketFirstCross_div.add
      tendsto_criticalBracketSecondCross_div).add
        tendsto_criticalBracketCurvature_div
  norm_num at hsum
  apply Filter.Tendsto.congr' _ hsum
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (criticalBracket_div_eq_three_contributions (n + 1)).symm)

/-- Degree scale at which the prime Euler parameter `q = p⁻¹` first interacts non-uniformly with
the orthogonalized critical residual. -/
def criticalBoundaryDegree (n : ℕ) : ℕ :=
  2 * (n + 1)

theorem tendsto_criticalBoundaryDegree :
    Tendsto criticalBoundaryDegree atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  unfold criticalBoundaryDegree
  omega

theorem tendsto_criticalBoundaryPredecessor :
    Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

theorem tendsto_criticalBracket_boundary :
    Tendsto
      (fun n : ℕ =>
        criticalBracket (criticalBoundaryDegree n) /
          (criticalBoundaryDegree n : ℝ))
      atTop (nhds 4) := by
  have h := tendsto_criticalBracket_div.comp
    tendsto_criticalBoundaryPredecessor
  convert h using 1
  funext n
  simp only [Function.comp_apply]
  unfold criticalBoundaryDegree
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
  push_cast
  ring

theorem tendsto_centralBinom_boundary :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt (criticalBoundaryDegree n) *
          normalizedCentralBinom (criticalBoundaryDegree n))
      atTop (nhds (1 / Real.sqrt Real.pi)) := by
  exact tendsto_sqrtNat_mul_normalizedCentralBinom.comp
    tendsto_criticalBoundaryDegree

theorem criticalResidualJet_div_sqrt_eq_boundary_product (n : ℕ) :
    criticalResidualJet (n + 1) /
        Real.sqrt (criticalBoundaryDegree n) =
      Real.sqrt 2 *
        (Real.sqrt (criticalBoundaryDegree n) *
          normalizedCentralBinom (criticalBoundaryDegree n)) *
        (criticalBracket (criticalBoundaryDegree n) /
          (criticalBoundaryDegree n : ℝ)) := by
  rw [criticalResidualJet_eq_centralBinom_mul_bracket]
  have hdegree :
      2 * (n + 1) = criticalBoundaryDegree n := by
    rfl
  rw [hdegree]
  have hpos : 0 < (criticalBoundaryDegree n : ℝ) := by
    unfold criticalBoundaryDegree
    positivity
  have hsqrt : Real.sqrt (criticalBoundaryDegree n) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsquare :
      Real.sqrt (criticalBoundaryDegree n) ^ (2 : ℕ) =
        (criticalBoundaryDegree n : ℝ) :=
    Real.sq_sqrt hpos.le
  field_simp [hsqrt, hpos.ne']
  rw [hsquare]

/-- **Sharp determinant-provenance first-jet boundary law.**  The first Euler jet of the fully
orthogonalized four-radius critical residual grows like `4 √(2/π) √(2n)`.  Consequently its
first-order correction is order one on the scale `q √n ≍ 1`, equivalently `n ≍ p²` for
`q = p⁻¹`.  This theorem does not control higher Euler coefficients. -/
theorem tendsto_criticalResidualJet_div_sqrt_boundary :
    Tendsto
      (fun n : ℕ =>
        criticalResidualJet (n + 1) /
          Real.sqrt (criticalBoundaryDegree n))
      atTop (nhds (4 * Real.sqrt (2 / Real.pi))) := by
  have hproduct :=
    (tendsto_centralBinom_boundary.mul
      tendsto_criticalBracket_boundary).const_mul (Real.sqrt 2)
  have hconstant :
      Real.sqrt 2 * ((1 / Real.sqrt Real.pi) * 4) =
        4 * Real.sqrt (2 / Real.pi) := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2)]
    ring
  rw [hconstant] at hproduct
  apply Filter.Tendsto.congr' _ hproduct
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [mul_assoc] using
      (criticalResidualJet_div_sqrt_eq_boundary_product n).symm)

end FirstEulerCriticalJet

end RHTower
