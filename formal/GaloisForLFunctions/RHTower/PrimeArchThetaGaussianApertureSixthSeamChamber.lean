import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.RHTower.XiThetaSourceSeam
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The positive modular chamber of the Gaussian-aperture sixth seam

The Gaussian-aperture balance has its first non-universal large-aperture coefficient at the
sixth logarithmic seam jet.  Modular closure reduces that coefficient to a polynomial in one
self-dual theta scale.  This file constructs that actual source scale and proves that it lies in
the polynomial's positive chamber.

Write

`M = theta_3(i) = evenKernel 0 1`, `R = pi M^(4 : ℕ)`, and `X = R^(2 : ℕ)`.

The autonomous self-dual modular system obtained from the theta functional equation, the
modular-lambda derivative, and the Ramanujan differential equations is

`z' = -R (1-z^(2 : ℕ))`,
`R' = -(2/3) R (p+Rz)`,
`p' = 3-p^(2 : ℕ)/3+R^(2 : ℕ)(3+z^(2 : ℕ))/12`,

where `z = 2 lambda-1` and `p = pi t E_2(it)-3` are odd at the seam and `R` is even.  Exact
sixth-order elimination gives

`N_6 = M^(3 : ℕ) Q(X) / 131072`,

with `N_6 = f_0^(2 : ℕ) f_6 - 15 f_0 f_2 f_4 + 30 f_2^(3 : ℕ)` and

`Q(X) = 99X^(6 : ℕ) + 12X^(5 : ℕ) - 3160X^(4 : ℕ) - 544272X^(3 : ℕ)
        - 1446144X^(2 : ℕ) - 1509120X + 276480`.

The analytic equality with `thetaCuspGaussianApertureSixthSeamNumerator` requires the remaining
real-theta/modular-differential bridge and is deliberately not asserted here.  What is proved
unconditionally is the source-specific sign chamber needed by that bridge:

`191/10 < X` and hence `0 < Q(X)`.

The proof is non-numerical: the first positive theta term, a rational exponential-series bound,
and rigorous decimal bounds for `pi` give the strict enclosure.  Expanding `Q` about `191/10`
then leaves only positive coefficients.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial HurwitzZeta

namespace RHTower

noncomputable section

/-- The theta-nullwert at the self-dual point, in the real-kernel coordinates already used by
the completed Xi source. -/
def thetaCuspSelfDualThetaMass : ℝ := evenKernel 0 1

/-- The single modular scale left after self-dual elimination of the Gaussian-aperture seam
jets: `R = pi * theta_3(i)^(4 : ℕ)`. -/
def thetaCuspSelfDualModularScale : ℝ :=
  Real.pi * thetaCuspSelfDualThetaMass ^ (4 : ℕ)

/-- The exact polynomial selected by sixth-order elimination in the self-dual modular system. -/
def thetaCuspGaussianApertureSixthSeamModularPolynomial (X : ℝ) : ℝ :=
  99 * X ^ (6 : ℕ) + 12 * X ^ (5 : ℕ) - 3160 * X ^ (4 : ℕ) -
    544272 * X ^ (3 : ℕ) - 1446144 * X ^ (2 : ℕ) - 1509120 * X + 276480

/-- The modular-closure value predicted for the actual sixth seam numerator.  Its equality with
`thetaCuspGaussianApertureSixthSeamNumerator` is the remaining analytic bridge, not an assumption
of this file. -/
def thetaCuspGaussianApertureSixthSeamModularClosureValue : ℝ :=
  thetaCuspSelfDualThetaMass ^ (3 : ℕ) /
      131072 *
    thetaCuspGaussianApertureSixthSeamModularPolynomial
      (thetaCuspSelfDualModularScale ^ (2 : ℕ))

/-- A rational lower bound for the first theta exponential at the self-dual seam. -/
theorem exp_neg_pi_gt_four_hundred_thirty_one_div_ten_thousand :
    (431 / 10000 : ℝ) < Real.exp (-Real.pi) := by
  have hsmall :
      Real.exp (177 / 1250 : ℝ) < (11523 / 10000 : ℝ) := by
    calc
      Real.exp (177 / 1250 : ℝ) ≤
          (∑ m ∈ Finset.range 3,
              (177 / 1250 : ℝ) ^ m / m.factorial) +
            (177 / 1250 : ℝ) ^ (3 : ℕ) * (3 + 1) / (Nat.factorial 3 * 3) :=
        Real.exp_bound' (by norm_num) (by norm_num) (by norm_num)
      _ < (11523 / 10000 : ℝ) := by norm_num [Finset.sum_range_succ]
  have hpi : Real.pi < 3 + (177 / 1250 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h
  have hexpPi : Real.exp Real.pi < (10000 / 431 : ℝ) := by
    calc
      Real.exp Real.pi < Real.exp (3 + (177 / 1250 : ℝ)) :=
        Real.exp_lt_exp.mpr hpi
      _ = Real.exp 1 ^ (3 : ℕ) * Real.exp (177 / 1250 : ℝ) := by
        rw [Real.exp_add]
        congr 1
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num,
          Real.exp_add, Real.exp_add]
        ring
      _ < (2.7182818286 : ℝ) ^ (3 : ℕ) * (11523 / 10000 : ℝ) := by
        gcongr
        exact Real.exp_one_lt_d9
      _ < (10000 / 431 : ℝ) := by norm_num
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos _
  rw [show (431 / 10000 : ℝ) = (10000 / 431 : ℝ)⁻¹ by norm_num]
  simpa [one_div] using one_div_lt_one_div_of_lt hpos hexpPi

/-- The actual self-dual theta mass exceeds the first-term rational enclosure. -/
theorem thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand :
    (5431 / 5000 : ℝ) < thetaCuspSelfDualThetaMass := by
  have hs0 := hasSum_nat_cosKernel₀ 0 (by norm_num : (0 : ℝ) < 1)
  have hs : HasSum (fun n : ℕ =>
      2 * Real.exp (-Real.pi * (n + 1) ^ (2 : ℕ)))
      (evenKernel 0 1 - 1) := by
    have hs' : HasSum (fun n : ℕ =>
        2 * Real.exp (-Real.pi * (n + 1) ^ (2 : ℕ) * 1))
        (cosKernel (0 : UnitAddCircle) 1 - 1) := by
      simpa using hs0
    rw [← congrFun evenKernel_eq_cosKernel_of_zero (1 : ℝ)] at hs'
    simpa using hs'
  have hfirst := hs.summable.le_tsum 0 (fun n _ => by positivity)
  rw [hs.tsum_eq] at hfirst
  have hfirst' : 2 * Real.exp (-Real.pi) ≤ evenKernel 0 1 - 1 := by
    simpa using hfirst
  rw [thetaCuspSelfDualThetaMass]
  nlinarith [exp_neg_pi_gt_four_hundred_thirty_one_div_ten_thousand]

/-- The squared self-dual modular scale lies strictly beyond the rational sign threshold
`191/10`. -/
theorem thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one :
    (191 / 10 : ℝ) < thetaCuspSelfDualModularScale ^ (2 : ℕ) := by
  have hp : (31415 / 10000 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h
  have hm :=
    thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
  rw [thetaCuspSelfDualModularScale]
  calc
    (191 / 10 : ℝ) <
        (31415 / 10000 : ℝ) ^ (2 : ℕ) * (5431 / 5000 : ℝ) ^ (8 : ℕ) := by norm_num
    _ < Real.pi ^ (2 : ℕ) * thetaCuspSelfDualThetaMass ^ (8 : ℕ) := by gcongr
    _ = (Real.pi * thetaCuspSelfDualThetaMass ^ (4 : ℕ)) ^ (2 : ℕ) := by ring

/-- The sixth-seam modular polynomial is positive throughout the chamber selected by the actual
theta source.  Expansion at `X = 191/10` has strictly positive constant term and nonnegative
remaining monomials. -/
theorem thetaCuspGaussianApertureSixthSeamModularPolynomial_pos_of_threshold
    {X : ℝ} (hX : (191 / 10 : ℝ) ≤ X) :
    0 < thetaCuspGaussianApertureSixthSeamModularPolynomial X := by
  let y := X - (191 / 10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hXeq : X = (191 / 10 : ℝ) + y := by dsimp [y]; ring
  rw [hXeq]
  rw [show thetaCuspGaussianApertureSixthSeamModularPolynomial
        ((191 / 10 : ℝ) + y) =
      99 * y ^ (6 : ℕ) + (56787 / 5 : ℝ) * y ^ (5 : ℕ) +
        (10794577 / 20 : ℝ) * y ^ (4 : ℕ) +
        (652723289 / 50 : ℝ) * y ^ (3 : ℕ) +
        (317839252857 / 2000 : ℝ) * y ^ (2 : ℕ) +
        (38870479127747 / 50000 : ℝ) * y +
        (67989377597579 / 1000000 : ℝ) by
      unfold thetaCuspGaussianApertureSixthSeamModularPolynomial
      ring]
  positivity

/-- The actual theta self-dual scale is in the strict positive chamber of the sixth-seam modular
polynomial. -/
theorem thetaCuspGaussianApertureSixthSeamModularPolynomial_source_pos :
    0 < thetaCuspGaussianApertureSixthSeamModularPolynomial
      (thetaCuspSelfDualModularScale ^ (2 : ℕ)) :=
  thetaCuspGaussianApertureSixthSeamModularPolynomial_pos_of_threshold
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le

/-- Consequently the fully source-specialized modular-closure value for the Gaussian-aperture
sixth seam is strictly positive. -/
theorem thetaCuspGaussianApertureSixthSeamModularClosureValue_pos :
    0 < thetaCuspGaussianApertureSixthSeamModularClosureValue := by
  rw [thetaCuspGaussianApertureSixthSeamModularClosureValue]
  have hm : 0 < thetaCuspSelfDualThetaMass := by
    linarith [
      thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand]
  exact mul_pos (div_pos (pow_pos hm 3) (by norm_num))
    thetaCuspGaussianApertureSixthSeamModularPolynomial_source_pos

end

end RHTower
