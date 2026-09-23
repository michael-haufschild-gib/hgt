import GaloisForLFunctions.HTGeometry.CavityResponseConvergence
import GaloisForLFunctions.HTGeometry.CavityInteractionCoefficients
/-!
# Uniform coupling and truncation bounds for the cavity hierarchy

The all-order bound in arXiv:2608.14343, Eq. (8), follows from the linear
Chebyshev envelope. The exact finite generating identity additionally gives a
two-term bound for both the denominator residual and the actual reciprocal error.
All coordinates are parameterized so that positivity and convergence are proved.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- All-order cavity coupling bound for the normalized physical sum-of-squares coordinates. -/
theorem cavityInteractionCoeff_normalized_bound (η d D E : ℝ) (n : ℕ) :
    |cavityInteractionCoeff η (D ^ (2 : ℕ) + E ^ (2 : ℕ))⁻¹ d D n| ≤
      |η * d / 2| * (|η| / Real.sqrt (D ^ (2 : ℕ) + E ^ (2 : ℕ))) ^ n * ((n : ℝ) + 1) := by
  let s := Real.sqrt (D ^ (2 : ℕ) + E ^ (2 : ℕ))⁻¹
  have hs : s ^ (2 : ℕ) = (D ^ (2 : ℕ) + E ^ (2 : ℕ))⁻¹ := Real.sq_sqrt (by positivity)
  have hcoord : -D * s = cavityChebyshevCoordinate D E := by
    simp only [s, Real.sqrt_inv, cavityChebyshevCoordinate, div_eq_mul_inv]
  rw [← hs, cavityInteractionCoeff_chebyshev, hcoord, abs_mul, abs_mul, abs_pow]
  have hc := quadraticResponseCoeff_cavity_bound D E n
  rw [quadraticResponseCoeff_eq_chebyshev] at hc
  have hnorm : |η * s| = |η| / Real.sqrt (D ^ (2 : ℕ) + E ^ (2 : ℕ)) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp only [Real.sqrt_inv, div_eq_mul_inv]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hc (by positivity)
/-- Explicit two-term envelope for the residual of a finite cavity-response approximation. -/
theorem quadraticCavityResponse_finite_residual_bound (D E s : ℝ) (n : ℕ) :
    |(1 - 2 * cavityChebyshevCoordinate D E * cavityDiskCoordinate s + cavityDiskCoordinate s ^ (2 : ℕ)) *
      (∑ k ∈ Finset.range (n + 1), quadraticResponseCoeff (-(2 * cavityChebyshevCoordinate D E)) 1 k *
        cavityDiskCoordinate s ^ k) - 1| ≤
      ((n : ℝ) + 2) * |cavityDiskCoordinate s| ^ (n + 1) +
        ((n : ℝ) + 1) * |cavityDiskCoordinate s| ^ (n + 2) := by
  let x := cavityChebyshevCoordinate D E
  let r := cavityDiskCoordinate s
  let c := quadraticResponseCoeff (-(2 * x)) 1
  have he : (1 - 2 * x * r + r ^ (2 : ℕ)) * (∑ k ∈ Finset.range (n + 1), c k * r ^ k) - 1 =
      -(c (n + 1) * r ^ (n + 1)) + c n * r ^ (n + 2) := by
    have h := quadraticResponseCoeff_finite_remainder (-(2 * x)) 1 r n
    dsimp [c]
    linear_combination h
  change |(1 - 2 * x * r + r ^ (2 : ℕ)) * (∑ k ∈ Finset.range (n + 1), c k * r ^ k) - 1| ≤ _
  rw [he]
  have h0 := quadraticResponseCoeff_cavity_bound D E n
  have h1 := quadraticResponseCoeff_cavity_bound D E (n + 1)
  change |c n| ≤ (n : ℝ) + 1 at h0
  change |c (n + 1)| ≤ ((n + 1 : ℕ) : ℝ) + 1 at h1
  have h := abs_add_le (-(c (n + 1) * r ^ (n + 1))) (c n * r ^ (n + 2))
  simp only [abs_neg, abs_mul, abs_pow] at h
  calc
    _ ≤ |c (n + 1)| * |r| ^ (n + 1) + |c n| * |r| ^ (n + 2) := h
    _ ≤ (((n + 1 : ℕ) : ℝ) + 1) * |r| ^ (n + 1) +
        ((n : ℝ) + 1) * |r| ^ (n + 2) := by gcongr
    _ = _ := by push_cast; ring
/-- The normalized response denominator is strictly positive throughout the parameterized disk. -/
theorem quadraticCavityResponse_denominator_pos (D E s : ℝ) :
    0 < 1 - 2 * cavityChebyshevCoordinate D E * cavityDiskCoordinate s + cavityDiskCoordinate s ^ (2 : ℕ) := by
  let x := cavityChebyshevCoordinate D E
  let r := cavityDiskCoordinate s
  have hx := abs_cavityChebyshevCoordinate_le_one D E
  have hr := abs_cavityDiskCoordinate_lt_one s
  have hprod : x * r ≤ |r| := by
    calc x * r ≤ |x * r| := le_abs_self _
         _ = |x| * |r| := abs_mul _ _
         _ ≤ 1 * |r| := mul_le_mul_of_nonneg_right hx (abs_nonneg r)
         _ = |r| := one_mul _
  have hs : 0 < (1 - |r|) ^ (2 : ℕ) := sq_pos_of_pos (sub_pos.mpr hr)
  have ha : |r| ^ (2 : ℕ) = r ^ (2 : ℕ) := sq_abs r
  change 0 < 1 - 2 * x * r + r ^ (2 : ℕ)
  nlinarith
/-- A quantitative error bound for the actual reciprocal, with no convergence or nonzero premises. -/
theorem quadraticCavityResponse_truncation_error (D E s : ℝ) (n : ℕ) :
    abs ((1 - 2 * cavityChebyshevCoordinate D E * cavityDiskCoordinate s + cavityDiskCoordinate s ^ (2 : ℕ))⁻¹ -
      (∑ k ∈ Finset.range (n + 1), quadraticResponseCoeff (-(2 * cavityChebyshevCoordinate D E)) 1 k *
        cavityDiskCoordinate s ^ k)) ≤
      (((n : ℝ) + 2) * |cavityDiskCoordinate s| ^ (n + 1) +
        ((n : ℝ) + 1) * |cavityDiskCoordinate s| ^ (n + 2)) /
      (1 - 2 * cavityChebyshevCoordinate D E * cavityDiskCoordinate s + cavityDiskCoordinate s ^ (2 : ℕ)) := by
  let den := 1 - 2 * cavityChebyshevCoordinate D E * cavityDiskCoordinate s + cavityDiskCoordinate s ^ (2 : ℕ)
  let partialSum := ∑ k ∈ Finset.range (n + 1),
    quadraticResponseCoeff (-(2 * cavityChebyshevCoordinate D E)) 1 k * cavityDiskCoordinate s ^ k
  have hd : 0 < den := quadraticCavityResponse_denominator_pos D E s
  have heq : den⁻¹ - partialSum = -(den * partialSum - 1) / den := by
    field_simp
    ring
  change |den⁻¹ - partialSum| ≤ _
  rw [heq, abs_div, abs_neg, abs_of_pos hd]
  exact div_le_div_of_nonneg_right (quadraticCavityResponse_finite_residual_bound D E s n) hd.le

end
end GaloisForLFunctions.HTGeometry
