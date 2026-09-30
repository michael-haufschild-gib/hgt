import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentEndpointCoefficients
import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentClockSource
import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentClockSeries


import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Literal actual-current clock limit

The endpoint-normalized polynomial gives an exact finite moment-functional
expansion of the actual current. Its clock-scaled coefficients and the complete
shifted source moments have fixed-degree limits. A uniform summable factorial
envelope passes those limits through the full natural-index sum along any filter.
-/

open Polynomial Complex Real Filter Set Topology
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Exact endpoint normalization of the actual adjacent-current polynomial. -/
theorem liEvenCrossUnitFluxQuotient_eq_normalizedEndpointPolynomial (n : ℕ) :
    liEvenCrossUnitFluxQuotient n =
      C (2 * ((n + 1 : ℕ) : ℝ) ^ 2) * (1 - X) *
        liEvenCrossNormalizedEndpointPolynomial n := by
  apply Polynomial.funext
  intro x
  have hu : (Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).eval (2 * x - 1) =
      -(Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).eval (1 - 2 * x) := by
    rw [show 2 * x - 1 = -(1 - 2 * x) by ring, Chebyshev.U_eval_neg]
    simp [Int.negOnePow_two_mul_add_one]
  rw [liEvenCrossUnitFluxQuotient_eq_oddChebyshev]
  simp only [liEvenCrossNormalizedEndpointPolynomial, liEvenCrossUnitAffine,
    eval_mul, eval_neg, eval_add, eval_sub, eval_natCast, eval_one, eval_ofNat,
    eval_X, eval_C, eval_comp]
  rw [hu]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

private theorem momentFunctional_one_sub_X_scaled
    (s : ℕ → ℝ) (v : ℝ) (P : ℝ[X]) :
    HTGeometry.momentFunctional s (((1 - X) * P).comp (C v * X)) =
      HTGeometry.momentFunctional (fun j => v ^ j * (s j - v * s (j + 1))) P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [mul_add, Polynomial.add_comp, HTGeometry.momentFunctional_add, hp, hq]
  | monomial j a =>
      have hpoly : (1 - X) * Polynomial.monomial j a =
          Polynomial.monomial j a - Polynomial.monomial (j + 1) a := by
        rw [← Polynomial.C_mul_X_pow_eq_monomial,
          ← Polynomial.C_mul_X_pow_eq_monomial, pow_succ]
        ring
      rw [hpoly, Polynomial.sub_comp, HTGeometry.momentFunctional_sub,
        momentFunctional_monomial_comp_scale, momentFunctional_monomial_comp_scale,
        HTGeometry.momentFunctional_monomial, pow_succ]
      ring

private theorem momentFunctional_eq_coefficient_sum (s : ℕ → ℝ) (P : ℝ[X]) :
    HTGeometry.momentFunctional s P =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * s j := by
  conv_lhs => rw [P.as_sum_range]
  rw [HTGeometry.momentFunctional_finset_sum]
  simp only [HTGeometry.momentFunctional_monomial]

/-- Exact normalized finite coefficient expansion of the literal actual current. -/
theorem liEvenCrossSquareMassAdjacentCurrent_div_eq_endpoint_coeff_sum
    (v : ℝ) (n : ℕ) :
    liEvenCrossSquareMassAdjacentCurrent v n / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      ∑ j ∈ Finset.range ((liEvenCrossNormalizedEndpointPolynomial n).natDegree + 1),
        (liEvenCrossNormalizedEndpointPolynomial n).coeff j * v ^ j *
          ((xiShiftedReciprocalMoment v j).re -
            v * (xiShiftedReciprocalMoment v (j + 1)).re) := by
  rw [liEvenCrossSquareMassAdjacentCurrent,
    liEvenCrossUnitFluxQuotient_eq_normalizedEndpointPolynomial]
  rw [mul_assoc, Polynomial.mul_comp, Polynomial.C_comp,
    HTGeometry.momentFunctional_C_mul]
  have hn : (2 * ((n + 1 : ℕ) : ℝ) ^ 2) ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hn, momentFunctional_one_sub_X_scaled,
    momentFunctional_eq_coefficient_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Clock-scaled coefficients retain the exact finite product, even for bounded modes. -/
theorem liEvenCrossNormalizedEndpointPolynomial_coeff_mul_mass_pow (n j : ℕ) (v : ℝ) :
    (liEvenCrossNormalizedEndpointPolynomial n).coeff j * v ^ j =
      (-1 : ℝ) ^ j * 4 ^ j *
        (∏ i ∈ Finset.range j,
          (4 * (((n + 1 : ℕ) : ℝ) ^ 2 * v) - ((i + 1 : ℕ) : ℝ) ^ 2 * v)) /
        ((2 * j + 1).factorial : ℝ) := by
  rw [liEvenCrossNormalizedEndpointPolynomial_coeff]
  have hp : (∏ i ∈ Finset.range j,
      (4 * (((n + 1 : ℕ) : ℝ) ^ 2 * v) - ((i + 1 : ℕ) : ℝ) ^ 2 * v)) =
      (∏ i ∈ Finset.range j,
        (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2)) * v ^ j := by
    simp_rw [show ∀ i : ℕ,
      4 * (((n + 1 : ℕ) : ℝ) ^ 2 * v) - ((i + 1 : ℕ) : ℝ) ^ 2 * v =
        (4 * ((n + 1 : ℕ) : ℝ) ^ 2 - ((i + 1 : ℕ) : ℝ) ^ 2) * v by
      intro i; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hp]
  ring

/-- Fixed coefficient clock limit along an arbitrary filter. -/
theorem tendsto_liEvenCrossNormalizedEndpointPolynomial_scaled_coeff
    {α : Type*} {l : Filter α} {v : α → ℝ} {n : α → ℕ} {w : ℝ}
    (hv : Tendsto v l (𝓝[Ioi 0] 0))
    (hclock : Tendsto (fun x => ((n x + 1 : ℕ) : ℝ) ^ 2 * v x) l (𝓝 w))
    (j : ℕ) :
    Tendsto (fun x => (liEvenCrossNormalizedEndpointPolynomial (n x)).coeff j * (v x) ^ j)
      l (𝓝 ((-1 : ℝ) ^ j * (16 * w) ^ j / ((2 * j + 1).factorial : ℝ))) := by
  have hv0 : Tendsto v l (𝓝 0) := hv.mono_right nhdsWithin_le_nhds
  have hf (i : ℕ) : Tendsto (fun x =>
      4 * (((n x + 1 : ℕ) : ℝ) ^ 2 * v x) - ((i + 1 : ℕ) : ℝ) ^ 2 * v x)
      l (𝓝 (4 * w)) := by
    simpa only [mul_zero, sub_zero] using
      (hclock.const_mul 4).sub (hv0.const_mul (((i + 1 : ℕ) : ℝ) ^ 2))
  have hp := tendsto_finsetProd (Finset.range j) (fun i _ => hf i)
  have ht := (hp.const_mul ((-1 : ℝ) ^ j * 4 ^ j)).div_const
    ((2 * j + 1).factorial : ℝ)
  have hc : (-1 : ℝ) ^ j * 4 ^ j * (4 * w) ^ j =
      (-1 : ℝ) ^ j * (16 * w) ^ j := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    ring
  simpa only [liEvenCrossNormalizedEndpointPolynomial_coeff_mul_mass_pow,
    Finset.prod_const, Finset.card_range, hc] using ht

/-- Factorial envelope for the mass-scaled endpoint coefficients. -/
theorem norm_liEvenCrossNormalizedEndpointPolynomial_scaled_coeff_le
    (n j : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    ‖(liEvenCrossNormalizedEndpointPolynomial n).coeff j * v ^ j‖ ≤
      (16 * (((n + 1 : ℕ) : ℝ) ^ 2 * v)) ^ j / ((2 * j + 1).factorial : ℝ) := by
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hv]
  calc
    ‖(liEvenCrossNormalizedEndpointPolynomial n).coeff j‖ * v ^ j ≤
        ((16 * ((n + 1 : ℕ) : ℝ) ^ 2) ^ j / ((2 * j + 1).factorial : ℝ)) * v ^ j :=
      mul_le_mul_of_nonneg_right (norm_liEvenCrossNormalizedEndpointPolynomial_coeff_le n j)
        (pow_nonneg hv j)
    _ = _ := by
      rw [div_mul_eq_mul_div, ← mul_pow]
      congr 2
      ring

/-- Exact complete-current coefficient expansion with the second radial denominator retained. -/
theorem liEvenCrossSquareMassAdjacentCurrent_div_eq_clockSource_tsum
    (v : ℝ) (n : ℕ) :
    liEvenCrossSquareMassAdjacentCurrent v n / (2 * ((n + 1 : ℕ) : ℝ) ^ 2) =
      ∑' j : ℕ, (liEvenCrossNormalizedEndpointPolynomial n).coeff j * v ^ j *
        liEvenCrossActualClockSourceMoment v j := by
  rw [tsum_eq_sum (s := Finset.range
    ((liEvenCrossNormalizedEndpointPolynomial n).natDegree + 1))]
  · simpa only [liEvenCrossActualClockSourceMoment, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      liEvenCrossSquareMassAdjacentCurrent_div_eq_endpoint_coeff_sum v n
  · intro j hj
    have hc : (liEvenCrossNormalizedEndpointPolynomial n).coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hj
        omega)
    rw [hc, zero_mul, zero_mul]

/-- Full-source factorial domination, uniform over any bounded nonnegative clock. -/
theorem norm_liEvenCrossActualCurrentClockTerm_le
    {v R : ℝ} (hv : 0 ≤ v) (n j : ℕ)
    (hclock : ((n + 1 : ℕ) : ℝ) ^ 2 * v ≤ R) :
    ‖(liEvenCrossNormalizedEndpointPolynomial n).coeff j * v ^ j *
      liEvenCrossActualClockSourceMoment v j‖ ≤
      xiShiftAbsoluteMass 0 * ((16 * R / 150) ^ j / ((2 * j + 1).factorial : ℝ)) := by
  have hcl0 : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * v := mul_nonneg (sq_nonneg _) hv
  have hR : 0 ≤ R := hcl0.trans hclock
  rw [norm_mul]
  calc
    ‖(liEvenCrossNormalizedEndpointPolynomial n).coeff j * v ^ j‖ *
        ‖liEvenCrossActualClockSourceMoment v j‖ ≤
        ((16 * (((n + 1 : ℕ) : ℝ) ^ 2 * v)) ^ j / ((2 * j + 1).factorial : ℝ)) *
          ((1 / 150 : ℝ) ^ j * xiShiftAbsoluteMass 0) := by
      apply mul_le_mul (norm_liEvenCrossNormalizedEndpointPolynomial_scaled_coeff_le n j hv)
      · simpa only [Real.norm_eq_abs] using abs_liEvenCrossActualClockSourceMoment_le hv j
      · exact norm_nonneg _
      · positivity
    _ = xiShiftAbsoluteMass 0 *
        ((16 * (((n + 1 : ℕ) : ℝ) ^ 2 * v) / 150) ^ j /
          ((2 * j + 1).factorial : ℝ)) := by
      rw [show 16 * (((n + 1 : ℕ) : ℝ) ^ 2 * v) / 150 =
        (16 * (((n + 1 : ℕ) : ℝ) ^ 2 * v)) * (1 / 150) by ring,
        mul_pow (16 * (((n + 1 : ℕ) : ℝ) ^ 2 * v)) (1 / 150) j]
      ring
    _ ≤ _ := by
      have hA : 0 ≤ xiShiftAbsoluteMass 0 := xiShiftAbsoluteMass_nonneg 0
      gcongr

/-- The literal actual adjacent current has the entire source clock limit along any filter.
No separate mode-growth or filter nontriviality premise is needed. -/
theorem tendsto_liEvenCrossSquareMassAdjacentCurrent_clock
    {α : Type*} {l : Filter α} {v : α → ℝ} {n : α → ℕ} {w : ℝ}
    (hv : Tendsto v l (𝓝[Ioi 0] 0))
    (hclock : Tendsto (fun x => ((n x + 1 : ℕ) : ℝ) ^ 2 * v x) l (𝓝 w)) :
    Tendsto (fun x => liEvenCrossSquareMassAdjacentCurrent (v x) (n x) /
      (2 * ((n x + 1 : ℕ) : ℝ) ^ 2)) l
      (𝓝 (liEvenCrossActualCurrentClockSeries w)) := by
  let R : ℝ := |w| + 1
  have hR : 0 < R := by dsimp [R]; linarith [abs_nonneg w]
  have hwR : w < R := by dsimp [R]; linarith [le_abs_self w]
  have hsum : Summable (fun j : ℕ => xiShiftAbsoluteMass 0 *
      ((16 * R / 150) ^ j / ((2 * j + 1).factorial : ℝ))) :=
    (summable_liEvenCrossActualCurrentClockFactorialEnvelope (16 * R / 150)
      (by positivity)).mul_left (xiShiftAbsoluteMass 0)
  have hterms (j : ℕ) : Tendsto (fun x =>
      (liEvenCrossNormalizedEndpointPolynomial (n x)).coeff j * (v x) ^ j *
        liEvenCrossActualClockSourceMoment (v x) j) l
      (𝓝 (((-1 : ℝ) ^ j * (16 * w) ^ j / ((2 * j + 1).factorial : ℝ)) *
        normalizedPrimeArchMoment j)) :=
    (tendsto_liEvenCrossNormalizedEndpointPolynomial_scaled_coeff hv hclock j).mul
      ((liEvenCrossActualClockSourceMoment_tendsto_zero j).comp hv)
  have hbound : ∀ᶠ x in l, ∀ j : ℕ,
      ‖(liEvenCrossNormalizedEndpointPolynomial (n x)).coeff j * (v x) ^ j *
        liEvenCrossActualClockSourceMoment (v x) j‖ ≤
      xiShiftAbsoluteMass 0 * ((16 * R / 150) ^ j / ((2 * j + 1).factorial : ℝ)) := by
    have hvpos : ∀ᶠ x in l, 0 < v x := hv.eventually self_mem_nhdsWithin
    have hcR : ∀ᶠ x in l, ((n x + 1 : ℕ) : ℝ) ^ 2 * v x < R :=
      hclock.eventually (gt_mem_nhds hwR)
    filter_upwards [hvpos, hcR] with x hx hcx
    intro j
    exact norm_liEvenCrossActualCurrentClockTerm_le hx.le (n x) j hcx.le
  have ht := tendsto_tsum_of_dominated_convergence hsum hterms hbound
  have heq : (∑' j : ℕ, ((-1 : ℝ) ^ j * (16 * w) ^ j /
      ((2 * j + 1).factorial : ℝ)) * normalizedPrimeArchMoment j) =
      liEvenCrossActualCurrentClockSeries w := by
    unfold liEvenCrossActualCurrentClockSeries
    apply tsum_congr
    intro j
    ring
  rw [heq] at ht
  simpa only [← liEvenCrossSquareMassAdjacentCurrent_div_eq_clockSource_tsum] using ht

end
end RHTower
