/-
# Sixth-power polarization for Bourgain's double-large-sieve input

Equation (3.7) in Bourgain's paper first applies the sixth-power Hölder
inequality to a family of short curve sums and then chooses a unit complex
factor for each sample so that its sixth power becomes a nonnegative real
number.  Expanding that sixth power produces the six-fold moment cloud used
by the double large sieve.

This file proves that step exactly for arbitrary finite sample families.  No
spacing, large-sieve, or decoupling estimate is assumed.
-/
import GaloisForLFunctions.RHTower.BourgainSixfoldCloud
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Unit phase which turns `z ^ (6 : ℕ)` into the nonnegative real number
`‖z‖ ^ (6 : ℕ)`.  At zero we choose zero. -/
def bourgainSixthPowerPolarizer (z : ℂ) : ℂ :=
  if z = 0 then 0
  else (star z / (‖z‖ : ℂ)) ^ (6 : ℕ)

theorem norm_bourgainSixthPowerPolarizer_le_one (z : ℂ) :
    ‖bourgainSixthPowerPolarizer z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [bourgainSixthPowerPolarizer, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [bourgainSixthPowerPolarizer, if_neg hz, norm_pow, norm_div,
      norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z)]
    field_simp
    norm_num

/-- Exact phase alignment:
`polarizer(z) * z^(6 : ℕ) = ‖z‖^(6 : ℕ)`. -/
theorem bourgainSixthPowerPolarizer_mul_pow_six (z : ℂ) :
    bourgainSixthPowerPolarizer z * z ^ (6 : ℕ) =
      ((‖z‖ ^ (6 : ℕ) : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · simp [bourgainSixthPowerPolarizer, hz]
  · have hnR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnC : ((‖z‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hnR
    rw [bourgainSixthPowerPolarizer, if_neg hz]
    rw [div_pow]
    field_simp [hnC]
    rw [← mul_pow]
    have hc :
        star z * z = (((‖z‖ : ℝ) : ℂ) ^ (2 : ℕ)) := by
      simpa using Complex.conj_mul' z
    rw [hc]
    push_cast
    ring

/-- A finite sum of sixth powers of norms is the norm of the phase-aligned
sum of the corresponding complex sixth powers. -/
theorem sum_norm_pow_six_eq_norm_sum_polarized
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∑ i : ι, ‖z i‖ ^ (6 : ℕ)) =
      ‖∑ i : ι,
        bourgainSixthPowerPolarizer (z i) * z i ^ (6 : ℕ)‖ := by
  have hsum :
      (∑ i : ι,
          bourgainSixthPowerPolarizer (z i) * z i ^ (6 : ℕ)) =
        (((∑ i : ι, ‖z i‖ ^ (6 : ℕ)) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    simpa using bourgainSixthPowerPolarizer_mul_pow_six (z i)
  rw [hsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]

/-- Sixth-power Hölder with exact phase alignment. -/
theorem sum_norm_pow_six_le_card_five_mul_norm_polarized
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (∑ i : ι, ‖z i‖) ^ (6 : ℕ) ≤
      (Fintype.card ι : ℝ) ^ (5 : ℕ) *
        ‖∑ i : ι,
          bourgainSixthPowerPolarizer (z i) * z i ^ (6 : ℕ)‖ := by
  have hholder :
      (∑ i : ι, ‖z i‖) ^ (6 : ℕ) ≤
        (Fintype.card ι : ℝ) ^ (5 : ℕ) *
          ∑ i : ι, ‖z i‖ ^ (6 : ℕ) := by
    simpa using
      (pow_sum_le_card_mul_sum_pow
        (s := (Finset.univ : Finset ι))
        (f := fun i => ‖z i‖)
        (fun i hi => norm_nonneg (z i)) 5)
  rw [sum_norm_pow_six_eq_norm_sum_polarized] at hholder
  exact hholder

/-- The fully expanded, phase-aligned six-fold cloud over a finite family of
sample points. -/
def bourgainPolarizedSixfoldSampleSum
    {ι : Type*} [Fintype ι]
    (H : ℕ) (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace) : ℂ :=
  ∑ i : ι,
    ∑ h : Fin 6 → Fin H,
      bourgainSixthPowerPolarizer
          (bourgainShortCurveSum H α (x i)) *
        bourgainSixfoldWeight α h *
        bourgainAdditiveCharacter (x i) (bourgainSixfoldMoment h)

/-- Exact expansion of the phase-aligned sixth powers into Bourgain's
six-fold frequency cloud. -/
theorem sum_polarized_shortCurveSum_pow_six_eq_cloud
    {ι : Type*} [Fintype ι]
    (H : ℕ) (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace) :
    (∑ i : ι,
        bourgainSixthPowerPolarizer
            (bourgainShortCurveSum H α (x i)) *
          bourgainShortCurveSum H α (x i) ^ (6 : ℕ)) =
      bourgainPolarizedSixfoldSampleSum H α x := by
  unfold bourgainPolarizedSixfoldSampleSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [bourgainShortCurveSum_pow_six, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- **Bourgain equation (3.7), exact finite form.**

For any finite sample family, the sixth power of the sum of the short-sum
moduli is bounded by `card^(5 : ℕ)` times the norm of one bilinear exponential sum
over the sample family and the six-fold moment cloud.  Its outer
polarization coefficients have norm at most one by
`norm_bourgainSixthPowerPolarizer_le_one`. -/
theorem sum_norm_bourgainShortCurveSum_pow_six_le_cloud
    {ι : Type*} [Fintype ι]
    (H : ℕ) (α : Fin H → ℂ) (x : ι → BourgainPhaseSpace) :
    (∑ i : ι, ‖bourgainShortCurveSum H α (x i)‖) ^ (6 : ℕ) ≤
      (Fintype.card ι : ℝ) ^ (5 : ℕ) *
        ‖bourgainPolarizedSixfoldSampleSum H α x‖ := by
  have h :=
    sum_norm_pow_six_le_card_five_mul_norm_polarized
      (fun i : ι => bourgainShortCurveSum H α (x i))
  rw [sum_polarized_shortCurveSum_pow_six_eq_cloud] at h
  exact h

end

end RHTower
