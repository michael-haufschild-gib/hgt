import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanWeights
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingTransitionKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The arithmetic entrance distribution and its reciprocal-observable tail

The entrance weights are a discrete derivative of the zeta power law.
They have total mass one. Their reciprocal-observable tail telescopes exactly;
this is faster than their probability tail and preserves the receiver's observable.
-/

open Finset Filter Topology RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The probability entering finite states from arbitrarily large cutoffs. -/
def arithmeticDampingEntrance (η : ℝ) (k : ℕ) : ℝ :=
  (pmPowerDampedDivisorDensity η).re * k *
    ((k : ℝ) ^ (-1 - η) - ((k + 1 : ℕ) : ℝ) ^ (-1 - η))

@[simp] theorem arithmeticDampingEntrance_zero (η : ℝ) :
    arithmeticDampingEntrance η 0 = 0 := by
  simp [arithmeticDampingEntrance]

theorem arithmeticDampingEntrance_nonneg {η : ℝ} (hη : 0 < η) (k : ℕ) :
    0 ≤ arithmeticDampingEntrance η k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  unfold arithmeticDampingEntrance
  apply mul_nonneg (mul_nonneg (pmPowerDampedDivisorDensity_re_pos hη).le hk0.le)
  exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hk0 (by norm_cast; omega) (by linarith))

/-- Dividing by the actual observable's denominator removes the size bias. -/
theorem arithmeticDampingEntrance_div (η : ℝ) {k : ℕ} (hk : 0 < k) :
    arithmeticDampingEntrance η k / k =
      (pmPowerDampedDivisorDensity η).re *
        ((k : ℝ) ^ (-1 - η) - ((k + 1 : ℕ) : ℝ) ^ (-1 - η)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold arithmeticDampingEntrance
  field_simp

private theorem entrance_density_sum {η : ℝ} (hη : 0 < η) :
    (pmPowerDampedDivisorDensity η).re *
      (∑' k : ℕ, (k : ℝ) ^ (-1 - η)) = 1 := by
  have hs : 1 < (1 + (η : ℂ)).re := by simp; linarith
  have hz : (((∑' k : ℕ, (k : ℝ) ^ (-1 - η)) : ℝ) : ℂ) =
      riemannZeta (1 + (η : ℂ)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs, Complex.ofReal_tsum]
    apply tsum_congr
    intro k
    rw [show -1 - η = -(1 + η) by ring,
      Real.rpow_neg (Nat.cast_nonneg k), Complex.ofReal_inv,
      Complex.ofReal_cpow (Nat.cast_nonneg k)]
    simp
  have hprod : pmPowerDampedDivisorDensity η *
      (((∑' k : ℕ, (k : ℝ) ^ (-1 - η)) : ℝ) : ℂ) = 1 := by
    rw [hz, pmPowerDampedDivisorDensity]
    exact one_div_mul_cancel (riemannZeta_ne_zero_of_one_lt_re hs)
  have hre := congrArg Complex.re hprod
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.one_re] using hre

private theorem entrance_power_hasSum {η : ℝ} (hη : 0 < η) :
    HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-1 - η))
      (∑' k : ℕ, (k : ℝ) ^ (-1 - η)) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (-1 - η)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := ((summable_nat_add_iff 1).mpr hs).hasSum
  have he := hs.tsum_eq_zero_add
  have hp : (-1 - η) ≠ 0 := by linarith
  simp only [Nat.cast_zero, Real.zero_rpow hp, zero_add] at he
  rwa [← he] at ht

private theorem entrance_boundary_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ => (N : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-1 - η))
      atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop hη).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hr := (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ)).mul hp
  simp only [mul_zero] at hr
  apply hr.congr
  intro N
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have he : ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-1 - η) =
      ((N : ℝ) + 1) ^ (-η) := by
    calc
      _ = ((N : ℝ) + 1) ^ (1 + (-1 - η)) := by
        rw [Real.rpow_add hN, Real.rpow_one]
      _ = _ := by congr 1; ring
  dsimp only [Function.comp_def]
  push_cast
  rw [← he]
  field_simp [hN.ne']

/-- Total entrance mass equals one, using the actual reciprocal-zeta density. -/
theorem hasSum_arithmeticDampingEntrance {η : ℝ} (hη : 0 < η) :
    HasSum (fun k : ℕ => arithmeticDampingEntrance η (k + 1)) 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => arithmeticDampingEntrance_nonneg hη (k + 1)) 1).mpr
  have he (N : ℕ) :
      (∑ k ∈ range N, arithmeticDampingEntrance η (k + 1)) =
        (pmPowerDampedDivisorDensity η).re *
          ((∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) ^ (-1 - η)) -
            N * ((N + 1 : ℕ) : ℝ) ^ (-1 - η)) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      unfold arithmeticDampingEntrance
      push_cast
      ring
  simp_rw [he]
  have h := (((entrance_power_hasSum hη).tendsto_sum_nat).sub
    (entrance_boundary_tendsto hη)).const_mul (pmPowerDampedDivisorDensity η).re
  simpa only [sub_zero, entrance_density_sum hη] using h

/-- Exact omitted tail for the reciprocal observable. The cutoff is arbitrary. -/
theorem hasSum_arithmeticDampingEntrance_reciprocal_tail {η : ℝ} (hη : 0 < η) (N : ℕ) :
    HasSum (fun k : ℕ =>
      arithmeticDampingEntrance η (N + k + 1) / (N + k + 1 : ℕ))
      ((pmPowerDampedDivisorDensity η).re * ((N + 1 : ℕ) : ℝ) ^ (-1 - η)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => div_nonneg (arithmeticDampingEntrance_nonneg hη _) (Nat.cast_nonneg _)) _).mpr
  have he (M : ℕ) :
      (∑ k ∈ range M, arithmeticDampingEntrance η (N + k + 1) / (N + k + 1 : ℕ)) =
        (pmPowerDampedDivisorDensity η).re *
          (((N + 1 : ℕ) : ℝ) ^ (-1 - η) -
            ((N + M + 1 : ℕ) : ℝ) ^ (-1 - η)) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, arithmeticDampingEntrance_div η (by omega)]
      simp only [Nat.add_assoc, Nat.add_comm M 1]
      ring
  simp_rw [he]
  have hp := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 + η)).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_atTop_add_const_left atTop (N : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ))))
  have h := ((tendsto_const_nhds (x := ((N + 1 : ℕ) : ℝ) ^ (-1 - η))
    (f := atTop (α := ℕ))).sub hp).const_mul (pmPowerDampedDivisorDensity η).re
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one,
    show -(1 + η) = -1 - η by ring, sub_zero] using h

private theorem tendsto_arithmeticDampingPrefix_quotient {η : ℝ} (hη : 0 < η)
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => arithmeticDampingPrefix η (n / d) / (n : ℝ))
      atTop (𝓝 ((pmPowerDampedDivisorDensity η).re / (d : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := ((tendsto_pmPowerDampedDivisorSum_div_real hη).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const hd0)).div_const (d : ℝ)
  apply h.congr
  intro n
  dsimp only [Function.comp_def]
  rw [pmPowerDampedDivisorSum, Nat.floor_div_eq_div, div_div,
    div_mul_cancel₀ _ hd0.ne']
  rfl

/-- Every fixed finite state has the exact arithmetic entrance mass at large cutoffs. -/
theorem tendsto_arithmeticDampingTransition {η : ℝ} (hη : 0 < η) (k : ℕ) :
    Tendsto (fun n : ℕ => arithmeticDampingTransition η n k) atTop
      (𝓝 (arithmeticDampingEntrance η k)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have h := (((tendsto_arithmeticDampingPrefix_quotient hη hkpos).const_mul
      ((k : ℝ) ^ (-η))).sub
    ((tendsto_arithmeticDampingPrefix_quotient hη (Nat.succ_pos k)).const_mul
      (((k + 1 : ℕ) : ℝ) ^ (-η)))).const_mul (k : ℝ)
  have hpow {d : ℕ} (hd : 0 < d) :
      (d : ℝ) ^ (-η) / d = (d : ℝ) ^ (-1 - η) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    rw [show -1 - η = -η - 1 by ring, Real.rpow_sub hd0, Real.rpow_one]
  have hval : (k : ℝ) *
      ((k : ℝ) ^ (-η) * ((pmPowerDampedDivisorDensity η).re / k) -
        ((k + 1 : ℕ) : ℝ) ^ (-η) *
          ((pmPowerDampedDivisorDensity η).re / ((k + 1 : ℕ) : ℝ))) =
      arithmeticDampingEntrance η k := by
    unfold arithmeticDampingEntrance
    calc
      _ = (pmPowerDampedDivisorDensity η).re * k *
          ((k : ℝ) ^ (-η) / k -
            ((k + 1 : ℕ) : ℝ) ^ (-η) / ((k + 1 : ℕ) : ℝ)) := by ring
      _ = _ := by rw [hpow hkpos, hpow (Nat.succ_pos k)]
  rw [hval] at h
  apply h.congr
  intro n
  unfold arithmeticDampingTransition
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
