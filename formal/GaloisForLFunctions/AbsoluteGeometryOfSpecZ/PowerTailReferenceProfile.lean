import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ArithmeticPowerRiemannProfiles

/-!
# The reference convolution as an improper Riemann sum

Subtracting the power integral from the inner summatory function removes
its nonintegrable leading term. The remaining staircase has envelope
`t⁻²ᵃ/(1-a)`, integrable throughout `0<a<1/2`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The pole-subtracted power-prefix discrepancy in inverse coordinates. -/
def powerTailReferenceProfile (a t : ℝ) : ℝ :=
  t ^ (-(2 * a)) *
    (powerTailPrefix a (1 / t) - (1 / t) ^ (1 - a) / (1 - a))

theorem measurable_powerTailReferenceProfile (a : ℝ) :
    Measurable (powerTailReferenceProfile a) := by
  have hs : Measurable (fun N : ℕ => ∑ n ∈ Icc 1 N, powerTailWeight a n) :=
    measurable_from_nat
  have hf : Measurable (fun t : ℝ => ⌊1 / t⌋₊) :=
    Nat.measurable_floor.comp (measurable_const.div measurable_id)
  have hp : Measurable (fun t : ℝ => powerTailPrefix a (1 / t)) := hs.comp hf
  exact (measurable_id.pow_const (-(2 * a))).mul
    (hp.sub (((measurable_const.div measurable_id).pow_const (1 - a)).div_const (1 - a)))

theorem powerTailReferenceProfile_eq (a : ℝ) {t : ℝ} (ht : 0 < t) :
    powerTailReferenceProfile a t =
      arithmeticPowerProfile (2 * a) (powerTailWeight a) t - t ^ (-(1 + a)) / (1 - a) := by
  have hp : t ^ (-(2 * a)) * t ^ (-(1 - a)) = t ^ (-(1 + a)) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hq : (1 / t) ^ (1 - a) = t ^ (-(1 - a)) := by
    rw [one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  rw [powerTailReferenceProfile, mul_sub, ← mul_div_assoc, hq, hp]
  rfl

/-- The cancellation inside the reference profile leaves a subcritical power. -/
theorem abs_powerTailReferenceProfile_le {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    |powerTailReferenceProfile a t| ≤ (1 / (1 - a)) * t ^ (-(2 * a)) := by
  have hb : 0 < 1 - a := by linarith only [ha1]
  have hp := powerTailPrefix_sub_integral_bounds ha ha1 (one_div_nonneg.mpr ht.1.le)
  have he : |powerTailPrefix a (1 / t) - (1 / t) ^ (1 - a) / (1 - a)| ≤
      1 / (1 - a) := abs_le.mpr ⟨hp.1, hp.2.trans (by positivity)⟩
  rw [powerTailReferenceProfile, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht.1.le _), mul_comm (1 / (1 - a))]
  exact mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.1.le _)

/-- Every positive cutoff removes all but finitely many jumps of the reference
profile. The continuous power term is cut off at the same point. -/
theorem riemannOn_cut_powerTailReferenceProfile {a δ : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    RiemannOn ((Set.Ioi δ).indicator (powerTailReferenceProfile a)) := by
  have hu := riemannOn_cut_arithmeticPowerProfile
    (show 0 ≤ 2 * a by linarith only [ha]) hδ (powerTailWeight a)
  have hv := (riemannOn_rpow_interval (show 0 ≤ 1 + a by linarith only [ha])
    hδ hδ1).const_mul (1 / (1 - a))
  refine (hu.sub hv).congr fun t ht => ?_
  by_cases hδt : δ < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi δ from hδt),
      Set.indicator_of_mem (show t ∈ Set.Ioi δ from hδt), if_pos ⟨hδt, ht.2⟩,
      powerTailReferenceProfile_eq a ht.1]
    ring
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi δ from hδt),
      Set.indicator_of_notMem (show t ∉ Set.Ioi δ from hδt),
      if_neg (fun h => hδt h.1), mul_zero, sub_zero]

/-- The normalized reference-convolution profile has an actual limiting
integral throughout the subcritical range. -/
theorem riemannOn_powerTailReferenceProfile {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    RiemannOn (powerTailReferenceProfile a) := by
  exact riemannOn_of_powerBound_and_cuts
    (show 0 < 2 * a by linarith only [ha])
    (show 2 * a < 1 by linarith only [ha2])
    (measurable_powerTailReferenceProfile a)
    (fun t ht => abs_powerTailReferenceProfile_le ha (by linarith only [ha2]) ht)
    (fun δ hδ hδ1 => riemannOn_cut_powerTailReferenceProfile ha hδ hδ1)

/-- The leading reference term uses the finite first degree, so it cancels
the polar part of the comb before any limit is taken. -/
theorem tailRiemannSum_powerTailReferenceProfile_eq (a : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    tailRiemannSum (powerTailReferenceProfile a) N =
      (N : ℝ) ^ (2 * a - 1) *
        ((∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailZeta a) n) -
          ((N : ℝ) ^ (1 - a) / (1 - a)) *
            ∑ n ∈ Icc 1 N, powerTailWeight (1 + a) n) := by
  have hmesh := tailRiemannSum_inverse_power_eq (2 * a)
    (fun x => powerTailPrefix a x - x ^ (1 - a) / (1 - a)) hN
  change tailRiemannSum (powerTailReferenceProfile a) N = _ at hmesh
  rw [hmesh]
  congr 1
  simp only [mul_sub, sum_sub_distrib]
  congr 1
  · rw [RHTower.sum_Icc_mul_apply]
    apply sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    rw [powerTailZeta_apply hm0, powerTailPrefix, Nat.floor_div_eq_div]
    congr 1
    apply sum_congr rfl
    intro n hn
    exact (powerTailZeta_apply (by have := (mem_Icc.mp hn).1; omega) a).symm
  · rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
    rw [powerTailWeight, powerTailWeight, Real.div_rpow (Nat.cast_nonneg N) hmR.le]
    calc
      _ = ((N : ℝ) ^ (1 - a) / (1 - a)) *
          ((m : ℝ) ^ (-(2 * a)) * ((m : ℝ) ^ (1 - a))⁻¹) := by ring
      _ = _ := by
        rw [← Real.rpow_neg hmR.le, ← Real.rpow_add hmR]
        congr 2
        ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
