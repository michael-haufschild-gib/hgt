import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceProfile
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrefixFinitePart
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ArithmeticPowerProfileMellinIntegral

/-!
# The reference Mellin integral

Integrate the inverse staircase above `1/N` before taking a limit.
The divergent powers cancel exactly; the centered power prefix leaves
the continued zeta value at `1-a`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

private theorem integral_inverse_cut_rpow {a : ℝ} (ha : 0 < a)
    {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Set.Ioc (0 : ℝ) 1,
      (Set.Ioi (1 / (N : ℝ))).indicator (fun t => t ^ (-(1 + a))) t) =
      ((N : ℝ) ^ a - 1) / a := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNp
  have hδ1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNp]
    exact_mod_cast hN
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi (1 / (N : ℝ)) =
      Set.Ioc (1 / (N : ℝ)) 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hδ.trans h.1, h.2⟩, h.1⟩⟩
  rw [setIntegral_indicator measurableSet_Ioi, hset,
    ← intervalIntegral.integral_of_le hδ1,
    integral_rpow (Or.inr ⟨by linarith only [ha], by
      rw [Set.uIcc_of_le hδ1]
      intro h
      exact (not_le.mpr hδ) h.1⟩),
    show -(1 + a) + 1 = -a by ring, Real.one_rpow,
    one_div, Real.inv_rpow hNp.le, ← Real.rpow_neg hNp.le, neg_neg]
  ring

private theorem integral_cut_powerTailReferenceProfile {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Set.Ioc (0 : ℝ) 1,
      (Set.Ioi (1 / (N : ℝ))).indicator (powerTailReferenceProfile a) t) =
      (powerTailPrefix (1 - a) N -
        (N : ℝ) ^ (-(1 - 2 * a)) * powerTailPrefix a N) / (1 - 2 * a) -
        ((N : ℝ) ^ a - 1) / (a * (1 - a)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNp
  have hδ1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNp]
    exact_mod_cast hN
  have hu := (riemannOn_cut_arithmeticPowerProfile
    (show 0 ≤ 2 * a by linarith only [ha]) hδ (powerTailWeight a)).1
  have hv : IntegrableOn ((Set.Ioi (1 / (N : ℝ))).indicator
      (fun t : ℝ => t ^ (-(1 + a)))) (Set.Ioc 0 1) := by
    have h := riemannOn_rpow_interval (show 0 ≤ 1 + a by linarith only [ha]) hδ hδ1
    apply h.1.congr_fun _ measurableSet_Ioc
    intro t ht
    rw [Set.indicator_apply]
    simp only [Set.mem_Ioi]
    by_cases hδt : 1 / (N : ℝ) < t
    · rw [if_pos ⟨hδt, ht.2⟩, if_pos hδt]
    · rw [if_neg (fun h => hδt h.1), if_neg hδt]
  have he (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      (Set.Ioi (1 / (N : ℝ))).indicator (powerTailReferenceProfile a) t =
        (Set.Ioi (1 / (N : ℝ))).indicator
          (arithmeticPowerProfile (2 * a) (powerTailWeight a)) t -
          (1 / (1 - a)) * (Set.Ioi (1 / (N : ℝ))).indicator
            (fun t : ℝ => t ^ (-(1 + a))) t := by
    by_cases hδt : 1 / (N : ℝ) < t
    · rw [Set.indicator_of_mem hδt, Set.indicator_of_mem hδt,
        Set.indicator_of_mem hδt, powerTailReferenceProfile_eq a ht.1]
      ring
    · rw [Set.indicator_of_notMem hδt, Set.indicator_of_notMem hδt,
        Set.indicator_of_notMem hδt, mul_zero, sub_zero]
  rw [setIntegral_congr_fun measurableSet_Ioc he, integral_sub hu (hv.const_mul _),
    integral_const_mul, integral_inverse_cut_rpow ha hN,
    integral_cut_arithmeticPowerProfile (show 0 ≤ 2 * a by linarith only [ha])
      (show 2 * a < 1 by linarith only [ha2]) (powerTailWeight a) hN]
  have hw : (∑ n ∈ Icc 1 N, powerTailWeight a n * (n : ℝ) ^ (-(1 - 2 * a))) =
      powerTailPrefix (1 - a) N := by
    rw [powerTailPrefix, Nat.floor_natCast]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [powerTailWeight, powerTailWeight, ← Real.rpow_add hn0]
    congr 1
    ring
  rw [hw]
  have hp : (∑ n ∈ Icc 1 N, powerTailWeight a n) = powerTailPrefix a N := by
    simp only [powerTailPrefix, Nat.floor_natCast]
  rw [hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The divergent powers cancel before the inverse cutoff is removed. -/
theorem mul_integral_cut_powerTailReferenceProfile {a : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    (1 - 2 * a) * (∫ t in Set.Ioc (0 : ℝ) 1,
      (Set.Ioi (1 / (N : ℝ))).indicator (powerTailReferenceProfile a) t) =
      (powerTailPrefix (1 - a) N - (N : ℝ) ^ a / a) -
        (N : ℝ) ^ (-(1 - 2 * a)) *
          (powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)) +
        (1 - 2 * a) / (a * (1 - a)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : 1 - a ≠ 0 := by linarith only [ha2]
  have hθ : 1 - 2 * a ≠ 0 := by linarith only [ha2]
  have hpow : (N : ℝ) ^ (-(1 - 2 * a)) * (N : ℝ) ^ (1 - a) = (N : ℝ) ^ a := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have he : (N : ℝ) ^ (-(1 - 2 * a)) *
      (powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)) =
        (N : ℝ) ^ (-(1 - 2 * a)) * powerTailPrefix a N - (N : ℝ) ^ a / (1 - a) := by
    rw [mul_sub, ← mul_div_assoc, hpow]
  rw [integral_cut_powerTailReferenceProfile ha ha2 hN, he]
  field_simp [ha.ne', hb, hθ]
  ring

/-- The reference integral contributes the continued zeta value and the
explicit polar constant. -/
theorem mul_referencePowerMellinIntegral_eq {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    (1 - 2 * (a : ℂ)) * ((∫ t in Set.Ioc (0 : ℝ) 1, powerTailReferenceProfile a t : ℝ) : ℂ) =
      riemannZeta (1 - (a : ℂ)) + (1 - 2 * (a : ℂ)) / ((a : ℂ) * (1 - (a : ℂ))) := by
  have hb : 0 < 1 - a := by linarith only [ha2]
  have hb1 : 1 - a < 1 := by linarith only [ha]
  have hcut := (tendsto_integral_inverse_cut (measurable_powerTailReferenceProfile a)
    (riemannOn_powerTailReferenceProfile ha ha2).1).const_mul (1 - 2 * a)
  have hcutC := Complex.continuous_ofReal.continuousAt.tendsto.comp hcut
  have hz := tendsto_rpow_mul_powerTailPrefix_error ha
    (show a < 1 by linarith only [ha2]) (show 0 < 1 - 2 * a by linarith only [ha2])
  have hzC := Complex.continuous_ofReal.continuousAt.tendsto.comp hz
  have hf := tendsto_powerTailPrefix_finitePart hb hb1
  simp only [show 1 - (1 - a) = a by ring, Complex.ofReal_sub, Complex.ofReal_one] at hf
  have hr := (hf.sub hzC).add_const
    (((1 - 2 * a) / (a * (1 - a)) : ℝ) : ℂ)
  simp only [Complex.ofReal_zero, sub_zero] at hr
  have hsame : (fun N : ℕ =>
      ((powerTailPrefix (1 - a) N - (N : ℝ) ^ a / a : ℝ) : ℂ) -
        (((N : ℝ) ^ (-(1 - 2 * a)) *
          (powerTailPrefix a N - (N : ℝ) ^ (1 - a) / (1 - a)) : ℝ) : ℂ) +
        (((1 - 2 * a) / (a * (1 - a)) : ℝ) : ℂ)) =ᶠ[atTop]
      (fun N : ℕ => (((1 - 2 * a) * (∫ t in Set.Ioc (0 : ℝ) 1,
        (Set.Ioi (1 / (N : ℝ))).indicator (powerTailReferenceProfile a) t) : ℝ) : ℂ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [mul_integral_cut_powerTailReferenceProfile ha ha2 hN]
    push_cast <;> rfl
  have heq := tendsto_nhds_unique hcutC (hr.congr' hsame)
  simpa only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using heq

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
