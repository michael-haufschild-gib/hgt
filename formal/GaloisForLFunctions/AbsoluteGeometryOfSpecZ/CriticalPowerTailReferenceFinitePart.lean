import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrefixQuantitativeFinitePart
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceProfile

/-!
# The logarithmic finite part of the critical reference mesh

Subtracting `ζ(1/2)/t` leaves a profile bounded by `t⁻¹ᐟ²`.
Its positive cutoffs already have convergent arithmetic meshes, so the
whole corrected mesh converges. The removed mesh is exactly harmonic.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Remove the critical reference profile's sole nonintegrable term. -/
def criticalPowerTailReferenceProfile (t : ℝ) : ℝ :=
  powerTailReferenceProfile (1 / 2) t - (riemannZeta ((1 / 2 : ℝ) : ℂ)).re / t

private theorem criticalPowerTailReferenceProfile_eq (t : ℝ) :
    criticalPowerTailReferenceProfile t =
      (powerTailPrefix (1 / 2) (1 / t) -
        (1 / t) ^ (1 - (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) -
        (riemannZeta ((1 / 2 : ℝ) : ℂ)).re) / t := by
  rw [criticalPowerTailReferenceProfile, powerTailReferenceProfile]
  simp only [show 2 * (1 / 2 : ℝ) = 1 by ring, Real.rpow_neg_one]
  ring

/-- The real-cutoff finite-part bound makes the corrected profile
integrable at zero. -/
theorem exists_criticalPowerTailReferenceProfile_powerBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      |criticalPowerTailReferenceProfile t| ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hB⟩ := exists_powerTailPrefix_real_finitePart_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨C, hC, fun t ht => ?_⟩
  have hX : 1 ≤ 1 / t := (le_div_iff₀ ht.1).mpr (by simpa only [one_mul] using ht.2)
  have hX0 : 0 ≤ 1 / t := one_div_nonneg.mpr ht.1.le
  have hb := hB (1 / t) hX
  have hcast :
      ((powerTailPrefix (1 / 2) (1 / t) -
        (1 / t) ^ (1 - (1 / 2 : ℝ)) / (1 - (1 / 2 : ℝ)) : ℝ) : ℂ) =
      (powerTailPrefix (1 / 2) (1 / t) : ℂ) -
        ((1 / t : ℝ) : ℂ) ^ (1 - ((1 / 2 : ℝ) : ℂ)) /
          (1 - ((1 / 2 : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_cpow hX0,
      Complex.ofReal_one]
  rw [← hcast] at hb
  have hp := (Complex.abs_re_le_norm _).trans hb
  simp only [Complex.sub_re, Complex.ofReal_re] at hp
  have hpow : (1 / t) ^ (-(1 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
    rw [one_div, Real.inv_rpow ht.1.le, ← Real.rpow_neg ht.1.le, neg_neg]
  rw [criticalPowerTailReferenceProfile_eq, abs_div, abs_of_pos ht.1]
  calc
    _ ≤ (C * (1 / t) ^ (-(1 / 2 : ℝ))) / t :=
      div_le_div_of_nonneg_right hp ht.1.le
    _ = C * (t ^ (1 / 2 : ℝ) * t ^ (-1 : ℝ)) := by
      rw [hpow, Real.rpow_neg_one]
      ring
    _ = _ := by rw [← Real.rpow_add ht.1]; norm_num

theorem measurable_criticalPowerTailReferenceProfile :
    Measurable criticalPowerTailReferenceProfile :=
  (measurable_powerTailReferenceProfile (1 / 2)).sub (measurable_const.div measurable_id)

/-- Every positive cutoff has a convergent corrected arithmetic mesh. -/
theorem riemannOn_cut_criticalPowerTailReferenceProfile {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    RiemannOn ((Set.Ioi δ).indicator criticalPowerTailReferenceProfile) := by
  have hr := riemannOn_cut_powerTailReferenceProfile
    (by norm_num : (0 : ℝ) < 1 / 2) hδ hδ1
  have hp := (riemannOn_rpow_interval (p := 1) zero_le_one hδ hδ1).const_mul
    (riemannZeta ((1 / 2 : ℝ) : ℂ)).re
  refine (hr.sub hp).congr fun t ht => ?_
  by_cases hδt : δ < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi δ from hδt),
      Set.indicator_of_mem (show t ∈ Set.Ioi δ from hδt),
      if_pos ⟨hδt, ht.2⟩, criticalPowerTailReferenceProfile, Real.rpow_neg_one]
    ring
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi δ from hδt),
      Set.indicator_of_notMem (show t ∉ Set.Ioi δ from hδt),
      if_neg (fun h => hδt h.1), mul_zero, sub_self]

/-- The critical reference profile has convergent meshes after removing
its harmonic singularity. -/
theorem riemannOn_criticalPowerTailReferenceProfile :
    RiemannOn criticalPowerTailReferenceProfile := by
  obtain ⟨C, _, hB⟩ := exists_criticalPowerTailReferenceProfile_powerBound
  exact riemannOn_of_powerBound_and_cuts
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    measurable_criticalPowerTailReferenceProfile hB
    (fun δ hδ hδ1 => riemannOn_cut_criticalPowerTailReferenceProfile hδ hδ1)

/-- The removed singularity contributes exactly the harmonic number. -/
theorem tailRiemannSum_criticalPowerTailReferenceProfile {N : ℕ} (hN : 1 ≤ N) :
    tailRiemannSum criticalPowerTailReferenceProfile N =
      tailRiemannSum (powerTailReferenceProfile (1 / 2)) N -
        (riemannZeta ((1 / 2 : ℝ) : ℂ)).re * harm N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tailRiemannSum, tailRiemannSum]
  simp only [criticalPowerTailReferenceProfile, sum_sub_distrib, sub_div]
  congr 1
  calc
    _ = ∑ n ∈ Icc 1 N, (riemannZeta ((1 / 2 : ℝ) : ℂ)).re / (n : ℝ) := by
      rw [sum_div]
      apply sum_congr rfl
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      field_simp [hNp.ne', hn0.ne'] <;> ring
    _ = _ := by
      rw [sum_Icc_one_shift, harm, mul_sum]
      apply sum_congr rfl
      intro n _
      simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]

/-- Constant left after subtracting the reference mesh's logarithm. -/
def criticalPowerTailReferenceFinitePart : ℝ :=
  (∫ t in Set.Ioc (0 : ℝ) 1, criticalPowerTailReferenceProfile t) +
    (riemannZeta ((1 / 2 : ℝ) : ℂ)).re * Real.eulerMascheroniConstant

theorem tendsto_criticalPowerTailReference_finitePart :
    Tendsto (fun N : ℕ => tailRiemannSum (powerTailReferenceProfile (1 / 2)) N -
      (riemannZeta ((1 / 2 : ℝ) : ℂ)).re * Real.log N) atTop
        (𝓝 criticalPowerTailReferenceFinitePart) := by
  have hh := tendsto_harm_sub_log.const_mul (riemannZeta ((1 / 2 : ℝ) : ℂ)).re
  apply (riemannOn_criticalPowerTailReferenceProfile.2.add hh).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [tailRiemannSum_criticalPowerTailReferenceProfile hN]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
