import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanLimit
import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds

/-!
# Quantitative mesh error for the critical archimedean jet

At exponent one half the regularized jet is a sum of two decreasing
positive quotients. Integral comparison confines its mesh error to the
first cell, whose power envelope has integral `4 / √N`.
-/

noncomputable section

open Finset MeasureTheory Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Rationalizing the divided difference exposes two decreasing terms. -/
theorem powerTailJetProfile_half_eq {t : ℝ} (ht : 0 < t) :
    powerTailJetProfile (1 / 2) t =
      t ^ (-(1 / 2 : ℝ)) / (1 + t ^ (1 / 2 : ℝ)) +
        t ^ (-(1 / 2 : ℝ)) / (1 + t) := by
  by_cases ht1 : t = 1
  · subst t
    norm_num [powerTailJetProfile]
  have hu : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
  have hw : t ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
  have hwt : t ^ (-(1 / 2 : ℝ)) * t = t ^ (1 / 2 : ℝ) := by
    calc
      _ = t ^ (-(1 / 2 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ht]; norm_num
  rw [powerTailJetProfile, if_neg ht1]
  congr 1
  field_simp [sub_ne_zero.mpr (fun h : (1 : ℝ) = t => ht1 h.symm),
    (show 1 + t ^ (1 / 2 : ℝ) ≠ 0 by positivity)]
  nlinarith only [hw, hwt]

/-- The critical jet decreases throughout the positive unit interval. -/
theorem antitoneOn_powerTailJetProfile_half :
    AntitoneOn (powerTailJetProfile (1 / 2)) (Ioc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx.1
  have hy0 : 0 < y := hy.1
  rw [powerTailJetProfile_half_eq hy.1, powerTailJetProfile_half_eq hx.1]
  have hw := Real.rpow_le_rpow_of_nonpos hx.1 hxy (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hu := Real.rpow_le_rpow hx.1.le hxy (by norm_num : 0 ≤ (1 / 2 : ℝ))
  apply add_le_add
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul hw (add_le_add le_rfl hu) (by positivity) (by positivity)
  · rw [div_le_div_iff₀ (by linarith only [hy.1]) (by linarith only [hx.1])]
    exact mul_le_mul hw (add_le_add le_rfl hxy) (by linarith only [hx.1]) (by positivity)

private theorem antitone_power_mesh_error_le
    {g : ℝ → ℝ} {a C : ℝ} (ha1 : a < 1)
    (hg : ContinuousOn g (Ioc (0 : ℝ) 1))
    (hanti : AntitoneOn g (Ioc (0 : ℝ) 1))
    (hnn : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ g t)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, |g t| ≤ C * t ^ (-a))
    {N : ℕ} (hN : 1 ≤ N) :
    |(∫ t in Ioc (0 : ℝ) 1, g t) - tailRiemannSum g N| ≤
      C * ((1 / (N : ℝ)) ^ (1 - a) / (1 - a)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 < 1 / (N : ℝ) := by positivity
  have hδ1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNp]
    exact_mod_cast hN
  have hi := intervalIntegrable_of_powerTailBound ha1 hg hB
  have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi
  have hleft : IntervalIntegrable g volume 0 (1 / (N : ℝ)) := hi.mono_set (by
    rw [Set.uIcc_of_le hδ.le, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_right hδ1)
  have hright : IntervalIntegrable g volume (1 / (N : ℝ)) 1 := hi.mono_set (by
    rw [Set.uIcc_of_le hδ1, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc_left hδ.le)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [intervalIntegral.integral_of_le zero_le_one] at hsplit
  have hp : IntervalIntegrable (fun t : ℝ => C * t ^ (-a)) volume 0 (1 / (N : ℝ)) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith only [ha1])).const_mul C
  have hhead : |∫ t in (0 : ℝ)..(1 / (N : ℝ)), g t| ≤
      C * ((1 / (N : ℝ)) ^ (1 - a) / (1 - a)) := by
    have hpi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mp hp
    have hb : |∫ t in (0 : ℝ)..(1 / (N : ℝ)), g t| ≤
        ∫ t in (0 : ℝ)..(1 / (N : ℝ)), C * t ^ (-a) := by
      rw [intervalIntegral.integral_of_le hδ.le, intervalIntegral.integral_of_le hδ.le,
        ← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hpi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_eq_abs]
      exact hB t ⟨ht.1, ht.2.trans hδ1⟩
    apply hb.trans_eq
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith only [ha1])),
      show -a + 1 = 1 - a by ring, Real.zero_rpow (by linarith only [ha1]), sub_zero]
  have hup := tailRiemannSum_le_integral hanti hint hN
  have hlo := integral_le_tailRiemannSum hanti hnn hint hN
  rw [abs_of_nonneg (sub_nonneg.mpr hup)]
  linarith only [hsplit, hlo, (le_abs_self _).trans hhead]

/-- The critical jet mesh has error at most `4 / √N`. -/
theorem abs_criticalPowerTailJet_mesh_error_le {N : ℕ} (hN : 1 ≤ N) :
    |(∫ t in Ioc (0 : ℝ) 1, powerTailJetProfile (1 / 2) t) -
      tailRiemannSum (powerTailJetProfile (1 / 2)) N| ≤
        4 * (1 / (N : ℝ)) ^ (1 / 2 : ℝ) := by
  have hnn : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ powerTailJetProfile (1 / 2) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [powerTailJetProfile_half_eq ht.1]
    positivity
  have h := antitone_power_mesh_error_le (by norm_num : (1 / 2 : ℝ) < 1)
    (continuousOn_powerTailJetProfile (1 / 2)) antitoneOn_powerTailJetProfile_half hnn
    (fun t ht => abs_powerTailJetProfile_le (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) ht) hN
  convert h using 1 <;> norm_num <;> ring

/-- The critical row approaches its limit fast enough for harmonic
weighting to leave an absolutely summable error. -/
theorem abs_criticalPowerTailArchimedeanRow_error_le (N : ℕ) :
    |powerTailArchimedeanRow (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2)| ≤
      (5 / 2 : ℝ) / (N + 1) + 4 * (1 / (N + 1 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hh := _root_.RHTower.harmonic_mascheroni_half_bounds
    (show 1 ≤ N + 1 by omega)
  have hh0 : 0 ≤ harm (N + 1) - Real.log (N + 1 : ℕ) -
      Real.eulerMascheroniConstant := by
    rw [harm_eq_harmonic]
    exact (by positivity : (0 : ℝ) ≤ 1 / (2 * (((N + 1 : ℕ) : ℝ) + 1))).trans hh.1
  have hH : |harm (N + 1) - Real.log (N + 1 : ℕ) -
      Real.eulerMascheroniConstant| ≤ 1 / (2 * ((N + 1 : ℕ) : ℝ)) := by
    rw [abs_of_nonneg hh0, harm_eq_harmonic]
    exact hh.2
  have hmesh := abs_criticalPowerTailJet_mesh_error_le (show 1 ≤ N + 1 by omega)
  have he : powerTailArchimedeanRow (1 / 2) N - powerTailArchimedeanRowLimit (1 / 2) =
      -(harm (N + 1) - Real.log (N + 1 : ℕ) - Real.eulerMascheroniConstant) +
        ((∫ t in Ioc (0 : ℝ) 1, powerTailJetProfile (1 / 2) t) -
          tailRiemannSum (powerTailJetProfile (1 / 2)) (N + 1)) +
        2 / ((N + 1 : ℕ) : ℝ) := by
    rw [powerTailArchimedeanRow_eq, powerTailArchimedeanRowLimit,
      intervalIntegral.integral_of_le zero_le_one,
      show powerTailJetProfile (1 / 2) 1 = 1 by norm_num [powerTailJetProfile]]
    push_cast
    ring
  rw [he]
  calc
    _ ≤ |-(harm (N + 1) - Real.log (N + 1 : ℕ) - Real.eulerMascheroniConstant)| +
        |(∫ t in Ioc (0 : ℝ) 1, powerTailJetProfile (1 / 2) t) -
          tailRiemannSum (powerTailJetProfile (1 / 2)) (N + 1)| +
        |2 / ((N + 1 : ℕ) : ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 / (2 * ((N + 1 : ℕ) : ℝ)) +
        4 * (1 / ((N + 1 : ℕ) : ℝ)) ^ (1 / 2 : ℝ) + 2 / ((N + 1 : ℕ) : ℝ) := by
      rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 / ((N + 1 : ℕ) : ℝ))]
      exact add_le_add (add_le_add hH hmesh) le_rfl
    _ = _ := by
      push_cast
      field_simp [show (N : ℝ) + 1 ≠ 0 by positivity]
      <;> ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
