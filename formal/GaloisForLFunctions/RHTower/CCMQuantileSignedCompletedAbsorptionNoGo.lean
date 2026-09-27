import GaloisForLFunctions.RHTower.CCMQuantileSignedCompletedMass
import GaloisForLFunctions.RHTower.CCMGammaFractionalCapacity

/-!
# Signed terminal completion has no uniform scalar Gamma cap

Use actual canonical heads with endpoint `T = 2 log (n+1)` and cutoff
`floor (exp T) + 1 = (n+1)^2 + 1`. Terminal orientation and bulk overlaps
are retained before taking the absolute value. Their signed total mass is
`2n`, whereas their height is at most `10(n+1)^4`. Fractional Gamma
integrability forces a contradiction to any fixed almost-everywhere cap.

This rules out a scalar-density absorption mechanism. It asserts neither
negativity of an actual xi Hankel form nor failure of phase-sensitive
estimates for the full translated coherent field.
-/

open MeasureTheory Set Filter
noncomputable section
namespace RHTower

private theorem exp_half_canonical_endpoint (n : ℕ) :
    Real.exp ((2 * Real.log ((n : ℝ) + 1)) / 2) = (n : ℝ) + 1 := by
  rw [show 2 * Real.log ((n : ℝ) + 1) / 2 = Real.log ((n : ℝ) + 1) by ring,
    Real.exp_log (by positivity)]

theorem ccmQuantileSquareHead_canonical_cutoff (n : ℕ) :
    ⌊Real.exp (2 * Real.log ((n : ℝ) + 1))⌋₊ + 1 = (n + 1) ^ 2 + 1 := by
  have he : Real.exp (2 * Real.log ((n : ℝ) + 1)) = (((n + 1) ^ 2 : ℕ) : ℝ) := by
    rw [show 2 * Real.log ((n : ℝ) + 1) =
      Real.log ((n : ℝ) + 1) + Real.log ((n : ℝ) + 1) by ring,
      Real.exp_add, Real.exp_log (by positivity)]
    push_cast
    ring
  rw [he, Nat.floor_natCast]

theorem integral_ccmActualHeadQuantileCompletedDisplacementDensity_squareHead (n : ℕ) :
    (∫ r : ℝ, ccmActualHeadQuantileCompletedDisplacementDensity
      (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1) r) = 2 * (n : ℝ) := by
  rw [integral_ccmActualHeadQuantileCompletedDisplacementDensity,
    exp_half_canonical_endpoint]
  ring

theorem abs_ccmActualHeadQuantileCompletedDisplacementDensity_squareHead_le
    (n : ℕ) (r : ℝ) :
    |ccmActualHeadQuantileCompletedDisplacementDensity
      (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1) r| ≤
        10 * ((n : ℝ) + 1) ^ 4 := by
  have hh := abs_ccmActualHeadQuantileCompletedDisplacementDensity_le_height
    (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1) r
  rw [exp_half_canonical_endpoint] at hh
  push_cast at hh
  have hx : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsq := le_self_pow₀ hx (by decide : (2 : ℕ) ≠ 0)
  have hfour := le_self_pow₀ hx (by decide : (4 : ℕ) ≠ 0)
  have hbase : ((n : ℝ) + 1) ^ 2 + 1 + 1 ≤ 3 * ((n : ℝ) + 1) ^ 2 := by
    linarith
  have hp := pow_le_pow_left₀ (by positivity :
    0 ≤ ((n : ℝ) + 1) ^ 2 + 1 + 1) hbase 2
  nlinarith

private theorem gamma_abs_nonneg (r : ℝ) :
    0 ≤ ccmGammaHigherBinetModeDensity |r| := by
  by_cases hr : r = 0
  · simp [hr, ccmGammaHigherBinetModeDensity]
  · exact (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le

private theorem squareHead_mass_eighth_le_gamma_cap (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ᵐ r : ℝ,
      ccmActualHeadQuantileCompletedDisplacementDensity
        (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1) r ≤
          C * ccmGammaHigherBinetModeDensity |r|) :
    (2 * (n : ℝ)) ^ 8 ≤ 10 * ((n : ℝ) + 1) ^ 4 *
      (C ^ (7 / 8 : ℝ) *
        (∫ r : ℝ, ccmGammaHigherBinetModeDensity |r| ^ (7 / 8 : ℝ))) ^ 8 := by
  let F := ccmActualHeadQuantileCompletedDisplacementDensity
    (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1)
  let H : ℝ := 10 * ((n : ℝ) + 1) ^ 4
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hpoint : ∀ᵐ r : ℝ, F r ≤
      (H ^ (1 / 8 : ℝ) * C ^ (7 / 8 : ℝ)) *
        ccmGammaHigherBinetModeDensity |r| ^ (7 / 8 : ℝ) := by
    filter_upwards [hcap] with r hr
    by_cases hz : F r ≤ 0
    · apply hz.trans
      have hg := gamma_abs_nonneg r
      positivity
    have hd : 0 < F r := lt_of_not_ge hz
    calc
      F r = F r ^ (1 / 8 : ℝ) * F r ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_add hd]
        norm_num
      _ ≤ H ^ (1 / 8 : ℝ) *
          (C * ccmGammaHigherBinetModeDensity |r|) ^ (7 / 8 : ℝ) :=
        mul_le_mul
          (Real.rpow_le_rpow hd.le
            ((le_abs_self (F r)).trans
              (abs_ccmActualHeadQuantileCompletedDisplacementDensity_squareHead_le n r))
            (by norm_num))
          (Real.rpow_le_rpow hd.le hr (by norm_num))
          (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hH _)
      _ = _ := by
        rw [Real.mul_rpow hC (gamma_abs_nonneg r)]
        ring
  have hf : Integrable F :=
    integrable_ccmActualHeadQuantileCompletedDisplacementDensity _ _
  have hgamma : Integrable
      (fun r : ℝ => ccmGammaHigherBinetModeDensity |r| ^ (7 / 8 : ℝ)) :=
    integrable_ccmGammaHigherBinetSymmetricDensity_fractional ⟨7 / 8, by norm_num⟩
  have hmajor := hgamma.const_mul (H ^ (1 / 8 : ℝ) * C ^ (7 / 8 : ℝ))
  have hi := integral_mono_ae hf hmajor hpoint
  change (∫ r : ℝ, ccmActualHeadQuantileCompletedDisplacementDensity _ _ r) ≤ _ at hi
  rw [integral_ccmActualHeadQuantileCompletedDisplacementDensity_squareHead,
    integral_const_mul] at hi
  have height := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (n : ℝ)) hi 8
  have hroot : (H ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = H := by
    rw [← Real.rpow_mul_natCast hH]
    norm_num
  rw [mul_assoc, mul_pow (H ^ (1 / 8 : ℝ)), hroot] at height
  exact height

theorem eventually_not_ccmActualHeadQuantileCompletedDisplacement_signed_Gamma_cap
    (C : {C : ℝ // 0 ≤ C}) :
    ∀ᶠ n : ℕ in atTop, ¬ ∀ᵐ r : ℝ,
      ccmActualHeadQuantileCompletedDisplacementDensity
        (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1) r ≤
          (C : ℝ) * ccmGammaHigherBinetModeDensity |r| := by
  let A : ℝ := ((C : ℝ) ^ (7 / 8 : ℝ) *
    (∫ r : ℝ, ccmGammaHigherBinetModeDensity |r| ^ (7 / 8 : ℝ))) ^ 8
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hgrowth : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hgrowth.eventually_gt_atTop A]
    with n hn hlarge
  intro hcap
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hmass := squareHead_mass_eighth_le_gamma_cap n C C.property hcap
  change (2 * (n : ℝ)) ^ 8 ≤ 10 * ((n : ℝ) + 1) ^ 4 * A at hmass
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 1)
    (show (n : ℝ) + 1 ≤ 2 * (n : ℝ) by linarith) 4
  have hupper : 10 * ((n : ℝ) + 1) ^ 4 * A ≤ 160 * (n : ℝ) ^ 4 * A := by
    nlinarith [mul_le_mul_of_nonneg_right hp hA]
  have hcancel : 256 * (n : ℝ) ^ 4 ≤ 160 * A := by
    apply le_of_mul_le_mul_right (a := (n : ℝ) ^ 4) ?_ (pow_pos hnpos _)
    calc
      256 * (n : ℝ) ^ 4 * (n : ℝ) ^ 4 = (2 * (n : ℝ)) ^ 8 := by ring
      _ ≤ 160 * (n : ℝ) ^ 4 * A := hmass.trans hupper
      _ = 160 * A * (n : ℝ) ^ 4 := by ring
  have hfour := le_self_pow₀ hnR (by decide : (4 : ℕ) ≠ 0)
  nlinarith

theorem eventually_not_ccmActualHeadQuantileCompletedDisplacement_Gamma_cap
    (C : {C : ℝ // 0 ≤ C}) :
    ∀ᶠ n : ℕ in atTop, ¬ ∀ᵐ r : ℝ,
      |ccmActualHeadQuantileCompletedDisplacementDensity
        (2 * Real.log ((n : ℝ) + 1)) ((n + 1) ^ 2 + 1) r| ≤
          (C : ℝ) * ccmGammaHigherBinetModeDensity |r| := by
  filter_upwards [eventually_not_ccmActualHeadQuantileCompletedDisplacement_signed_Gamma_cap C]
    with n hn
  intro hcap
  apply hn
  filter_upwards [hcap] with r hr
  exact (le_abs_self _).trans hr

theorem not_exists_uniform_ccmActualHeadQuantileCompletedDisplacement_signed_Gamma_cap :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : {T : ℝ // 0 < T},
      ∀ᵐ r : ℝ,
        ccmActualHeadQuantileCompletedDisplacementDensity T (⌊Real.exp T⌋₊ + 1) r ≤
          C * ccmGammaHigherBinetModeDensity |r| := by
  rintro ⟨C, hC, hcap⟩
  obtain ⟨n, hn, hN⟩ := ((eventually_not_ccmActualHeadQuantileCompletedDisplacement_signed_Gamma_cap
    ⟨C, hC⟩).and (eventually_ge_atTop (1 : ℕ))).exists
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hN
  have hT : 0 < 2 * Real.log ((n : ℝ) + 1) :=
    mul_pos (by norm_num) (Real.log_pos (by linarith))
  apply hn
  simpa only [ccmQuantileSquareHead_canonical_cutoff] using hcap
    ⟨2 * Real.log ((n : ℝ) + 1), hT⟩

theorem not_exists_uniform_ccmActualHeadQuantileCompletedDisplacement_Gamma_cap :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : {T : ℝ // 0 < T},
      ∀ᵐ r : ℝ,
        |ccmActualHeadQuantileCompletedDisplacementDensity T (⌊Real.exp T⌋₊ + 1) r| ≤
          C * ccmGammaHigherBinetModeDensity |r| := by
  rintro ⟨C, hC, hcap⟩
  apply not_exists_uniform_ccmActualHeadQuantileCompletedDisplacement_signed_Gamma_cap
  refine ⟨C, hC, fun T => ?_⟩
  filter_upwards [hcap T] with r hr
  exact (le_abs_self _).trans hr

end RHTower
