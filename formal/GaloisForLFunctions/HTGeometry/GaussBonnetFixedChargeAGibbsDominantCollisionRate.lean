import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsNormalizedCollision

/-!
# A complete collision-rate classification

Every Gibbs input to the critical thermal kernel has one of three asymptotic
collision behaviors: immediate equilibrium, the fast rate, or the slow rate.
The selection is determined by its two initial nonconstant Fourier energies.
-/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section

/-- The spectral rate selected by an arbitrary Gibbs energy landscape. -/
def egbFixedChargeAGibbsDominantCollisionRate (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  if egbFixedChargeAGibbsSlowModeEnergy n β E = 0 then
    if egbFixedChargeAGibbsFastModeEnergy n β E = 0 then 0 else 1 / 36
  else 4 / 9

/-- The exact three-way spectral classification is the actual consecutive collision ratio limit. -/
theorem egbFixedChargeAGibbsCollisionExcess_step_ratio_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => egbFixedChargeAGibbsCollisionExcess n (m + 2) β E /
      egbFixedChargeAGibbsCollisionExcess n (m + 1) β E) atTop
        (nhds (egbFixedChargeAGibbsDominantCollisionRate n β E)) := by
  unfold egbFixedChargeAGibbsDominantCollisionRate
  split_ifs with ha hb
  · have hz (m : ℕ) : egbFixedChargeAGibbsCollisionExcess n (m + 1) β E = 0 :=
      (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n m β E).mpr ⟨ha, hb⟩
    have he (m : ℕ) : egbFixedChargeAGibbsCollisionExcess n (m + 2) β E /
        egbFixedChargeAGibbsCollisionExcess n (m + 1) β E = 0 := by
      rw [hz (m + 1), hz m, zero_div]
    simpa only [he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · have he (m : ℕ) : egbFixedChargeAGibbsCollisionExcess n (m + 2) β E /
        egbFixedChargeAGibbsCollisionExcess n (m + 1) β E = (1 / 36 : ℝ) := by
      have hq : (1 / 36 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [egbFixedChargeAGibbsCollisionExcess_two_rate n (m + 1) β E,
        egbFixedChargeAGibbsCollisionExcess_two_rate n m β E, ha]
      simp only [mul_zero, zero_add]
      rw [pow_succ (1 / 36 : ℝ) (m + 1)]
      field_simp
      <;> ring
    simpa only [he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 36 : ℝ)) atTop (nhds (1 / 36 : ℝ)))
  · have hA : 0 < egbFixedChargeAGibbsSlowModeEnergy n β E :=
      lt_of_le_of_ne (egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E) (by intro h; exact ha h.symm)
    have h := egbFixedChargeAGibbsNormalizedCollision_limit n β E
    have h1 := (Filter.tendsto_add_atTop_iff_nat
      (f := fun m => egbFixedChargeAGibbsNormalizedCollision n m β E) 1).mpr h
    have h2 := (Filter.tendsto_add_atTop_iff_nat
      (f := fun m => egbFixedChargeAGibbsNormalizedCollision n m β E) 2).mpr h
    have hc : Tendsto (fun _ : ℕ => (4 / 9 : ℝ)) atTop (nhds (4 / 9 : ℝ)) := tendsto_const_nhds
    have ht := hc.mul (h2.div h1 ha)
    have he (m : ℕ) : egbFixedChargeAGibbsCollisionExcess n (m + 2) β E /
        egbFixedChargeAGibbsCollisionExcess n (m + 1) β E =
        (4 / 9 : ℝ) * (egbFixedChargeAGibbsNormalizedCollision n (m + 2) β E /
          egbFixedChargeAGibbsNormalizedCollision n (m + 1) β E) := by
      have hq : (4 / 9 : ℝ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
      have hd := ((egbFixedChargeAGibbsCollisionExcess_positive_time_pos_iff n m β E).mpr (Or.inl hA)).ne'
      unfold egbFixedChargeAGibbsNormalizedCollision
      rw [pow_succ (4 / 9 : ℝ) (m + 1)]
      field_simp
      <;> ring
    simp_rw [he]
    simpa only [Pi.div_def, div_self ha, mul_one] using ht

end
end GaloisForLFunctions.HTGeometry
