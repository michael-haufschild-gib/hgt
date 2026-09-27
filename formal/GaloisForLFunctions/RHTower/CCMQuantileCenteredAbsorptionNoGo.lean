import GaloisForLFunctions.RHTower.CCMQuantileDisplacementMass
import GaloisForLFunctions.RHTower.CCMGammaFractionalDensity

/-!
# No uniform scalar Gamma cap for the actual displaced prime cells

The centered transport estimate costs a full translation defect instead of
its square root. Even this improvement cannot absorb the whole positive
displacement density with one Gamma-density constant. The contradiction
uses the actual prime mass, its retained overlap height, and the integrable
three-quarter power of the higher Binet density. Domination is tested almost
everywhere, so the singular clock's assigned value at zero plays no role.

This excludes a scalar absorption method, not positivity of the signed
completed arithmetic source, which retains prime phases and the terminal.
-/

open MeasureTheory Set Filter
noncomputable section
namespace RHTower

private theorem gamma_abs_nonneg (r : ℝ) :
    0 ≤ ccmGammaHigherBinetModeDensity |r| := by
  by_cases hr : r = 0
  · simp [hr, ccmGammaHigherBinetModeDensity]
  · exact (ccmGammaHigherBinetModeDensity_pos (abs_pos.mpr hr)).le

private theorem mass_fourth_le_gamma_cap (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ᵐ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r ≤
      C * ccmGammaHigherBinetModeDensity |r|) :
    ccmOutgoingPrimeCumulative N ^ 4 ≤
      (N : ℝ) * (1 + ccmOutgoingPrimeCumulative N / 2) *
        (C ^ (3 / 4 : ℝ) *
          (∫ r : ℝ, ccmGammaHigherBinetModeDensity |r| ^ (3 / 4 : ℝ))) ^ 4 := by
  let H : ℝ := (N : ℝ) * (1 + ccmOutgoingPrimeCumulative N / 2)
  have hH : 0 ≤ H := by
    dsimp only [H]
    have hM := ccmOutgoingPrimeCumulative_nonneg N
    positivity
  have hpoint : ∀ᵐ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r ≤
      (H ^ (1 / 4 : ℝ) * C ^ (3 / 4 : ℝ)) *
        ccmGammaHigherBinetModeDensity |r| ^ (3 / 4 : ℝ) := by
    filter_upwards [hcap] with r hr
    let d := ccmOutgoingQuantileDisplacementDensity N r
    have hd : 0 ≤ d := ccmOutgoingQuantileDisplacementDensity_nonneg N r
    by_cases hz : d = 0
    · change d ≤ _
      rw [hz]
      have hg := gamma_abs_nonneg r
      positivity
    have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    calc
      d = d ^ (1 / 4 : ℝ) * d ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hdpos]
        norm_num
      _ ≤ H ^ (1 / 4 : ℝ) *
          (C * ccmGammaHigherBinetModeDensity |r|) ^ (3 / 4 : ℝ) :=
        mul_le_mul
          (Real.rpow_le_rpow hd (ccmOutgoingQuantileDisplacementDensity_le_height N r)
            (by norm_num))
          (Real.rpow_le_rpow hd hr (by norm_num))
          (Real.rpow_nonneg hd _) (Real.rpow_nonneg hH _)
      _ = _ := by
        rw [Real.mul_rpow hC (gamma_abs_nonneg r)]
        ring
  have hmajor := integrable_ccmGammaHigherBinetSymmetricDensity_threeQuarters.const_mul
    (H ^ (1 / 4 : ℝ) * C ^ (3 / 4 : ℝ))
  have hi := integral_mono_ae (integrable_ccmOutgoingQuantileDisplacementDensity N)
    hmajor hpoint
  rw [integral_ccmOutgoingQuantileDisplacementDensity, integral_const_mul] at hi
  have hfour := pow_le_pow_left₀ (ccmOutgoingPrimeCumulative_nonneg N) hi 4
  have hroot : (H ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = H := by
    rw [← Real.rpow_mul_natCast hH]
    norm_num
  rw [mul_assoc, mul_pow, hroot] at hfour
  exact hfour

/-- Every fixed scalar Gamma cap fails on all sufficiently large actual
prime heads, even after ignoring null sets. -/
theorem eventually_not_ccmOutgoingQuantileDisplacement_Gamma_cap
    (C : {C : ℝ // 0 ≤ C}) :
    ∀ᶠ N : ℕ in atTop, ¬
      ∀ᵐ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r ≤
        (C : ℝ) * ccmGammaHigherBinetModeDensity |r| := by
  rcases C with ⟨C, hC⟩
  suffices hsucc : ∀ᶠ N : ℕ in atTop, ¬
      ∀ᵐ r : ℝ, ccmOutgoingQuantileDisplacementDensity (N + 1) r ≤
        C * ccmGammaHigherBinetModeDensity |r| by
    exact (Filter.eventually_atTop.2 (by
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hsucc
      refine ⟨n + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact hn k (by omega)))
  let A : ℝ := (C ^ (3 / 4 : ℝ) *
    (∫ r : ℝ, ccmGammaHigherBinetModeDensity |r| ^ (3 / 4 : ℝ))) ^ 4
  let c : ℝ := Real.log 2 / 2
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hlow : ∀ᶠ N : ℕ in atTop,
      c * Real.sqrt (N : ℝ) ≤ ccmOutgoingPrimeCumulative (N + 1) :=
    eventually_sqrt_le_ccmOutgoingPrimeCumulative
  have hgrowth : Tendsto (fun N : ℕ => ccmOutgoingPrimeCumulative (N + 1)) atTop atTop :=
    tendsto_atTop_mono' atTop hlow
      (Filter.Tendsto.const_mul_atTop hc
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  have hcgrowth := Filter.Tendsto.const_mul_atTop (sq_pos_of_pos hc) hgrowth
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlow,
    hgrowth.eventually_ge_atTop 2, hcgrowth.eventually_gt_atTop (2 * A)]
    with N hN hlowN hM hlarge
  intro hcap
  let M := ccmOutgoingPrimeCumulative (N + 1)
  have hNpos : (0 : ℝ) < N := by
    have hn : 0 < N := by omega
    exact_mod_cast hn
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMpos : 0 < M := by dsimp only [M]; linarith
  have hfour := mass_fourth_le_gamma_cap (N + 1) C hC hcap
  change M ^ 4 ≤ ((N + 1 : ℕ) : ℝ) * (1 + M / 2) * A at hfour
  push_cast at hfour
  have hcube : M ^ 3 ≤ ((N : ℝ) + 1) * A := by
    apply le_of_mul_le_mul_right (a := M) ?_ hMpos
    calc
      M ^ 3 * M = M ^ 4 := by ring
      _ ≤ ((N : ℝ) + 1) * (1 + M / 2) * A := hfour
      _ ≤ (((N : ℝ) + 1) * A) * M := by
        have hb : 1 + M / 2 ≤ M := by dsimp only [M]; linarith
        nlinarith only [mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb hA) (by positivity : 0 ≤ (N : ℝ) + 1)]
  have hsquare : c ^ 2 * (N : ℝ) ≤ M ^ 2 := by
    have hs := pow_le_pow_left₀ (mul_nonneg hc.le (Real.sqrt_nonneg _)) hlowN 2
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] using hs
  have hlower := mul_le_mul_of_nonneg_right hsquare hMpos.le
  have hupper : ((N : ℝ) + 1) * A ≤ 2 * (N : ℝ) * A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNge) hA]
  have hstrict := mul_lt_mul_of_pos_left hlarge hNpos
  change 2 * A < c ^ 2 * M at hlarge
  nlinarith only [hlower, hcube, hupper, hstrict]

/-- Centering cannot justify replacing the full signed prime transport by
one uniformly Gamma-dominated positive displacement density. -/
theorem not_exists_uniform_ccmOutgoingQuantileDisplacement_Gamma_cap :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∀ᵐ r : ℝ, ccmOutgoingQuantileDisplacementDensity N r ≤
        C * ccmGammaHigherBinetModeDensity |r| := by
  rintro ⟨C, hC, hall⟩
  obtain ⟨N, hN⟩ := (eventually_not_ccmOutgoingQuantileDisplacement_Gamma_cap ⟨C, hC⟩).exists
  exact hN (hall N)

end RHTower
