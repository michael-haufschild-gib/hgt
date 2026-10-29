import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ExactSuccessorShellWindows
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanCrossTermsVanishOnPeriodicProfiles

/-!
# A fixed overlap has a logarithmic downward divisor fiber

With the Schur weights `n^(-1/2)`, all divisors of a product `ℓ` have the same
lag and their Mangoldt coefficients sum to `log ℓ`. For the actual smooth
plateau at width `c/N`, the normalized fiber from row `N` to product `N+1`
is asymptotic to a positive multiple of `log(N+1)` at every fixed `c>1`.
This is a weighted row statement, not an unweighted operator norm estimate.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory Filter Topology _root_.RHTower

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory

/-- One product fiber in the downward prime row, with the corpus's Schur weights. -/
def weightedDownwardDivisorFiber (g : ℝ → ℝ) (m ℓ : ℕ) : ℝ :=
  ∑ k ∈ ℓ.divisors, vonMangoldtAtom k * Real.sqrt ((m : ℝ) / (ℓ / k : ℕ)) *
    bumpCorr g (Real.log k - (Real.log m - Real.log (ℓ / k : ℕ)))

/-- Every nonzero Mangoldt term in the successor product is a genuine non-ratio
edge inside the atom horizon. The divisor `1` has zero Mangoldt coefficient. -/
theorem successor_divisor_in_horizon {N k : ℕ} (hN : 1 ≤ N)
    (hk : k ∈ (N + 1).divisors) (hk1 : k ≠ 1) :
    (N + 1) / k ∈ Icc 1 N ∧ N ≠ k * ((N + 1) / k) := by
  have hkpos := Nat.pos_of_mem_divisors hk
  have hkdvd := Nat.dvd_of_mem_divisors hk
  have hqpos : 0 < (N + 1) / k :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hkdvd) hkpos
  have hprod : k * ((N + 1) / k) = N + 1 := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hkdvd]
  have hk2 : 2 ≤ k := by omega
  have hq : (N + 1) / k ≤ N := by
    nlinarith only [hprod, hk2, hqpos, hN]
  exact ⟨mem_Icc.mpr ⟨hqpos, hq⟩, by omega⟩

/-- The exact divisor sum leaves one autocorrelation value and the charge `log ℓ`. -/
theorem weightedDownwardDivisorFiber_eq (g : ℝ → ℝ) {m ℓ : ℕ}
    (hm : 0 < m) (hℓ : 0 < ℓ) :
    weightedDownwardDivisorFiber g m ℓ =
      Real.sqrt ((m : ℝ) / ℓ) * Real.log ℓ * bumpCorr g (Real.log ℓ - Real.log m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm : ∀ k ∈ ℓ.divisors,
      vonMangoldtAtom k * Real.sqrt ((m : ℝ) / (ℓ / k : ℕ)) *
          bumpCorr g (Real.log k - (Real.log m - Real.log (ℓ / k : ℕ))) =
        ArithmeticFunction.vonMangoldt k *
          (Real.sqrt ((m : ℝ) / ℓ) * bumpCorr g (Real.log ℓ - Real.log m)) := by
    intro k hk
    have hkpos := Nat.pos_of_mem_divisors hk
    have hkdiv := Nat.dvd_of_mem_divisors hk
    have hnpos : 0 < ℓ / k := Nat.div_pos (Nat.le_of_dvd hℓ hkdiv) hkpos
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hn0 : (0 : ℝ) < (ℓ / k : ℕ) := by exact_mod_cast hnpos
    have hprod : (k : ℝ) * (ℓ / k : ℕ) = ℓ := by
      exact_mod_cast ((Nat.mul_comm k (ℓ / k)).trans (Nat.div_mul_cancel hkdiv))
    have hlog : Real.log k + Real.log (ℓ / k : ℕ) = Real.log ℓ := by
      rw [← Real.log_mul hk0.ne' hn0.ne', hprod]
    have hlag : Real.log k - (Real.log m - Real.log (ℓ / k : ℕ)) =
        Real.log ℓ - Real.log m := by linarith only [hlog]
    rw [hlag]
    by_cases hk1 : k = 1
    · subst k
      simp only [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : 1 < 2),
        ArithmeticFunction.vonMangoldt_apply_one, zero_mul]
    have hk2 : 2 ≤ k := by omega
    have hsqrt : Real.sqrt ((m : ℝ) / (ℓ / k : ℕ)) =
        Real.sqrt k * Real.sqrt ((m : ℝ) / ℓ) := by
      rw [← Real.sqrt_mul hk0.le]
      congr 1
      rw [← hprod]
      field_simp
    have hweight : vonMangoldtAtom k * Real.sqrt ((m : ℝ) / (ℓ / k : ℕ)) =
        ArithmeticFunction.vonMangoldt k * Real.sqrt ((m : ℝ) / ℓ) := by
      rw [vonMangoldtAtom_eq hk2, hsqrt, ← mul_assoc,
        div_mul_cancel₀ _ (Real.sqrt_pos.mpr hk0).ne']
    rw [hweight]
    ring
  rw [weightedDownwardDivisorFiber, sum_congr rfl hterm, ← sum_mul,
    ArithmeticFunction.vonMangoldt_sum]
  ring

theorem bumpCorr_atomDilate {w : ℝ} (hw : 0 < w) (φ : ℝ → ℝ) (t : ℝ) :
    bumpCorr (atomDilate φ w) t = w * bumpCorr φ (t / w) := by
  have h := MeasureTheory.Measure.integral_comp_div
    (fun u => φ u * φ (u + t / w)) w
  simp only [smul_eq_mul, abs_of_pos hw] at h
  simpa only [bumpCorr, atomDilate, add_div] using h

/-- The explicit plateau's autocorrelation is positive throughout its open support. -/
theorem transMetzlerProfile_bumpCorr_pos {t : ℝ} (ht : |t| < 1) :
    0 < bumpCorr transMetzlerProfile t := by
  have hc : Continuous fun u => transMetzlerProfile u * transMetzlerProfile (u + t) :=
    contDiff_transMetzlerProfile.continuous.mul
      (contDiff_transMetzlerProfile.continuous.comp (continuous_id.add continuous_const))
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_transMetzlerProfile.mul_right
    (fun u => mul_nonneg (transMetzlerProfile_nonneg u) (transMetzlerProfile_nonneg (u + t)))
    (x := (1 - t) / 2)
  have h₁ : 0 < transMetzlerProfile ((1 - t) / 2) :=
    transMetzlerProfile_pos ⟨by linarith only [(abs_lt.mp ht).2],
      by linarith only [(abs_lt.mp ht).1]⟩
  have h₂ : 0 < transMetzlerProfile ((1 - t) / 2 + t) :=
    transMetzlerProfile_pos ⟨by linarith only [(abs_lt.mp ht).1],
      by linarith only [(abs_lt.mp ht).2]⟩
  exact (mul_pos h₁ h₂).ne'

/-- Successor-product fiber in atom-mass normalization. -/
def plateauSuccessorFiber (c : ℝ) (N : ℕ) : ℝ :=
  weightedDownwardDivisorFiber (atomDilate transMetzlerProfile (c / N)) N (N + 1) /
    (∫ u, atomDilate transMetzlerProfile (c / N) u ^ 2)

theorem plateauSuccessorFiber_eq {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    plateauSuccessorFiber c N =
      Real.sqrt ((N : ℝ) / (N + 1 : ℕ)) * Real.log (N + 1 : ℕ) *
        bumpCorr transMetzlerProfile (firstExteriorOverlap N / c) /
          (∫ u, transMetzlerProfile u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  rw [plateauSuccessorFiber,
    weightedDownwardDivisorFiber_eq _ (by omega) (by omega),
    bumpCorr_atomDilate hw, integral_atomDilate_sq hw]
  have hlag : (Real.log (N + 1 : ℕ) - Real.log N) / (c / N) =
      firstExteriorOverlap N / c := by
    unfold firstExteriorOverlap
    field_simp
  rw [hlag]
  field_simp [hc.ne', hN0.ne']
  ring

private theorem nat_succ_real_atTop :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
  exact Eventually.of_forall fun N => by exact_mod_cast Nat.le_succ N

private theorem tendsto_sqrt_nat_div_succ :
    Tendsto (fun N : ℕ => Real.sqrt ((N : ℝ) / (N + 1 : ℕ))) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => 1 - 1 / (N + 1 : ℕ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (show Tendsto (fun N : ℕ => 1 / (N + 1 : ℕ)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop nat_succ_real_atTop)
  have heq : ∀ N : ℕ, 1 - 1 / (N + 1 : ℕ) = (N : ℝ) / (N + 1 : ℕ) := by
    intro N
    have hden : (N + 1 : ℕ) ≠ 0 := by omega
    push_cast
    field_simp
    ring
  have hratio := Filter.Tendsto.congr heq h
  simpa only [Real.sqrt_one] using hratio.sqrt

/-- The exact positive coefficient of logarithmic growth at every fixed overlap above one. -/
theorem tendsto_plateauSuccessorFiber_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => plateauSuccessorFiber c N / Real.log (N + 1 : ℕ)) atTop
      (𝓝 (bumpCorr transMetzlerProfile (1 / c) / (∫ u, transMetzlerProfile u ^ 2))) := by
  have hcorr := (continuous_bumpCorr contDiff_transMetzlerProfile
    hasCompactSupport_transMetzlerProfile).tendsto (1 / c)
  have hlag : Tendsto (fun N : ℕ => firstExteriorOverlap N / c) atTop (𝓝 (1 / c)) :=
    tendsto_firstExteriorOverlap.div_const c
  have h := (tendsto_sqrt_nat_div_succ.mul (hcorr.comp hlag)).div_const
    (∫ u, transMetzlerProfile u ^ 2)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hl : Real.log (N + 1 : ℕ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))).ne'
  rw [plateauSuccessorFiber_eq hc hN]
  dsimp only [Function.comp_def]
  field_simp
  ring

/-- One non-ratio divisor fiber already diverges at every fixed overlap `c>1`. -/
theorem plateauSuccessorFiber_atTop {c : ℝ} (hc : 1 < c) :
    Tendsto (plateauSuccessorFiber c) atTop atTop := by
  have hc0 := zero_lt_one.trans hc
  have hlag : |1 / c| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hc0)]
    exact (div_lt_one hc0).mpr hc
  have hcoef : 0 < bumpCorr transMetzlerProfile (1 / c) /
      (∫ u, transMetzlerProfile u ^ 2) :=
    div_pos (transMetzlerProfile_bumpCorr_pos hlag) integral_transMetzlerProfile_sq_pos
  have h := Filter.Tendsto.pos_mul_atTop hcoef (tendsto_plateauSuccessorFiber_div_log hc0)
    (Real.tendsto_log_atTop.comp nat_succ_real_atTop)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))).ne'

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.weightedDownwardDivisorFiber_eq
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_plateauSuccessorFiber_div_log
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateauSuccessorFiber_atTop
