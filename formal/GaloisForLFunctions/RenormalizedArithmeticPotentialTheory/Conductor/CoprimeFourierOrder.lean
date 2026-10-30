import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicSieveMassIsControlledByItsEulerCorrection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleConductorMinimizesTheCompletedEnergy

/-!
# Coprime Fourier order at the conductor scale

Harmonic sifting costs at most its Euler density. In the completed Fourier
series this density cancels the totient normalization, giving a logarithmic
conductor floor uniform in overlap. Abel summation also compares the complete
energy with the pole energy at overlap divided by the conductor.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry

private def conductorPrimeSieve (m : ℕ) : Finset Nat.Primes :=
  Finset.subtype Nat.Prime m.primeFactors

private theorem coprime_conductorPrimeSieve {m : ℕ} (hm : 0 < m) (a : ℕ) :
    a.Coprime (sievePrimorial (conductorPrimeSieve m)) ↔ a.Coprime m := by
  rw [sievePrimorial, Nat.coprime_prod_right_iff]
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpa hpm
    have hpQ : (⟨p, hp⟩ : Nat.Primes) ∈ conductorPrimeSieve m := by
      exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩)
    exact (hp.coprime_iff_not_dvd.mp (h ⟨p, hp⟩ hpQ).symm) hpa
  · intro h p hp
    exact h.of_dvd_right (Nat.mem_primeFactors.mp (Finset.mem_subtype.mp hp)).2.1

private theorem density_conductorPrimeSieve {m : ℕ} (hm : 0 < m) :
    sieveDensity (conductorPrimeSieve m) = (m.totient : ℝ) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors m)
  push_cast at h
  dsimp only [sieveDensity, conductorPrimeSieve]
  change (∏ p ∈ Finset.subtype Nat.Prime m.primeFactors, (1 - (p.val : ℝ)⁻¹)) = _
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => 1 - (p : ℝ)⁻¹)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  apply (eq_div_iff hm0).mpr
  simpa only [mul_comm] using h.symm

theorem totient_div_mul_harmonicSum_le_coprimeSum {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (m.totient : ℝ) / m * harmonicSum N ≤
      ∑ a ∈ (Icc 1 N).filter (fun a => a.Coprime m), (1 : ℝ) / a := by
  have h := sieveDensity_mul_harmonicSum_le (conductorPrimeSieve m) N
  simpa only [density_conductorPrimeSieve hm, sievedHarmonic,
    coprime_conductorPrimeSieve hm] using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open MeasureTheory Set
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry CompletedShell SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory

private theorem coprimeHarmonic_eq_range (m N : ℕ) :
    (∑ a ∈ (Finset.Icc 1 N).filter (fun a => a.Coprime m), (1 : ℝ) / a) =
      ∑ n ∈ range N, if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) else 0 := by
  rw [Finset.sum_filter]
  symm
  apply sum_bij (fun n _ => n + 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨by omega, by have := mem_range.mp hn; omega⟩
  · intro a _ b _ hab
    omega
  · intro a ha
    have ha' := Finset.mem_Icc.mp ha
    exact ⟨a - 1, mem_range.mpr (by omega), by omega⟩
  · intro n _
    simp only [Nat.cast_add, Nat.cast_one, Nat.coprime_comm]

/-- A coprime prefix retains the full unsifted harmonic mass after totient normalization. -/
theorem shellTail_mul_harmonicSum_le_completedConductorEnergy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) (N : ℕ) (hNc : (N : ℝ) * c ≤ m) :
    (2 / (∫ u, φ u ^ 2)) * (∫ t in Set.Ioi 1, shellSpectrum φ t) * harmonicSum N ≤
      completedConductorEnergy φ c m := by
  set M := ∫ u, φ u ^ 2
  set J := ∫ t in Set.Ioi 1, shellSpectrum φ t
  set B := 2 / (M * m.totient) * (m : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hJ : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  have hB : 0 ≤ B := mul_nonneg (div_nonneg zero_le_two (mul_nonneg hM.le htot.le)) hmR.le
  have htail (n : ℕ) (hn : n ∈ range N) :
      J ≤ ∫ t in Set.Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t := by
    have hnN : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
    have harg : ((n : ℝ) + 1) * c / m ≤ 1 := by
      apply (div_le_one hmR).mpr
      exact (mul_le_mul_of_nonneg_right hnN hc.le).trans hNc
    exact setIntegral_mono_set
      (integrableOn_shellSpectrum_Ioi hφ (hasCompactSupport_profile hsupp) _)
      (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi harg))
  have hsum := hasSum_completedConductorEnergy hφ hsupp hM hc hm
  have hnonneg (n : ℕ) : 0 ≤ (if m.Coprime (n + 1) then
      2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
        ∫ t in Set.Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg
        (div_nonneg zero_le_two (mul_nonneg hM.le htot.le))
        (div_nonneg hmR.le (by positivity)))
        (setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t)
    · exact le_rfl
  have hprefix : B * J *
      (∑ a ∈ (Finset.Icc 1 N).filter (fun a => a.Coprime m), (1 : ℝ) / a) ≤
      completedConductorEnergy φ c m := by
    rw [coprimeHarmonic_eq_range, Finset.mul_sum]
    calc
      _ ≤ ∑ n ∈ range N, if m.Coprime (n + 1) then
          2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
            ∫ t in Set.Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0 := by
        apply sum_le_sum
        intro n hn
        split_ifs
        · calc
            _ = (2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1))) * J := by
              dsimp only [B]
              ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (htail n hn)
              (mul_nonneg (div_nonneg zero_le_two (mul_nonneg hM.le htot.le))
                (div_nonneg hmR.le (by positivity)))
        · simp only [mul_zero, le_refl]
      _ ≤ _ := sum_le_hasSum _ (fun n _ => hnonneg n) hsum
  have hdensity := mul_le_mul_of_nonneg_left
    (totient_div_mul_harmonicSum_le_coprimeSum hm N) (mul_nonneg hB hJ)
  have hcancel : B * J * ((m.totient : ℝ) / m * harmonicSum N) =
      (2 / M) * J * harmonicSum N := by
    dsimp only [B]
    field_simp [hmR.ne', htot.ne']
  rw [hcancel] at hdensity
  exact hdensity.trans hprefix

/-- A fixed Fourier tail gives a logarithmic conductor floor with logarithmic overlap loss. -/
theorem shellTail_mul_log_le_completedConductorEnergy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    (2 / (∫ u, φ u ^ 2)) * (∫ t in Set.Ioi 1, shellSpectrum φ t) *
        (Real.log m - Real.log c) ≤ completedConductorEnergy φ c m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfloor : (⌊(m : ℝ) / c⌋₊ : ℝ) * c ≤ m :=
    (le_div_iff₀ hc).mp (Nat.floor_le (div_nonneg hmR.le hc.le))
  have hlog : Real.log m - Real.log c ≤ harmonicSum ⌊(m : ℝ) / c⌋₊ := by
    have h := log_le_harmonic_floor ((m : ℝ) / c) (div_nonneg hmR.le hc.le)
    rw [Real.log_div hmR.ne' hc.ne'] at h
    simpa only [← sum_Icc_one_div_eq_harmonic, harmonicSum] using h
  have hcoef : 0 ≤ (2 / (∫ u, φ u ^ 2)) * (∫ t in Set.Ioi 1, shellSpectrum φ t) :=
    mul_nonneg (div_nonneg zero_le_two hM.le)
      (setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t)
  exact (mul_le_mul_of_nonneg_left hlog hcoef).trans
    (shellTail_mul_harmonicSum_le_completedConductorEnergy hφ hsupp hM hc hm _ hfloor)

/-- The tilted spline controls logarithmic degree uniformly over all overlaps and conductors. -/
theorem exists_tiltedUnitSpline_uniform_logarithmic_conductor_coercivity :
    ∃ a : ℝ, 0 < a ∧ ∀ (c : ℝ) (m : ℕ), 0 < c → 0 < m →
      a * (Real.log m - Real.log c) ≤ completedConductorEnergy tiltedUnitSpline c m := by
  refine ⟨(2 / (∫ u, tiltedUnitSpline u ^ 2)) *
      (∫ t in Set.Ioi 1, shellSpectrum tiltedUnitSpline t), ?_, ?_⟩
  · exact mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
      (integral_shellSpectrum_tiltedUnitSpline_pos 1)
  · intro c m hc hm
    exact shellTail_mul_log_le_completedConductorEnergy contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm

#print axioms exists_tiltedUnitSpline_uniform_logarithmic_conductor_coercivity
end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
