import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicSieveMassIsControlledByItsEulerCorrection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleConductorMinimizesTheCompletedEnergy
import GaloisForLFunctions.HTGeometry.ShiftPartialSummation
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapForcesNewRamanujanTerms

/-!
# Coprime Fourier order at the conductor scale

Harmonic sifting costs at most its Euler density. Abel summation transfers
this order to decreasing Fourier tails, and the density cancels the totient
normalization: `E_m(c) ≥ E_1(c/m)`. Consequently the logarithmic conductor
floor loses only `log c`, with a fixed profile constant. A fixed positive
spectral tail also gives a positive multiple of `log(m/c)` without that constant.
-/

noncomputable section
open Finset MeasureTheory
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry CompletedShell SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory

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

/-- The coprime harmonic prefix retains at least the totient density of the full prefix. -/
theorem totient_div_mul_harmonicSum_le_coprimeSum {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (m.totient : ℝ) / m * harmonicSum N ≤
      ∑ a ∈ (Icc 1 N).filter (fun a => a.Coprime m), (1 : ℝ) / a := by
  have h := sieveDensity_mul_harmonicSum_le (conductorPrimeSieve m) N
  simpa only [density_conductorPrimeSieve hm, sievedHarmonic,
    coprime_conductorPrimeSieve hm] using h


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


private theorem harmonicSum_eq_range (N : ℕ) :
    harmonicSum N = ∑ n ∈ range N, 1 / ((n : ℝ) + 1) := by
  simpa [harmonicSum] using coprimeHarmonic_eq_range 1 N

/-- Harmonic sifting preserves every nonnegative decreasing weight after density normalization. -/
theorem density_mul_weighted_harmonic_le_coprime {m : ℕ} (hm : 0 < m)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w) (N : ℕ) :
    (m.totient : ℝ) / m * (∑ n ∈ range N, 1 / ((n : ℝ) + 1) * w n) ≤
      ∑ n ∈ range N, if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) * w n else 0 := by
  let d : ℕ → ℝ := fun n =>
    (if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) else 0) -
      (m.totient : ℝ) / m * (1 / ((n : ℝ) + 1))
  have hprefix (k : ℕ) : 0 ≤ _root_.HTGeometry.partialSum d k := by
    have h := totient_div_mul_harmonicSum_le_coprimeSum hm k
    rw [coprimeHarmonic_eq_range, harmonicSum_eq_range] at h
    dsimp only [_root_.HTGeometry.partialSum, d]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    exact sub_nonneg.mpr h
  have hweighted : 0 ≤ ∑ n ∈ range N, d n * w n := by
    rw [_root_.HTGeometry.sum_mul_weight_eq]
    have hhead := mul_nonneg (hprefix N) (hw N)
    have htail : (∑ j ∈ range N,
        _root_.HTGeometry.partialSum d (j + 1) * (w (j + 1) - w j)) ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hprefix (j + 1))
        (sub_nonpos.mpr (hanti (Nat.le_succ j)))
    linarith only [hhead, htail]
  have heq : (∑ n ∈ range N, d n * w n) =
      (∑ n ∈ range N, if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) * w n else 0) -
        (m.totient : ℝ) / m * (∑ n ∈ range N, 1 / ((n : ℝ) + 1) * w n) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    dsimp only [d]
    split_ifs <;> ring
  rw [heq] at hweighted
  exact sub_nonneg.mp hweighted

/-- The completed conductor dominates the pole at its natural overlap `c/m`. -/
theorem completedShellEnergy_div_conductor_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    completedShellEnergy φ (c / m) ≤ completedConductorEnergy φ c m := by
  set M := ∫ u, φ u ^ 2
  set T : ℕ → ℝ := fun n => ∫ t in Set.Ioi (((n : ℝ) + 1) * (c / m)), shellSpectrum φ t
  set K := 2 / (M * m.totient) * (m : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hK : 0 ≤ K := mul_nonneg (div_nonneg zero_le_two (mul_nonneg hM.le htot.le)) hmR.le
  have hT (n : ℕ) : 0 ≤ T n :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  have hanti : Antitone T := by
    intro i j hij
    have hijR : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    exact setIntegral_mono_set
      (integrableOn_shellSpectrum_Ioi hφ (hasCompactSupport_profile hsupp) _)
      (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi
        (mul_le_mul_of_nonneg_right hijR (div_nonneg hc.le hmR.le))))
  have hseries : HasSum (fun n : ℕ => K *
      (if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) * T n else 0))
      (completedConductorEnergy φ c m) := by
    convert hasSum_completedConductorEnergy hφ hsupp hM hc hm using 1
    funext n
    dsimp only [K, T]
    split_ifs
    · rw [show ((n : ℝ) + 1) * (c / m) = ((n : ℝ) + 1) * c / m by ring]
      ring
    · ring
  have hcoef : K * ((m.totient : ℝ) / m) = 2 / M := by
    dsimp only [K]
    field_simp [hmR.ne', htot.ne']
  have hpartial (N : ℕ) :
      (∑ n ∈ range N, 2 / M * (((n : ℝ) + 1)⁻¹ * T n)) ≤
        completedConductorEnergy φ c m := by
    have h := mul_le_mul_of_nonneg_left
      (density_mul_weighted_harmonic_le_coprime hm T hT hanti N) hK
    rw [← mul_assoc, hcoef] at h
    calc
      _ = (2 / M) * (∑ n ∈ range N, 1 / ((n : ℝ) + 1) * T n) := by
        rw [Finset.mul_sum]
        simp only [one_div]
      _ ≤ _ := h
      _ = ∑ n ∈ range N, K *
          (if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) * T n else 0) := Finset.mul_sum _ _ _
      _ ≤ _ := sum_le_hasSum _ (fun n _ => mul_nonneg hK (by
        split_ifs
        · exact mul_nonneg (by positivity) (hT n)
        · exact le_rfl)) hseries
  exact le_of_tendsto
    (CompletedShell.hasSum_completedShellEnergy hφ hsupp hM (div_pos hc hmR)).tendsto_sum_nat
    (Filter.Eventually.of_forall hpartial)

/-- The conductor floor loses only one logarithm of overlap, with a fixed profile constant. -/
theorem log_conductor_sub_log_overlap_le_completedEnergy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    Real.log m - Real.log c + min 0 (completeWeilSelfFinitePart φ 1) ≤
      completedConductorEnergy φ c m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hcm : c ≤ (m : ℝ)
  · have hr := div_pos hc hmR
    have hbase : completedShellEnergy φ (c / m) =
        completeWeilSelfFinitePart φ 1 + Real.log m - Real.log c +
          completeWeilPoleShift φ (c / m) := by
      rw [← completedConductorEnergy_one,
        completedConductorEnergy_eq_adjunction hr ((div_le_one hmR).mpr hcm) (by norm_num),
        completeWeilAdjunctionEnergy, completeWeilSelfFinitePart_eq_at_one_sub_log φ hr,
        Real.log_div hc.ne' hmR.ne', if_pos rfl]
      have h1 : ramanujanAdjunctionEnergy 1 = Real.eulerMascheroniConstant := by
        simp [ramanujanAdjunctionEnergy, ArithmeticIntersectionTheory.tameDifferent]
      rw [h1]
      ring
    have horder := completedShellEnergy_div_conductor_le hφ hsupp hM hc hm
    have hpole := completeWeilPoleShift_nonneg φ hr.le
    have hmin := min_le_right (0 : ℝ) (completeWeilSelfFinitePart φ 1)
    linarith only [hbase, horder, hpole, hmin]
  · have hlog := Real.log_le_log hmR (le_of_lt (lt_of_not_ge hcm))
    have hmin := min_le_left (0 : ℝ) (completeWeilSelfFinitePart φ 1)
    have hE := completedConductorEnergy_nonneg hφ hsupp hM hc hm
    linarith only [hlog, hmin, hE]

#print axioms exists_tiltedUnitSpline_uniform_logarithmic_conductor_coercivity
#print axioms density_mul_weighted_harmonic_le_coprime
#print axioms completedShellEnergy_div_conductor_le
#print axioms log_conductor_sub_log_overlap_le_completedEnergy
end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
