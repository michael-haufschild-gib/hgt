import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.CoprimeFourierOrder
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasOneEulerConstant

/-!
# Positive Fourier bands for the conductor surplus

The normalized coprime harmonic surplus is nonnegative and has a finite Euler
limit. Abel summation therefore expresses the completed conductor energy above
its rescaled pole as a sum of positive Fourier-band energies; its boundary term
vanishes at infinity.
-/

noncomputable section
open Finset MeasureTheory Filter Topology
open scoped Classical
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HTGeometry CompletedShell SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory

/-- The excess of a coprime harmonic prefix after normalization by its density. -/
def coprimeHarmonicSurplus (m N : ℕ) : ℝ :=
  (m : ℝ) / m.totient *
    (∑ a ∈ (Icc 1 N).filter (fun a => a.Coprime m), (1 : ℝ) / a) - harmonicSum N

theorem coprimeHarmonicSurplus_nonneg {m : ℕ} (hm : 0 < m) (N : ℕ) :
    0 ≤ coprimeHarmonicSurplus m N := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have h := mul_le_mul_of_nonneg_left (totient_div_mul_harmonicSum_le_coprimeSum hm N)
    (div_nonneg hmR.le ht.le)
  have hcancel : (m : ℝ) / m.totient * ((m.totient : ℝ) / m) = 1 := by
    field_simp [hmR.ne', ht.ne']
  rw [← mul_assoc, hcancel, one_mul] at h
  exact sub_nonneg.mpr h

/-- The harmonic excess converges to the sum of the deleted Euler-factor shifts. -/
theorem tendsto_coprimeHarmonicSurplus {m : ℕ} (hm : 0 < m) :
    Tendsto (coprimeHarmonicSurplus m) atTop
      (𝓝 (sieveEuler (conductorPrimeSieve m) - Real.eulerMascheroniConstant)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hcancel : (m : ℝ) / m.totient * ((m.totient : ℝ) / m) = 1 := by
    field_simp [hmR.ne', ht.ne']
  have h := ((tendsto_sievedHarmonic_sub_sieveEuler (conductorPrimeSieve m)).const_mul
    ((m : ℝ) / m.totient)).sub tendsto_harmonicSum_sub_log
  simp only [density_conductorPrimeSieve hm] at h
  convert h using 1
  · funext N
    simp only [coprimeHarmonicSurplus, sievedHarmonic, coprime_conductorPrimeSieve hm]
    rw [mul_sub, ← mul_assoc, hcancel, one_mul]
    ring
  · rw [← mul_assoc, hcancel, one_mul]

private def coprimeHarmonicIncrement (m n : ℕ) : ℝ :=
  (m : ℝ) / m.totient *
    (if m.Coprime (n + 1) then 1 / ((n : ℝ) + 1) else 0) - 1 / ((n : ℝ) + 1)

private theorem partialSum_coprimeHarmonicIncrement (m N : ℕ) :
    _root_.HTGeometry.partialSum (coprimeHarmonicIncrement m) N =
      coprimeHarmonicSurplus m N := by
  simp only [_root_.HTGeometry.partialSum, coprimeHarmonicIncrement,
    coprimeHarmonicSurplus, coprimeHarmonic_eq_range, harmonicSum_eq_range,
    Finset.sum_sub_distrib, Finset.mul_sum]

/-- A Fourier-square band weighted by the nonnegative coprime harmonic excess. -/
def conductorSurplusBand (φ : ℝ → ℝ) (c : ℝ) (m n : ℕ) : ℝ :=
  (2 / (∫ u, φ u ^ 2)) * coprimeHarmonicSurplus m (n + 1) *
    ∫ t in Set.Ioc (((n : ℝ) + 1) * (c / m)) (((n : ℝ) + 2) * (c / m)),
      shellSpectrum φ t

theorem conductorSurplusBand_nonneg (φ : ℝ → ℝ) (c : ℝ) {m : ℕ}
    (hm : 0 < m) (n : ℕ) : 0 ≤ conductorSurplusBand φ c m n := by
  exact mul_nonneg (mul_nonneg (div_nonneg zero_le_two (integral_nonneg fun u => sq_nonneg (φ u)))
    (coprimeHarmonicSurplus_nonneg hm (n + 1)))
    (setIntegral_nonneg measurableSet_Ioc fun t _ => shellSpectrum_nonneg t)

private theorem shellSpectrum_tail_sub_tail {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Set.Ioi a, shellSpectrum φ t) - (∫ t in Set.Ioi b, shellSpectrum φ t) =
      ∫ t in Set.Ioc a b, shellSpectrum φ t := by
  have hint := integrableOn_shellSpectrum_Ioi hφ (hasCompactSupport_profile hsupp) a
  have hsplit : (∫ t in Set.Ioi a, shellSpectrum φ t) =
      (∫ t in Set.Ioc a b, shellSpectrum φ t) + ∫ t in Set.Ioi b, shellSpectrum φ t := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hab)),
      Set.Ioc_union_Ioi_eq_Ioi hab]
  linarith only [hsplit]

/-- Abel summation resolves the conductor surplus into nonnegative Fourier-square bands. -/
theorem hasSum_conductorSurplusBand {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    HasSum (conductorSurplusBand φ c m)
      (completedConductorEnergy φ c m - completedShellEnergy φ (c / m)) := by
  let M := ∫ u, φ u ^ 2
  let x := c / m
  let w : ℕ → ℝ := fun n => (2 / M) *
    ∫ t in Set.Ioi (((n : ℝ) + 1) * x), shellSpectrum φ t
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : 0 < x := div_pos hc hmR
  have hseries : HasSum (fun n => coprimeHarmonicIncrement m n * w n)
      (completedConductorEnergy φ c m - completedShellEnergy φ x) := by
    convert (hasSum_completedConductorEnergy hφ hsupp hM hc hm).sub
      (CompletedShell.hasSum_completedShellEnergy hφ hsupp hM hx) using 1
    all_goals try rfl
    funext n
    dsimp only [coprimeHarmonicIncrement, w, M, x]
    rw [show ((n : ℝ) + 1) * (c / m) = ((n : ℝ) + 1) * c / m by ring]
    split_ifs <;> ring
  have harg : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * x) atTop atTop := by
    have hnat := (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one] using hnat.atTop_mul_const hx
  have hwzero : Tendsto w atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_integral_Ioi_zero (f := shellSpectrum φ) (μ := volume) harg).const_mul (2 / M)
  have hboundary : Tendsto (fun N => coprimeHarmonicSurplus m N * w N) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_coprimeHarmonicSurplus hm).mul hwzero
  have hband (n : ℕ) : coprimeHarmonicSurplus m (n + 1) * (w (n + 1) - w n) =
      -conductorSurplusBand φ c m n := by
    have hab : ((n : ℝ) + 1) * x ≤ ((n : ℝ) + 2) * x :=
      mul_le_mul_of_nonneg_right (by linarith) hx.le
    have hdiff := shellSpectrum_tail_sub_tail hφ hsupp hab
    have hdiff' :
        (∫ t in Set.Ioi (((n : ℝ) + 2) * x), shellSpectrum φ t) -
          (∫ t in Set.Ioi (((n : ℝ) + 1) * x), shellSpectrum φ t) =
        -(∫ t in Set.Ioc (((n : ℝ) + 1) * x) (((n : ℝ) + 2) * x), shellSpectrum φ t) := by
      linarith only [hdiff]
    dsimp only [w, conductorSurplusBand]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
    change coprimeHarmonicSurplus m (n + 1) *
        ((2 / M) * (∫ t in Set.Ioi (((n : ℝ) + 2) * x), shellSpectrum φ t) -
          (2 / M) * (∫ t in Set.Ioi (((n : ℝ) + 1) * x), shellSpectrum φ t)) = _
    rw [← mul_sub, hdiff']
    ring
  have hfinite (N : ℕ) : (∑ n ∈ range N, conductorSurplusBand φ c m n) =
      (∑ n ∈ range N, coprimeHarmonicIncrement m n * w n) -
        coprimeHarmonicSurplus m N * w N := by
    have h := _root_.HTGeometry.sum_mul_weight_eq (coprimeHarmonicIncrement m) w N
    simp only [partialSum_coprimeHarmonicIncrement, hband, Finset.sum_neg_distrib] at h
    linarith only [h]
  apply (hasSum_iff_tendsto_nat_of_nonneg (conductorSurplusBand_nonneg φ c hm) _).mpr
  have hlim := hseries.tendsto_sum_nat.sub hboundary
  simpa only [sub_zero, ← hfinite] using hlim

/-- The excess over the rescaled pole is exactly the positive Fourier-band series. -/
theorem completedConductorEnergy_sub_pole_eq_tsum {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy φ c m - completedShellEnergy φ (c / m) =
      ∑' n, conductorSurplusBand φ c m n :=
  (hasSum_conductorSurplusBand hφ hsupp hM hc hm).tsum_eq.symm

/-- The tilted spline supplies every analytic input to the positive conductor decomposition. -/
theorem tiltedUnitSpline_conductorSurplus_positive_series {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    HasSum (conductorSurplusBand tiltedUnitSpline c m)
        (completedConductorEnergy tiltedUnitSpline c m -
          completedShellEnergy tiltedUnitSpline (c / m)) ∧
      ∀ n, 0 ≤ conductorSurplusBand tiltedUnitSpline c m n :=
  ⟨hasSum_conductorSurplusBand contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hc hm,
    conductorSurplusBand_nonneg tiltedUnitSpline c hm⟩

#print axioms tendsto_coprimeHarmonicSurplus
#print axioms hasSum_conductorSurplusBand
#print axioms tiltedUnitSpline_conductorSurplus_positive_series
end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
