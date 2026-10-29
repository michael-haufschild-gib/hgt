import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPacketPoleCoordinatesSelectConductorOne

/-!
# Actual mass, Markov and Weil limits on finite Ramanujan packets

The exact atomic mass and complete-matrix identities transfer the normalized
packet Gram and mixed energy limits to the synthesized test functions.
Both actual pole moments select conductor one. Subtracting their contribution
from the complete Weil form reverses the sign of its pole correction.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis ArithmeticIntersectionTheory

private theorem atomicTest_extension_profile (a : ℕ → ℝ) (g : ℝ → ℝ) (N : ℕ) :
    atomicTest N (primeHorizonExtension (horizonProfileVector a N)) g = atomicTest N a g := by
  funext u
  unfold atomicTest
  apply sum_congr rfl
  intro n hn
  have h := primeHorizonExtension_coe (horizonProfileVector a N) (⟨n, hn⟩ : PrimeHorizonIndex N)
  change primeHorizonExtension (horizonProfileVector a N) n = a n at h
  rw [h]

/-- The literal test mass has the coefficient Gram limit at every strict width ratio. -/
theorem tendsto_ramanujanPacketTest_mass {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (∫ u, ramanujanPacketTest φ c S b N u ^ 2) /
      ((c / N) * Real.log N)) atTop (𝓝 ((∫ u, φ u ^ 2) * ∑ m ∈ S, b m ^ 2)) := by
  have h := (tendsto_normalizedRamanujanPacketVector_norm_sq S hS b).const_mul (∫ u, φ u ^ 2)
  refine h.congr' ?_
  filter_upwards [eventually_div_horizon_lt_atomSpacing hc0 hc1, eventually_ge_atTop 2]
    with N hsep hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : 0 < c / N := div_pos hc0 hN0
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  rw [ramanujanPacketTest, integral_atomicTest_sq hg hgc hgs hsep.2.2,
    integral_atomDilate_sq hw, normalizedRamanujanPacketVector_norm_sq_eq]
  field_simp [hN0.ne', hc0.ne', hlog.ne']

private theorem packet_weil_ratio_eq_matrix {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (S : Finset ℕ) (b : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    weilQuad (ramanujanPacketTest φ c S b N) / ((c / N) * Real.log N) =
      (∫ u, φ u ^ 2) *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanPacketVector S b N),
          normalizedRamanujanPacketVector S b N⟫ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw : 0 < c / N := div_pos hc0 hN0
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [normalizedRamanujanPacketVector_matrix_inner,
    completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc0 (by omega),
    atomicTest_extension_profile, integral_atomDilate_sq hw, ramanujanPacketTest]
  field_simp [hN0.ne', hc0.ne', hM.ne', hlog.ne']

/-- The actual Weil form has the full arithmetic packet energy, including conductor one. -/
theorem tendsto_ramanujanPacketTest_weil_adjunction {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => weilQuad (ramanujanPacketTest φ c S b N) / ((c / N) * Real.log N))
      atTop (𝓝 ((∫ u, φ u ^ 2) * ∑ m ∈ S, b m ^ 2 * completeWeilAdjunctionEnergy φ c m)) := by
  have h := (tendsto_completeWeilMatrix_packet_inner hφ hsupp hM hc0 hc1 S hS b b).const_mul
    (∫ u, φ u ^ 2)
  have heq : ∀ᶠ N : ℕ in atTop,
      (∫ u, φ u ^ 2) *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanPacketVector S b N),
          normalizedRamanujanPacketVector S b N⟫ =
        weilQuad (ramanujanPacketTest φ c S b N) / ((c / N) * Real.log N) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (packet_weil_ratio_eq_matrix hφ hsupp hM hc0 S b hN).symm
  simpa only [pow_two] using h.congr' heq

private theorem packet_adjunction_sum_eq {φ : ℝ → ℝ} (hM : 0 < ∫ u, φ u ^ 2)
    (c : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ u, φ u ^ 2) * (∑ m ∈ S, b m ^ 2 * completeWeilAdjunctionEnergy φ c m) =
      (∫ u, φ u ^ 2) * (∑ m ∈ S, b m ^ 2 *
        (completeWeilSelfFinitePart φ c + Real.log m + tameDifferent m)) +
          c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2 := by
  classical
  have hground : (∑ m ∈ S, b m ^ 2 * (if m = 1 then completeWeilPoleShift φ c else 0)) =
      completeWeilPoleShift φ c * ramanujanPacketGroundCoefficient S b ^ 2 := by
    simp only [mul_ite, mul_zero, sum_ite_eq', ramanujanPacketGroundCoefficient]
    by_cases h1 : 1 ∈ S
    · rw [if_pos h1, if_pos h1]
      ring
    · rw [if_neg h1, if_neg h1]
      ring
  have hterm (m : ℕ) : b m ^ 2 * completeWeilAdjunctionEnergy φ c m =
      b m ^ 2 * (completeWeilSelfFinitePart φ c + Real.log m + tameDifferent m) +
        b m ^ 2 * (if m = 1 then completeWeilPoleShift φ c else 0) := by
    rw [completeWeilAdjunctionEnergy, ramanujanAdjunctionEnergy]
    ring
  simp only [hterm, sum_add_distrib, hground, mul_add]
  congr 1
  rw [completeWeilPoleShift]
  field_simp [hM.ne']

/-- The literal complete Weil packet limit adds the conductor-one pole correction. -/
theorem tendsto_ramanujanPacketTest_weil {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => weilQuad (ramanujanPacketTest φ c S b N) / ((c / N) * Real.log N))
      atTop (𝓝 ((∫ u, φ u ^ 2) * (∑ m ∈ S, b m ^ 2 *
        (completeWeilSelfFinitePart φ c + Real.log m + tameDifferent m)) +
          c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2)) := by
  rw [← packet_adjunction_sum_eq hM]
  exact tendsto_ramanujanPacketTest_weil_adjunction hφ hsupp hM hc0 hc1 S hS b

/-- The literal Markov packet limit has the opposite conductor-one correction. -/
theorem tendsto_ramanujanPacketTest_markov {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => RHTower.markovEnergy (fun u => (ramanujanPacketTest φ c S b N u : ℂ)) /
      ((c / N) * Real.log N))
      atTop (𝓝 ((∫ u, φ u ^ 2) * (∑ m ∈ S, b m ^ 2 *
        (completeWeilSelfFinitePart φ c + Real.log m + tameDifferent m)) -
          c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2)) := by
  have h := (tendsto_ramanujanPacketTest_weil hφ hsupp hM hc0 hc1 S hS b).sub
    (tendsto_ramanujanPacketTest_two_poles hφ hsupp hM hc0 hc1 S hS b)
  have hvalue : ((∫ u, φ u ^ 2) * (∑ m ∈ S, b m ^ 2 *
      (completeWeilSelfFinitePart φ c + Real.log m + tameDifferent m)) +
        c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2) -
      2 * c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2 =
      (∫ u, φ u ^ 2) * (∑ m ∈ S, b m ^ 2 *
        (completeWeilSelfFinitePart φ c + Real.log m + tameDifferent m)) -
          c * (∫ u, φ u) ^ 2 * ramanujanPacketGroundCoefficient S b ^ 2 := by ring
  rw [hvalue] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hw : 0 < c / N := div_pos hc0 (by exact_mod_cast (show 0 < N by omega))
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  rw [ramanujanPacketTest,
    SelectiveMultiscaleArithmeticPositivity.weilQuad_eq_markov_add_pole
      (contDiff_atomicTest hg N _) (hasCompactSupport_atomicTest hgs N _)]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
