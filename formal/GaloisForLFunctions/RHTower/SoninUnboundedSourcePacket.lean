import GaloisForLFunctions.RHTower.SoninCouplingEnergyLowerBound
import GaloisForLFunctions.RHTower.SoninAperturePacketCurvatureTrace
import GaloisForLFunctions.RHTower.SoninStrictApertureCurvature

/-!
# An unbounded-below source packet

The coupling energy has a uniform floor along the clock, so a unit-weight source packet spread over
enough scales drives the aperture curvature trace below any prescribed level.  The curvature
channel is therefore not merely nonpositive, and not merely nonzero: it is unbounded below over
actual finite source packets with unit weights.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **Unbounded below.**  For every level there is a finite unit-weight source packet whose
aperture curvature trace lies below it. -/
theorem exists_soninAperturePacketCurvature_re_opTrace_lt
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (M : ℝ) :
    ∃ s : Finset ℕ,
      (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
        (one_lt_soninCrossingClock a c) (fun _ => 1))).re < -M := by
  have hcr : ∀ n : ℕ, c < soninCrossingClock a c n * a :=
    fun n => lt_soninCrossingClock_mul a c ha n
  have hfloor := eventually_le_hsNormSq_soninApertureCoupling a b c ha hb hab hbc q haq hqb
    (soninCrossingClock a c) (soninCrossingClock_pos a c) (one_lt_soninCrossingClock a c)
    hcr (tendsto_soninCrossingClock a c)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfloor
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * M)
  refine ⟨Finset.Ico N₀ (N₀ + k), ?_⟩
  have hcard : (Finset.Ico N₀ (N₀ + k)).card = k := by
    rw [Nat.card_Ico]
    omega
  have hre := re_opTrace_soninAperturePacketCurvature (Finset.Ico N₀ (N₀ + k)) ha hab hbc
    (soninCrossingClock a c) (one_lt_soninCrossingClock a c) (fun _ => (1 : ℝ))
    (fun i _ => hcr i)
  rw [hre]
  have hlb : ((k : ℝ) * (4 : ℝ)⁻¹) ≤
      ∑ i ∈ Finset.Ico N₀ (N₀ + k), (1 : ℝ) *
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
          (soninCrossingClock a c i) (one_lt_soninCrossingClock a c i)) := by
    have hterm : ∀ i ∈ Finset.Ico N₀ (N₀ + k), (4 : ℝ)⁻¹ ≤ (1 : ℝ) *
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
          (soninCrossingClock a c i) (one_lt_soninCrossingClock a c i)) := by
      intro i hi
      rw [one_mul]
      exact hN₀ i (Finset.mem_Ico.mp hi).1
    calc ((k : ℝ) * (4 : ℝ)⁻¹)
        = ∑ _i ∈ Finset.Ico N₀ (N₀ + k), (4 : ℝ)⁻¹ := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hM : M < (k : ℝ) * (4 : ℝ)⁻¹ := by linarith
  linarith

end RHTower
