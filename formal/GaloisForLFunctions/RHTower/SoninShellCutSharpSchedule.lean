import GaloisForLFunctions.RHTower.SoninShellCutSharpBandBound
import GaloisForLFunctions.RHTower.SoninShellCutEnergySchedule

/-!
# The energy bound on the sharp band estimate

Rebuilding the band budget and the energy bound on the estimate that keeps the packet mean gives the
same shape with a different content: every band term now carries a tail at its own gap, so a band
whose radius grows with the scale is controlled by the gap growing with it.

This is the form in which a schedule can be chosen, since no term is bounded below by a constant of
the reference profile alone.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **The band budget on the sharp estimate.** -/
theorem exists_soninCouplingBandTotal_soninShellCutPacket_le_sharp (N₀ : ℕ) (hN₀ : 1 ≤ N₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c q : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r),
      0 < b → a ≤ b → 0 < a → a < q → 2 * q ≤ b → b < r * q →
      2 * soninRefTailSup (soninShellCutWidth b c N * |r * q|) ≤ ∫ y : ℝ, soninUnitBumpData y →
      ∀ i : Fin N,
        soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
            (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
              (2 * Real.pi * (r * q)) (soninShellCutWidth_pos b c hbc hN)) ≤
          Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (r * b)) +
            Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) (r * a)) +
            Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) b) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sq_sub_evenFourierCutoff_soninShellCutPacket_le N₀ hN₀
  refine ⟨K, hK0, ?_⟩
  intro a b c q hbc N hN r hr hb hab ha haq hqb hbrq htail i
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  have hqpos : (0 : ℝ) < q := ha.trans haq
  refine soninCouplingBandTotal_soninShellCutPacket_le_of_sq_bounds a b c hb hab hbc hN hr
    (r * q) i _ _ _ (hK b c q hbc hN hr hqpos hqb htail i) ?_ ?_
  · exact norm_sq_evenFourierCutoff_soninShellCutPacket_le_sharp b c (r * q) hbc hN (r * a)
      (by positivity) (by nlinarith [haq, hrpos]) i
  · exact norm_sq_evenFourierCutoff_soninShellCutPacket_le_sharp b c (r * q) hbc hN b
      hb.le hbrq i

/-- **Coupling energy under an explicit schedule, on the sharp estimate.** -/
theorem exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut_sharp (N₀ : ℕ) (hN₀ : 1 ≤ N₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c q : ℝ) {N : ℕ} {r : ℝ} (hr : 1 < r),
      b < c → 0 < N → 0 < a → a ≤ b → 0 < b → a < q → 2 * q ≤ b → b < r * q → c ≤ r * a →
      2 * soninRefTailSup (soninShellCutWidth b c N * |r * q|) ≤ ∫ y : ℝ, soninUnitBumpData y →
      soninRefSqTailSup (soninShellCutWidth b c N * |r * q|) ≤
        (∫ y : ℝ, soninUnitBumpSq y) / 20 →
      ∀ ε η : ℝ, 0 < ε → η ≤ 1 →
        3 * ε + (Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (r * b)) +
            Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) (r * a)) +
            Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) b)) /
          soninShellCutNormFloor b c N ≤ η →
        ((N : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r⁻¹
            (inv_pos.mpr (zero_lt_one.trans hr)) k) / ε ^ (2 : ℕ)) * (1 - η) ^ (2 : ℕ) ≤
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  obtain ⟨K, hK0, hK⟩ := exists_soninCouplingBandTotal_soninShellCutPacket_le_sharp N₀ hN₀
  refine ⟨K, hK0, ?_⟩
  intro a b c q N r hr hbc hN ha hab hb haq hqb hbrq hcr htail hSq ε η hε hη hcomb
  have hPnn : (0 : ℝ) ≤ Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (r * b)) +
      Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) (r * a)) +
      Real.sqrt (soninShellCutSharpBandBoundAt b c N (r * q) b) := by positivity
  exact card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bandBound a b c ha hb hab hbc
    hN hr hcr (r * q) htail hSq _ hPnn
    (fun i => hK a b c q hbc hN hr hb hab ha haq hqb hbrq htail i) ε η hε hη hcomb

end RHTower
