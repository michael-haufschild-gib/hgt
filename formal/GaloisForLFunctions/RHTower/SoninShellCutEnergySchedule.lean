import GaloisForLFunctions.RHTower.SoninShellCutUniformBandBound

/-!
# Coupling energy of a cut shell, with every input explicit

Combining the annulus-free band budget with the named norm floor leaves an energy bound whose only
inputs are the schedule: the shell, the number of annuli, the scale, the carrier ratio, the decay
order, the mode threshold and the shortfall.

The number of annuli is the only quantity on the left that grows.  Everything subtracted from it —
the three ideal errors' energies over the squared threshold — is a constant of the aperture, and the
factor `(1 - η)²` is a constant of the schedule.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Coupling energy under an explicit schedule.**  The band budget is the sum of three roots and
the floor is the cut's own, so the slack is a quantity of the schedule alone. -/
theorem exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut (N₀ : ℕ) (hN₀ : 1 ≤ N₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a b c q : ℝ) {N : ℕ} {r : ℝ} (hr : 1 < r),
      b < c → 0 < N → 0 < a → a ≤ b → 0 < b → a < q → 2 * q ≤ b → b < r * q → c ≤ r * a →
      2 * soninRefTailSup (soninShellCutWidth b c N * |r * q|) ≤ ∫ y : ℝ, soninUnitBumpData y →
      soninRefSqTailSup (soninShellCutWidth b c N * |r * q|) ≤
        (∫ y : ℝ, soninUnitBumpSq y) / 20 →
      ∀ ε η : ℝ, 0 < ε → η ≤ 1 →
        3 * ε + (Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (r * b)) +
            Real.sqrt (soninShellCutBandBoundAt b c N (r * q) (r * a)) +
            Real.sqrt (soninShellCutBandBoundAt b c N (r * q) b)) /
          soninShellCutNormFloor b c N ≤ η →
        ((N : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r⁻¹
            (inv_pos.mpr (zero_lt_one.trans hr)) k) / ε ^ 2) * (1 - η) ^ 2 ≤
          hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  obtain ⟨K, hK0, hK⟩ := exists_soninCouplingBandTotal_soninShellCutPacket_le_uniform N₀ hN₀
  refine ⟨K, hK0, ?_⟩
  intro a b c q N r hr hbc hN ha hab hb haq hqb hbrq hcr htail hSq ε η hε hη hcomb
  have hPnn : (0 : ℝ) ≤ Real.sqrt (soninShellCutHighBoundAt b c N K N₀ (r * b)) +
      Real.sqrt (soninShellCutBandBoundAt b c N (r * q) (r * a)) +
      Real.sqrt (soninShellCutBandBoundAt b c N (r * q) b) := by positivity
  exact card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bandBound a b c ha hb hab hbc
    hN hr hcr (r * q) htail hSq _ hPnn
    (fun i => hK a b c q hbc hN hr hb hab ha haq hqb hbrq htail i) ε η hε hη hcomb

end RHTower
