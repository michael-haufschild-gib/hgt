import GaloisForLFunctions.RHTower.SoninCouplingEnergyFromFamily
import GaloisForLFunctions.RHTower.SoninShellCut

/-!
# Coupling energy from a cut shell

Normalizing the packets of a shell cut changes nothing the coupling estimate sees: a scalar multiple
still vanishes inside the inner aperture and is still fixed by the outer one, because the cutoffs are
linear.  So the cut's `N` packets are admissible as a family, and the energy bound reads with `N` in
place of the family's cardinality.

The number of annuli is now the only quantity on the right that grows.  Everything subtracted from
it — the ideal errors' energies, the threshold, the shortfall — is fixed once the schedule's
constants are chosen.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The normalized packet of the `i`-th piece of a shell cut. -/
def soninShellCutUnit (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) (w : ℝ) (i : Fin N) :
    evenSubspace :=
  ((‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
        (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖ : ℂ))⁻¹ •
    soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
      (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)

theorem orthonormal_soninShellCutUnit (b c : ℝ) (hb : 0 < b) (hbc : b < c) {N : ℕ} (hN : 0 < N)
    (w : ℝ)
    (hmean : 2 * soninRefTailSup (soninShellCutWidth b c N * |w|) ≤
      ∫ y : ℝ, soninUnitBumpData y)
    (hSq : soninRefSqTailSup (soninShellCutWidth b c N * |w|) ≤
      (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    Orthonormal ℂ (soninShellCutUnit b c hbc hN w) :=
  orthonormal_soninShellCutPacket b c hb hbc hN w hmean hSq

/-- The normalized packet still vanishes under the inner cutoff. -/
theorem evenIndicatorCutoff_soninShellCutUnit_eq_zero (b c : ℝ) (hbc : b < c) {N : ℕ}
    (hN : 0 < N) (w : ℝ) (i : Fin N) :
    evenIndicatorCutoff b (soninShellCutUnit b c hbc hN w i) = 0 := by
  rw [soninShellCutUnit, map_smul,
    evenIndicatorCutoff_soninScaledPacketEven_eq_zero _ _ (2 * Real.pi * w)
      (soninShellCutWidth_pos b c hbc hN) b (soninShellCut_le b c hbc hN i).1,
    smul_zero]

/-- The normalized packet is still fixed by the outer cutoff. -/
theorem evenIndicatorCutoff_soninShellCutUnit_eq_self (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    {N : ℕ} (hN : 0 < N) (w : ℝ) (i : Fin N) :
    evenIndicatorCutoff c (soninShellCutUnit b c hbc hN w i) = soninShellCutUnit b c hbc hN w i := by
  rw [soninShellCutUnit, map_smul,
    evenIndicatorCutoff_soninScaledPacketEven_eq_self _ _ (2 * Real.pi * w)
      (soninShellCutWidth_pos b c hbc hN) (soninShellCutCentre_nonneg b c hb hbc hN i) c
      (soninShellCut_le b c hbc hN i).2]

/-- **Coupling energy from a cut shell.**  With the cut's packets as the family, the energy bound
reads with the number of annuli in place of the family's cardinality. -/
theorem card_sub_le_hsNormSq_soninApertureCoupling_shellCut
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c)
    {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a) (w : ℝ)
    (hmean : 2 * soninRefTailSup (soninShellCutWidth b c N * |w|) ≤
      ∫ y : ℝ, soninUnitBumpData y)
    (hSq : soninRefSqTailSup (soninShellCutWidth b c N * |w|) ≤
      (∫ y : ℝ, soninUnitBumpSq y) / 20)
    (β ε η : ℝ) (hε : 0 < ε) (hη : η ≤ 1) (hcomb : 3 * ε + β ≤ η)
    (hband : ∀ i : Fin N, ‖(evenIndicatorCutoff b - evenIndicatorCutoff a)
          (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
            (soninShellCutUnit b c hbc hN w i))‖ +
        (‖evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
              (soninShellCutUnit b c hbc hN w i) -
            evenFourierCutoff b (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
              (soninShellCutUnit b c hbc hN w i))‖ +
          ‖evenFourierCutoff a (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
            (soninShellCutUnit b c hbc hN w i))‖) +
        ‖evenFourierCutoff b (soninShellCutUnit b c hbc hN w i)‖ ≤ β) :
    ((N : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r⁻¹
        (inv_pos.mpr (zero_lt_one.trans hr)) k) / ε ^ (2 : ℕ)) * (1 - η) ^ (2 : ℕ) ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  have hc : 0 < c := hb.trans hbc
  have hmain := card_sub_le_hsNormSq_soninApertureCoupling ha hb hc hab hbc.le hr hcr
    (orthonormal_soninShellCutUnit b c hb hbc hN w hmean hSq)
    (fun i => evenIndicatorCutoff_soninShellCutUnit_eq_zero b c hbc hN w i)
    (fun i => evenIndicatorCutoff_soninShellCutUnit_eq_self b c hb hbc hN w i)
    β ε η hε hη hcomb hband
  simpa using hmain

end RHTower
