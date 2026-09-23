import GaloisForLFunctions.RHTower.SoninShellCutEnergyFromBounds

/-!
# Coupling energy with the norm floor named

The floor for the packets' norms is the square root of half the half-width times the reference
square's mass, so it need not be carried as a parameter: the energy bound can be stated with the
band budget as its only quantitative input, and the slack read as that budget over the explicit
floor.

The floor is positive whenever the shell is nondegenerate, so the statement carries no side
condition beyond the ones the cut already needs.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The explicit norm floor of a shell cut's packets. -/
def soninShellCutNormFloor (b c : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (soninShellCutWidth b c N * (∫ y : ℝ, soninUnitBumpSq y) / 2)

theorem soninShellCutNormFloor_pos (b c : ℝ) (hbc : b < c) {N : ℕ} (hN : 0 < N) :
    0 < soninShellCutNormFloor b c N := by
  have hδ := soninShellCutWidth_pos b c hbc hN
  have hI : 0 < ∫ y : ℝ, soninUnitBumpSq y := integral_soninUnitBumpSq_pos
  rw [soninShellCutNormFloor]
  exact Real.sqrt_pos.mpr (by positivity)

/-- **Energy from a band bound alone.**  The norm floor is supplied by the cut. -/
theorem card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bandBound
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c)
    {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a) (w : ℝ)
    (hmeanTail : 2 * soninRefTailSup (soninShellCutWidth b c N * |w|) ≤
      ∫ y : ℝ, soninUnitBumpData y)
    (hSq : soninRefSqTailSup (soninShellCutWidth b c N * |w|) ≤
      (∫ y : ℝ, soninUnitBumpSq y) / 20)
    (P : ℝ) (hPnn : 0 ≤ P)
    (hP : ∀ i : Fin N, soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
      (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
        (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)) ≤ P)
    (ε η : ℝ) (hε : 0 < ε) (hη : η ≤ 1)
    (hcomb : 3 * ε + P / soninShellCutNormFloor b c N ≤ η) :
    ((N : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r⁻¹
        (inv_pos.mpr (zero_lt_one.trans hr)) k) / ε ^ (2 : ℕ)) * (1 - η) ^ (2 : ℕ) ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  have hmean : ∀ i : Fin N, |soninScaledPacketMean (soninShellCutCentre b c N i)
      (soninShellCutWidth b c N) (2 * Real.pi * w)| ≤ 1 := fun i =>
    abs_soninScaledPacketMean_le_one _ _ w (soninShellCutWidth_pos b c hbc hN) hmeanTail
  refine card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bounds a b c ha hb hab hbc hN hr
    hcr w hmeanTail hSq P (soninShellCutNormFloor b c N)
    (soninShellCutNormFloor_pos b c hbc hN) hPnn hP ?_ ε η hε hη hcomb
  intro i
  exact sqrt_le_norm_soninShellCutPacket b c hb hbc hN w i (hmean i) hSq

end RHTower
