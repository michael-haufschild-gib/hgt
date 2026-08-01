import GaloisForLFunctions.RHTower.SoninShellCutBandTotalBound

/-!
# Coupling energy from a bounded band budget and a norm floor

The family hypothesis of the energy bound is the band budget of the *normalized* packets, and the
budget divides by the packet norm.  So a bound on the packets' budgets together with a floor for
their norms supplies that hypothesis, with the ratio as the slack.

Everything else in the energy bound is fixed: the ideal errors' energies, the threshold, and the
shortfall from one.  Only the number of annuli grows.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Energy from a budget bound and a norm floor.**  The slack is the ratio of the two. -/
theorem card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bounds
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c)
    {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r) (hcr : c ≤ r * a) (w : ℝ)
    (hmeanTail : 2 * soninRefTailSup (soninShellCutWidth b c N * |w|) ≤
      ∫ y : ℝ, soninUnitBumpData y)
    (hSq : soninRefSqTailSup (soninShellCutWidth b c N * |w|) ≤
      (∫ y : ℝ, soninUnitBumpSq y) / 20)
    (P L : ℝ) (hL : 0 < L) (hPnn : 0 ≤ P)
    (hP : ∀ i : Fin N, soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
      (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
        (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)) ≤ P)
    (hLnorm : ∀ i : Fin N, L ≤ ‖soninScaledPacketEven (soninShellCutCentre b c N i)
      (soninShellCutWidth b c N) (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖)
    (ε η : ℝ) (hε : 0 < ε) (hη : η ≤ 1) (hcomb : 3 * ε + P / L ≤ η) :
    ((N : ℝ) - ∑ k : Fin 3, hsNormSq (soninCouplingIdealErrors a b r⁻¹
        (inv_pos.mpr (zero_lt_one.trans hr)) k) / ε ^ 2) * (1 - η) ^ 2 ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  have hmean : ∀ i : Fin N, |soninScaledPacketMean (soninShellCutCentre b c N i)
      (soninShellCutWidth b c N) (2 * Real.pi * w)| ≤ 1 := fun i =>
    abs_soninScaledPacketMean_le_one _ _ w (soninShellCutWidth_pos b c hbc hN) hmeanTail
  have hne : ∀ i : Fin N, soninScaledPacketEven (soninShellCutCentre b c N i)
      (soninShellCutWidth b c N) (2 * Real.pi * w)
      (soninShellCutWidth_pos b c hbc hN) ≠ 0 := fun i =>
    soninScaledPacketEven_ne_zero _ _ w (soninShellCutWidth_pos b c hbc hN)
      (soninShellCutWidth_lt_centre b c hb hbc hN i) (hmean i) hSq
  have hband : ∀ i : Fin N, ‖(evenIndicatorCutoff b - evenIndicatorCutoff a)
        (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (soninShellCutUnit b c hbc hN w i))‖ +
      (‖evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
            (soninShellCutUnit b c hbc hN w i) -
          evenFourierCutoff b (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
            (soninShellCutUnit b c hbc hN w i))‖ +
        ‖evenFourierCutoff a (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (soninShellCutUnit b c hbc hN w i))‖) +
      ‖evenFourierCutoff b (soninShellCutUnit b c hbc hN w i)‖ ≤ P / L := by
    intro i
    rw [← soninCouplingBandTotal_eq a b (inv_pos.mpr (zero_lt_one.trans hr))]
    exact soninCouplingBandTotal_soninShellCutUnit_le a b c hbc hN
      (inv_pos.mpr (zero_lt_one.trans hr)) w i (hne i) P L hL (hP i) (hLnorm i) hPnn
  exact card_sub_le_hsNormSq_soninApertureCoupling_shellCut a b c ha hb hab hbc hN hr hcr w
    hmeanTail hSq (P / L) ε η hε hη hcomb hband

end RHTower
