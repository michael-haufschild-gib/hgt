import GaloisForLFunctions.RHTower.SoninShellCutBandPacketTerms

/-!
# From squared band estimates to the band budget

The budget is a sum of norms while the spectral estimates bound squares, so each estimate enters
through its square root.  With the physical term gone, three squared bounds — one above the outer
radius, two inside bands — give the budget as the sum of their roots.

Nothing here is specific to the packets: any vector whose dilate the physical shell annihilates, and
whose three band energies are bounded, has this budget.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- A squared bound gives a bound by the square root. -/
theorem norm_le_sqrt_of_sq_le {x X : ℝ} (hx : 0 ≤ x) (h : x ^ (2 : ℕ) ≤ X) : x ≤ Real.sqrt X := by
  rw [show x = Real.sqrt (x ^ (2 : ℕ)) from (Real.sqrt_sq hx).symm]
  exact Real.sqrt_le_sqrt h

/-- **The band budget from three squared estimates.** -/
theorem soninCouplingBandTotal_le_of_sq_bounds
    (a b : ℝ) {r : ℝ} (hr : 0 < r) (x : evenSubspace) (Bhigh Bra Bb : ℝ)
    (hphys : (evenIndicatorCutoff b - evenIndicatorCutoff a)
      (evenDilationCLM r⁻¹ (inv_pos.mpr hr) x) = 0)
    (h1 : ‖x - evenFourierCutoff (r * b) x‖ ^ (2 : ℕ) ≤ Bhigh)
    (h2 : ‖evenFourierCutoff (r * a) x‖ ^ (2 : ℕ) ≤ Bra)
    (h3 : ‖evenFourierCutoff b x‖ ^ (2 : ℕ) ≤ Bb) :
    soninCouplingBandTotal a b (inv_pos.mpr hr) x ≤
      Real.sqrt Bhigh + Real.sqrt Bra + Real.sqrt Bb := by
  rw [soninCouplingBandTotal_eq_packetTerms a b hr x, hphys, norm_zero, zero_add]
  have k1 : ‖x - evenFourierCutoff (r * b) x‖ ≤ Real.sqrt Bhigh :=
    norm_le_sqrt_of_sq_le (norm_nonneg _) h1
  have k2 : ‖evenFourierCutoff (r * a) x‖ ≤ Real.sqrt Bra :=
    norm_le_sqrt_of_sq_le (norm_nonneg _) h2
  have k3 : ‖evenFourierCutoff b x‖ ≤ Real.sqrt Bb :=
    norm_le_sqrt_of_sq_le (norm_nonneg _) h3
  linarith

/-- **The band budget of a cut packet from three squared estimates.**  The physical term is supplied
by the cut's geometry, so only the three spectral bounds are needed. -/
theorem soninCouplingBandTotal_soninShellCutPacket_le_of_sq_bounds
    (a b c : ℝ) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r)
    (w : ℝ) (i : Fin N) (Bhigh Bra Bb : ℝ)
    (h1 : ‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN) -
        evenFourierCutoff (r * b)
          (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
            (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ ^ (2 : ℕ) ≤ Bhigh)
    (h2 : ‖evenFourierCutoff (r * a)
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ ^ (2 : ℕ) ≤ Bra)
    (h3 : ‖evenFourierCutoff b
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ ^ (2 : ℕ) ≤ Bb) :
    soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)) ≤
      Real.sqrt Bhigh + Real.sqrt Bra + Real.sqrt Bb :=
  soninCouplingBandTotal_le_of_sq_bounds a b (zero_lt_one.trans hr) _ Bhigh Bra Bb
    (evenIndicatorCutoff_sub_evenDilationCLM_inv_soninShellCutPacket_eq_zero a b c hb hab hbc
      hN hr w i) h1 h2 h3

end RHTower
