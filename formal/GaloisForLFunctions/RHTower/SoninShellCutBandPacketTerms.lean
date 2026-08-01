import GaloisForLFunctions.RHTower.SoninDilatedBandTransport

/-!
# The band budget of a cut packet in its own terms

Transporting the dilate's two band terms back through the dilation, and discarding the physical term
that vanishes, leaves the band budget of a cut packet as three quantities of the packet alone: the
mass it keeps above the band of radius `r b`, its content in the band of radius `r a`, and its
content in the band of radius `b`.

All three are band quantities of one vector at three radii, so the estimates already proved apply to
each without further transport.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The band total with the dilate's terms read on the vector itself. -/
theorem soninCouplingBandTotal_eq_packetTerms (a b : ℝ) {r : ℝ} (hr : 0 < r) (x : evenSubspace) :
    soninCouplingBandTotal a b (inv_pos.mpr hr) x =
      ‖(evenIndicatorCutoff b - evenIndicatorCutoff a)
          (evenDilationCLM r⁻¹ (inv_pos.mpr hr) x)‖ +
        (‖x - evenFourierCutoff (r * b) x‖ + ‖evenFourierCutoff (r * a) x‖) +
        ‖evenFourierCutoff b x‖ := by
  rw [soninCouplingBandTotal_eq, norm_sub_evenFourierCutoff_evenDilationCLM_inv b r hr,
    norm_evenFourierCutoff_evenDilationCLM_inv a r hr]

/-- The physical term vanishes on a cut packet. -/
theorem evenIndicatorCutoff_sub_evenDilationCLM_inv_soninShellCutPacket_eq_zero
    (a b c : ℝ) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r)
    (w : ℝ) (i : Fin N) :
    (evenIndicatorCutoff b - evenIndicatorCutoff a)
        (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
            (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))) = 0 := by
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  have hcut : b ≤ soninShellCutCentre b c N i - soninShellCutWidth b c N :=
    (soninShellCut_le b c hbc hN i).1
  have hinner : (0 : ℝ) ≤ soninShellCutCentre b c N i - soninShellCutWidth b c N :=
    le_trans hb.le hcut
  have hkey : ∀ s : ℝ, s ≤ b → evenIndicatorCutoff s
      (evenDilationCLM r⁻¹ (inv_pos.mpr hrpos)
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))) = 0 := by
    intro s hs
    refine evenIndicatorCutoff_evenDilationCLM_inv_soninScaledPacketEven_eq_zero _ _
      (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN) r hrpos s ?_
    nlinarith [hs, hcut, hinner, hr]
  rw [sub_apply, hkey b le_rfl, hkey a hab, sub_zero]

/-- **The cut packet's band budget in three radii.**  The mass above `r b`, the content in the band
of radius `r a`, and the content in the band of radius `b`. -/
theorem soninCouplingBandTotal_soninShellCutPacket_eq
    (a b c : ℝ) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r)
    (w : ℝ) (i : Fin N) :
    soninCouplingBandTotal a b (inv_pos.mpr (zero_lt_one.trans hr))
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)) =
      (‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
            (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN) -
          evenFourierCutoff (r * b)
            (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
              (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ +
        ‖evenFourierCutoff (r * a)
          (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
            (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖) +
      ‖evenFourierCutoff b
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN))‖ := by
  rw [soninCouplingBandTotal_eq_packetTerms a b (zero_lt_one.trans hr),
    evenIndicatorCutoff_sub_evenDilationCLM_inv_soninShellCutPacket_eq_zero a b c hb hab hbc
      hN hr w i, norm_zero, zero_add]

end RHTower
