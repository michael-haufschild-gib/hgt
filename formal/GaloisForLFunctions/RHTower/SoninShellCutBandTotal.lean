import GaloisForLFunctions.HTGeometry.NormalizeApply
import GaloisForLFunctions.RHTower.SoninShellCutCouplingEnergy

/-!
# The band budget of a normalized cut packet

The three band terms of the error budget are values of fixed operators — the shell composed with the
dilation, the complement of a band composed with the dilation, and a band itself — so on a
normalized packet each is the packet's own value divided by the packet's norm.

Their total therefore divides by the norm as a whole, which turns the estimates proved for the
packets into the uniform bound the family hypothesis wants, at the cost of one division that the
energy floor bounds from below.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The three band terms of the error budget, as one functional of the vector. -/
def soninCouplingBandTotal (a b : ℝ) {r : ℝ} (hr : 0 < r) (x : evenSubspace) : ℝ :=
  ‖((evenIndicatorCutoff b - evenIndicatorCutoff a) * evenDilationCLM r hr) x‖ +
    (‖((1 - evenFourierCutoff b) * evenDilationCLM r hr) x‖ +
      ‖(evenFourierCutoff a * evenDilationCLM r hr) x‖) +
    ‖evenFourierCutoff b x‖

/-- The normalization law, read on the complex carrier. -/
theorem norm_apply_normalizeC (S : evenSubspace →L[ℂ] evenSubspace) {v : evenSubspace}
    (hv : v ≠ 0) : ‖S (((‖v‖ : ℂ))⁻¹ • v)‖ = ‖S v‖ / ‖v‖ :=
  norm_apply_normalize S hv

/-- The budget's band terms are the functional's value. -/
theorem soninCouplingBandTotal_eq (a b : ℝ) {r : ℝ} (hr : 0 < r) (x : evenSubspace) :
    soninCouplingBandTotal a b hr x =
      ‖(evenIndicatorCutoff b - evenIndicatorCutoff a) (evenDilationCLM r hr x)‖ +
        (‖evenDilationCLM r hr x - evenFourierCutoff b (evenDilationCLM r hr x)‖ +
          ‖evenFourierCutoff a (evenDilationCLM r hr x)‖) +
        ‖evenFourierCutoff b x‖ := by
  have h : ((1 - evenFourierCutoff b) * evenDilationCLM r hr) x =
      evenDilationCLM r hr x - evenFourierCutoff b (evenDilationCLM r hr x) := by
    rw [mul_apply, sub_apply, one_apply]
  rw [soninCouplingBandTotal, h]
  rfl

/-- **The band total divides under normalization.** -/
theorem soninCouplingBandTotal_normalize (a b : ℝ) {r : ℝ} (hr : 0 < r)
    {v : evenSubspace} (hv : v ≠ 0) :
    soninCouplingBandTotal a b hr (((‖v‖ : ℂ))⁻¹ • v) =
      soninCouplingBandTotal a b hr v / ‖v‖ := by
  rw [soninCouplingBandTotal, soninCouplingBandTotal,
    norm_apply_normalizeC _ hv, norm_apply_normalizeC _ hv, norm_apply_normalizeC _ hv,
    norm_apply_normalizeC _ hv]
  ring

/-- **The uniform band bound for the cut's packets.**  A bound on the packets' band totals, divided
by a lower bound for their norms, bounds the normalized family's band totals. -/
theorem soninCouplingBandTotal_soninShellCutUnit_le
    (a b c : ℝ) (hb : 0 < b) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) (w : ℝ)
    (i : Fin N)
    (hne : soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
      (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN) ≠ 0)
    (P L : ℝ) (hL : 0 < L)
    (hP : soninCouplingBandTotal a b hr
      (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
        (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)) ≤ P)
    (hnorm : L ≤ ‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
      (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖)
    (hPnn : 0 ≤ P) :
    soninCouplingBandTotal a b hr (soninShellCutUnit b c hbc hN w i) ≤ P / L := by
  have hpos : (0 : ℝ) < ‖soninScaledPacketEven (soninShellCutCentre b c N i)
      (soninShellCutWidth b c N) (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖ :=
    lt_of_lt_of_le hL hnorm
  rw [soninShellCutUnit, soninCouplingBandTotal_normalize a b hr hne]
  calc soninCouplingBandTotal a b hr
        (soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)) /
        ‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖
      ≤ P / ‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
          (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖ := by gcongr
    _ ≤ P / L := by gcongr

end RHTower
