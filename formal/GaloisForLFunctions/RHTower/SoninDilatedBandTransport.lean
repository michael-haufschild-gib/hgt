import GaloisForLFunctions.RHTower.SoninShellCutBandTotal
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.SoninFourierCutoffDilation

/-!
# Reading the dilate's band terms on the packet

Dilation conjugates a cutoff into a cutoff at a rescaled radius and preserves norms.  For the
frequency side this is already recorded; here it is the physical side, which moves the other way: an
inverse dilate is annihilated by every physical cutoff below `r` times its inner radius, so for a
packet of a shell cut both aperture radii annihilate it at once.

The dilate therefore contributes nothing new to the error budget: its two band terms are the
packet's band content at radius `r a` and the packet's spectral mass above radius `r b`, and its
physical term vanishes outright.  The packet's own norm floor, needed to divide the budget, comes
from the energy floor by taking square roots.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- A physical cutoff below `r` times the inner radius annihilates the inverse dilate. -/
theorem evenIndicatorCutoff_evenDilationCLM_inv_soninScaledPacketEven_eq_zero
    (m δ κ : ℝ) (hδ : 0 < δ) (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : s ≤ r * (m - δ)) :
    evenIndicatorCutoff s
        (evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninScaledPacketEven m δ κ hδ)) = 0 := by
  have hcov := DFunLike.congr_fun
    (evenIndicatorCutoff_mul_evenDilationCLM s r⁻¹ (inv_pos.mpr hr))
    (soninScaledPacketEven m δ κ hδ)
  rw [mul_apply_eq_comp, mul_apply_eq_comp] at hcov
  rw [hcov, evenIndicatorCutoff_soninScaledPacketEven_eq_zero m δ κ hδ (r⁻¹ * s) ?_, map_zero]
  rw [inv_mul_le_iff₀ hr]
  linarith [hs]

/-- **The dilate's physical term vanishes for a cut packet.**  Both aperture radii sit below `r`
times the annulus's inner radius, since the cut starts at `b` and the scale exceeds one. -/
theorem evenIndicatorCutoff_sub_evenDilationCLM_inv_soninShellCutUnit_eq_zero
    (a b c : ℝ) (hb : 0 < b) (hab : a ≤ b) (hbc : b < c) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 1 < r)
    (w : ℝ) (i : Fin N) :
    (evenIndicatorCutoff b - evenIndicatorCutoff a)
        (evenDilationCLM r⁻¹ (inv_pos.mpr (zero_lt_one.trans hr))
          (soninShellCutUnit b c hbc hN w i)) = 0 := by
  have hrpos : (0 : ℝ) < r := zero_lt_one.trans hr
  have hcut : b ≤ soninShellCutCentre b c N i - soninShellCutWidth b c N :=
    (soninShellCut_le b c hbc hN i).1
  have hinner : (0 : ℝ) ≤ soninShellCutCentre b c N i - soninShellCutWidth b c N :=
    le_trans hb.le hcut
  have hkey : ∀ s : ℝ, s ≤ b → evenIndicatorCutoff s
      (evenDilationCLM r⁻¹ (inv_pos.mpr hrpos) (soninShellCutUnit b c hbc hN w i)) = 0 := by
    intro s hs
    rw [soninShellCutUnit, map_smul, map_smul,
      evenIndicatorCutoff_evenDilationCLM_inv_soninScaledPacketEven_eq_zero _ _
        (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN) r hrpos s ?_, smul_zero]
    · nlinarith [hs, hcut, hinner, hr]
  rw [sub_apply, hkey b le_rfl, hkey a hab, sub_zero]

/-- **The norm floor for a cut packet.** -/
theorem sqrt_le_norm_soninShellCutPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) {N : ℕ}
    (hN : 0 < N) (w : ℝ) (i : Fin N)
    (hmean : |soninScaledPacketMean (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
      (2 * Real.pi * w)| ≤ 1)
    (hSq : soninRefSqTailSup (soninShellCutWidth b c N * |w|) ≤
      (∫ y : ℝ, soninUnitBumpSq y) / 20) :
    Real.sqrt (soninShellCutWidth b c N * (∫ y : ℝ, soninUnitBumpSq y) / 2) ≤
      ‖soninScaledPacketEven (soninShellCutCentre b c N i) (soninShellCutWidth b c N)
        (2 * Real.pi * w) (soninShellCutWidth_pos b c hbc hN)‖ := by
  have hfloor := norm_sq_soninScaledPacketEven_ge_half (soninShellCutCentre b c N i)
    (soninShellCutWidth b c N) w (soninShellCutWidth_pos b c hbc hN)
    (soninShellCutWidth_lt_centre b c hb hbc hN i) hmean hSq
  have hsq := Real.sqrt_le_sqrt hfloor
  rwa [Real.sqrt_sq (norm_nonneg _)] at hsq

end RHTower
