import GaloisForLFunctions.RHTower.SoninPacketBandGapLimits
import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation

/-!
# The packet keeps its energy between a slow and a fast band

The wavepacket loses all its frequency mass below any band the carrier outruns, and keeps all of it
below any band that outruns the carrier.  So between one slow radius and one fast radius the packet
holds essentially its whole energy, which stays bounded away from zero.

This is the mass a frequency-side step multiplier reads: it is not eroded as the carrier runs.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology

/-- **Band-gap energy floor.**  Between a band the carrier outruns and a band that outruns the
carrier, the packet's frequency mass stays above a fixed positive level. -/
theorem exists_pos_eventually_le_fourier_band_gap
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℝ) (A t T : ℕ → ℝ)
    (hA : Tendsto (fun i => 2 * Real.pi * A i) atTop atTop)
    (hAabs : Tendsto (fun i => |A i|) atTop atTop)
    (ht : Tendsto (fun i => |A i| - t i) atTop atTop)
    (hT : Tendsto (fun i => T i - |A i|) atTop atTop) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ i in atTop,
      c₀ ≤ ‖evenFourierCutoff (T i) (soninPacketEven b c hb hbc (2 * Real.pi * A i)) -
            evenFourierCutoff s (soninPacketEven b c hb hbc (2 * Real.pi * A i))‖ ^ (2 : ℕ) -
          ‖evenFourierCutoff (t i) (soninPacketEven b c hb hbc (2 * Real.pi * A i)) -
            evenFourierCutoff s (soninPacketEven b c hb hbc (2 * Real.pi * A i))‖ ^ (2 : ℕ) := by
  set w : ℕ → evenSubspace := fun i => soninPacketEven b c hb hbc (2 * Real.pi * A i) with hw
  set Λ : ℝ := Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ (2 : ℕ)) with hΛ
  have hΛpos : 0 < Λ := sqrt_half_energy_pos b c hb hbc
  have hgapS : Tendsto (fun i => |A i| - s) atTop atTop := by
    have h := hAabs.atTop_add (tendsto_const_nhds (x := -s) (f := atTop (α := ℕ)))
    refine h.congr fun i => ?_
    ring
  have hfixed : Tendsto (fun i => ‖evenFourierCutoff s (w i)‖) atTop (𝓝 0) :=
    tendsto_norm_evenFourierCutoff_soninPacketEven_gap b c hb hbc (fun _ => s) A hgapS hA
  have hinner : Tendsto (fun i => ‖evenFourierCutoff (t i) (w i)‖) atTop (𝓝 0) :=
    tendsto_norm_evenFourierCutoff_soninPacketEven_gap b c hb hbc t A ht hA
  have houter : Tendsto (fun i => ‖w i - evenFourierCutoff (T i) (w i)‖) atTop (𝓝 0) :=
    tendsto_norm_sub_evenFourierCutoff_soninPacketEven_gap b c hb hbc T A hT hA
  have hnorm : Tendsto (fun i => ‖w i‖) atTop (𝓝 Λ) :=
    tendsto_norm_soninPacketEven b c hb hbc (fun i => 2 * Real.pi * A i) hA
  refine ⟨(Λ / 2) ^ (2 : ℕ) - (Λ / 4) ^ (2 : ℕ), by nlinarith, ?_⟩
  have hsmallFixed : ∀ᶠ i in atTop, ‖evenFourierCutoff s (w i)‖ < Λ / 8 :=
    hfixed.eventually_lt_const (by linarith)
  have hsmallInner : ∀ᶠ i in atTop, ‖evenFourierCutoff (t i) (w i)‖ < Λ / 8 :=
    hinner.eventually_lt_const (by linarith)
  have hsmallOuter : ∀ᶠ i in atTop, ‖w i - evenFourierCutoff (T i) (w i)‖ < Λ / 8 :=
    houter.eventually_lt_const (by linarith)
  have hbigNorm : ∀ᶠ i in atTop, 3 * Λ / 4 < ‖w i‖ :=
    hnorm.eventually_const_lt (by linarith)
  filter_upwards [hsmallFixed, hsmallInner, hsmallOuter, hbigNorm] with i h1 h2 h3 h4
  have hhi : Λ / 2 ≤ ‖evenFourierCutoff (T i) (w i) - evenFourierCutoff s (w i)‖ := by
    have hsplit : ‖w i‖ ≤ ‖w i - evenFourierCutoff (T i) (w i)‖ +
        ‖evenFourierCutoff (T i) (w i) - evenFourierCutoff s (w i)‖ +
        ‖evenFourierCutoff s (w i)‖ := by
      calc ‖w i‖ = ‖(w i - evenFourierCutoff (T i) (w i)) +
            ((evenFourierCutoff (T i) (w i) - evenFourierCutoff s (w i)) +
              evenFourierCutoff s (w i))‖ := by congr 1; abel
        _ ≤ ‖w i - evenFourierCutoff (T i) (w i)‖ +
            ‖(evenFourierCutoff (T i) (w i) - evenFourierCutoff s (w i)) +
              evenFourierCutoff s (w i)‖ := norm_add_le _ _
        _ ≤ ‖w i - evenFourierCutoff (T i) (w i)‖ +
            (‖evenFourierCutoff (T i) (w i) - evenFourierCutoff s (w i)‖ +
              ‖evenFourierCutoff s (w i)‖) := by
              gcongr
              exact norm_add_le _ _
        _ = _ := by ring
    linarith
  have hlo : ‖evenFourierCutoff (t i) (w i) - evenFourierCutoff s (w i)‖ ≤ Λ / 4 := by
    calc ‖evenFourierCutoff (t i) (w i) - evenFourierCutoff s (w i)‖
        ≤ ‖evenFourierCutoff (t i) (w i)‖ + ‖evenFourierCutoff s (w i)‖ := norm_sub_le _ _
      _ ≤ Λ / 4 := by linarith
  have hlo0 : 0 ≤ ‖evenFourierCutoff (t i) (w i) - evenFourierCutoff s (w i)‖ := norm_nonneg _
  have hhi0 : 0 ≤ Λ / 2 := by linarith
  nlinarith

end RHTower
