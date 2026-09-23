import GaloisForLFunctions.RHTower.SoninFourierChannelBound
import GaloisForLFunctions.RHTower.SoninPacketBandGapFloor

/-!
# The frequency-side channel blows up on the packets

The frequency-side step multiplier reads the packet's mass between two tower radii, and that mass
stays above a fixed level when the inner radius is outrun by the carrier and the outer radius
outruns it.  The multiplier's coefficient on that range is the logarithm of the inner radius, which
diverges as the schedule climbs the tower.

So along such a schedule the channel's values on the packets have unbounded norm — the property that
every position-side candidate failed.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology

/-- **Frequency-side blow-up.**  Along a height schedule whose inner radius is outrun by the
carrier, whose outer radius outruns it, and whose inner radius climbs the tower, the reflected
channel sends the wavepackets to vectors of unbounded norm. -/
theorem tendsto_norm_evenFourierLogShellChannel_soninPacketEven_atTop
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (a₀ r₀ : ℝ) (ha₀ : 0 < a₀) (hr₀ : 1 < r₀)
    (A : ℕ → ℝ) (hA : Tendsto (fun i => 2 * Real.pi * A i) atTop atTop)
    (hAabs : Tendsto (fun i => |A i|) atTop atTop)
    (m n : ℕ → ℕ) (hmn : ∀ i, m i ≤ n i)
    (hinner : Tendsto (fun i => |A i| - logShellRadius a₀ r₀ (m i)) atTop atTop)
    (houter : Tendsto (fun i => logShellRadius a₀ r₀ (n i) - |A i|) atTop atTop)
    (hclimb : Tendsto (fun i => Real.log (logShellRadius a₀ r₀ (m i))) atTop atTop) :
    Tendsto (fun i => ‖evenFourierLogShellChannel a₀ r₀ (n i)
      (soninPacketEven b c hb hbc (2 * Real.pi * A i))‖) atTop atTop := by
  set w : ℕ → evenSubspace := fun i => soninPacketEven b c hb hbc (2 * Real.pi * A i) with hw
  set L : ℕ → ℝ := fun i => Real.log (logShellRadius a₀ r₀ (m i)) with hL
  obtain ⟨c₀, hc₀, hfloor⟩ := exists_pos_eventually_le_fourier_band_gap b c hb hbc
    (logShellRadius a₀ r₀ 0) A (fun i => logShellRadius a₀ r₀ (m i))
    (fun i => logShellRadius a₀ r₀ (n i)) hA hAabs hinner houter
  have hLnn : ∀ᶠ i in atTop, 0 ≤ L i := hclimb.eventually_ge_atTop 0
  have hkey : ∀ᶠ i in atTop, L i ^ (2 : ℕ) * c₀ ≤
      ‖evenFourierLogShellChannel a₀ r₀ (n i) (w i)‖ ^ (2 : ℕ) := by
    filter_upwards [hfloor, hLnn] with i hi hL0
    have hcoeff : ∀ k, m i ≤ k → k < n i → L i ≤ |Real.log (logShellRadius a₀ r₀ k)| := by
      intro k hmk _
      have hpos : 0 < logShellRadius a₀ r₀ (m i) := logShellRadius_pos ha₀ hr₀ (m i)
      have hmono : logShellRadius a₀ r₀ (m i) ≤ logShellRadius a₀ r₀ k :=
        logShellRadius_mono ha₀ hr₀ hmk
      have hlog : L i ≤ Real.log (logShellRadius a₀ r₀ k) := Real.log_le_log hpos hmono
      exact hlog.trans (le_abs_self _)
    have hbound := sq_le_norm_sq_evenFourierLogShellChannel_apply a₀ r₀ ha₀ hr₀ (n i) (m i)
      (hmn i) (w i) (L i) hL0 hcoeff
    have hmul : L i ^ (2 : ℕ) * c₀ ≤ L i ^ (2 : ℕ) *
        (‖evenFourierCutoff (logShellRadius a₀ r₀ (n i)) (w i) -
            evenFourierCutoff (logShellRadius a₀ r₀ 0) (w i)‖ ^ (2 : ℕ) -
          ‖evenFourierCutoff (logShellRadius a₀ r₀ (m i)) (w i) -
            evenFourierCutoff (logShellRadius a₀ r₀ 0) (w i)‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    exact hmul.trans hbound
  have hdiv : Tendsto (fun i => L i ^ (2 : ℕ) * c₀) atTop atTop := by
    have hsq : Tendsto (fun i => L i ^ (2 : ℕ)) atTop atTop := by
      have h := hclimb.atTop_mul_atTop₀ hclimb
      refine h.congr fun i => ?_
      rw [sq]
    exact hsq.atTop_mul_const hc₀
  have hsq : Tendsto (fun i => ‖evenFourierLogShellChannel a₀ r₀ (n i) (w i)‖ ^ (2 : ℕ))
      atTop atTop := tendsto_atTop_mono' atTop hkey hdiv
  refine tendsto_atTop.mpr fun M => ?_
  filter_upwards [hsq.eventually_ge_atTop (max M 0 ^ (2 : ℕ))] with i hi
  have hnn : 0 ≤ ‖evenFourierLogShellChannel a₀ r₀ (n i) (w i)‖ := norm_nonneg _
  have hmax : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hle : max M 0 ≤ ‖evenFourierLogShellChannel a₀ r₀ (n i) (w i)‖ := by nlinarith
  exact le_trans (le_max_left _ _) hle

end RHTower
