import GaloisForLFunctions.RHTower.SoninFourierChannelBlowUp
import GaloisForLFunctions.RHTower.SoninLogShellChannelGrowth

/-!
# An explicit schedule realising the frequency-side blow-up

Reading the carrier along the tower itself makes the bracketing schedule immediate: put the carrier
at height `2i`, the inner radius at height `i` and the outer radius at height `3i`.  The geometric
growth then separates all three by a factor tending to infinity, and the inner radius climbs.

So the blow-up hypothesis is not empty: there is an explicit carrier and height schedule for which
the frequency-side channel sends the wavepackets to vectors of unbounded norm.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology

/-- The tower radii grow without bound. -/
theorem tendsto_logShellRadius_atTop (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    Tendsto (fun k : ℕ => logShellRadius a r k) atTop atTop := by
  have hpow : Tendsto (fun k : ℕ => r ^ k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hr
  exact hpow.atTop_mul_const ha

/-- **An explicit blow-up instance.**  With the carrier read at height `2i` and the tower bracketed
between heights `i` and `3i`, the frequency-side channel blows up on the wavepackets. -/
theorem exists_schedule_tendsto_norm_evenFourierLogShellChannel_atTop
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (a₀ r₀ : ℝ) (ha₀ : 0 < a₀) (hr₀ : 1 < r₀) :
    ∃ (A : ℕ → ℝ) (m n : ℕ → ℕ),
      Tendsto (fun i => 2 * Real.pi * A i) atTop atTop ∧ (∀ i, m i ≤ n i) ∧
        Tendsto (fun i => ‖evenFourierLogShellChannel a₀ r₀ (n i)
          (soninPacketEven b c hb hbc (2 * Real.pi * A i))‖) atTop atTop := by
  have hr0 : (0 : ℝ) < r₀ := zero_lt_one.trans hr₀
  have hlogr : 0 < Real.log r₀ := Real.log_pos hr₀
  refine ⟨fun i => logShellRadius a₀ r₀ (2 * i), fun i => i, fun i => 3 * i, ?_,
    fun i => by show i ≤ 3 * i; omega, ?_⟩
  · have hrad : Tendsto (fun i : ℕ => logShellRadius a₀ r₀ (2 * i)) atTop atTop :=
      (tendsto_logShellRadius_atTop a₀ r₀ ha₀ hr₀).comp
        (Filter.tendsto_atTop_atTop_of_monotone (fun i j hij => by omega)
          (fun k => ⟨k, by omega⟩))
    exact hrad.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
  · have habs : ∀ i : ℕ, |logShellRadius a₀ r₀ (2 * i)| = logShellRadius a₀ r₀ (2 * i) :=
      fun i => abs_of_pos (logShellRadius_pos ha₀ hr₀ (2 * i))
    have hA : Tendsto (fun i : ℕ => 2 * Real.pi * logShellRadius a₀ r₀ (2 * i)) atTop atTop := by
      have hrad : Tendsto (fun i : ℕ => logShellRadius a₀ r₀ (2 * i)) atTop atTop :=
        (tendsto_logShellRadius_atTop a₀ r₀ ha₀ hr₀).comp
          (Filter.tendsto_atTop_atTop_of_monotone (fun i j hij => by omega)
            (fun k => ⟨k, by omega⟩))
      exact hrad.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
    have hAabs : Tendsto (fun i : ℕ => |logShellRadius a₀ r₀ (2 * i)|) atTop atTop := by
      have hrad : Tendsto (fun i : ℕ => logShellRadius a₀ r₀ (2 * i)) atTop atTop :=
        (tendsto_logShellRadius_atTop a₀ r₀ ha₀ hr₀).comp
          (Filter.tendsto_atTop_atTop_of_monotone (fun i j hij => by omega)
            (fun k => ⟨k, by omega⟩))
      exact hrad.congr fun i => (habs i).symm
    have hminorant : Tendsto (fun i : ℕ => a₀ * (r₀ ^ i - 1)) atTop atTop := by
      have hpow : Tendsto (fun i : ℕ => r₀ ^ i) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hr₀
      have hsub : Tendsto (fun i : ℕ => r₀ ^ i - 1) atTop atTop :=
        hpow.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)) (f := atTop (α := ℕ))) |>.congr
          fun i => by ring
      exact hsub.const_mul_atTop ha₀
    have hinner : Tendsto (fun i : ℕ =>
        |logShellRadius a₀ r₀ (2 * i)| - logShellRadius a₀ r₀ i) atTop atTop := by
      refine tendsto_atTop_mono (fun i => ?_) hminorant
      rw [habs i]
      have hone : (1 : ℝ) ≤ r₀ ^ i := one_le_pow₀ hr₀.le
      have hexp : logShellRadius a₀ r₀ (2 * i) = a₀ * (r₀ ^ i * r₀ ^ i) := by
        rw [logShellRadius, two_mul, pow_add]
        ring
      rw [hexp, logShellRadius]
      have hstep : r₀ ^ i - 1 ≤ r₀ ^ i * (r₀ ^ i - 1) :=
        le_mul_of_one_le_left (sub_nonneg.mpr hone) hone
      nlinarith [hstep, ha₀.le]
    have houter : Tendsto (fun i : ℕ =>
        logShellRadius a₀ r₀ (3 * i) - |logShellRadius a₀ r₀ (2 * i)|) atTop atTop := by
      refine tendsto_atTop_mono (fun i => ?_) hminorant
      rw [habs i]
      have hone : (1 : ℝ) ≤ r₀ ^ i := one_le_pow₀ hr₀.le
      have h3 : logShellRadius a₀ r₀ (3 * i) = a₀ * (r₀ ^ i * (r₀ ^ i * r₀ ^ i)) := by
        rw [logShellRadius, show 3 * i = i + (i + i) by omega, pow_add, pow_add]
        ring
      have h2 : logShellRadius a₀ r₀ (2 * i) = a₀ * (r₀ ^ i * r₀ ^ i) := by
        rw [logShellRadius, two_mul, pow_add]
        ring
      rw [h3, h2]
      have hsq1 : (1 : ℝ) ≤ r₀ ^ i * r₀ ^ i := by nlinarith
      have hstep : r₀ ^ i - 1 ≤ r₀ ^ i * r₀ ^ i * (r₀ ^ i - 1) :=
        le_mul_of_one_le_left (sub_nonneg.mpr hone) hsq1
      nlinarith [hstep, ha₀.le]
    have hclimb : Tendsto (fun i : ℕ => Real.log (logShellRadius a₀ r₀ i)) atTop atTop := by
      have hform : ∀ i : ℕ, Real.log (logShellRadius a₀ r₀ i) =
          (i : ℝ) * Real.log r₀ + Real.log a₀ := fun i => log_logShellRadius a₀ r₀ ha₀ hr₀ i
      have hlin : Tendsto (fun i : ℕ => (i : ℝ) * Real.log r₀ + Real.log a₀) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_mul_const hlogr).atTop_add
          (tendsto_const_nhds (x := Real.log a₀) (f := atTop (α := ℕ)))
      exact hlin.congr fun i => (hform i).symm
    exact tendsto_norm_evenFourierLogShellChannel_soninPacketEven_atTop b c hb hbc a₀ r₀ ha₀ hr₀
      (fun i => logShellRadius a₀ r₀ (2 * i)) hA hAabs (fun i => i) (fun i => 3 * i)
      (fun i => by omega) hinner houter hclimb

end RHTower
