import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedNativeL2
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMClearedOnsetPulseTransform
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedIngoingCurrent
import GaloisForLFunctions.HTGeometry.NegativeRayL2Exclusion

/-! # The on-shell cleared native coefficient is not in radial `L²`

At the on-shell frequency `w = 2s` the cleared onset numerator equals one, so the cleared native
reduced coefficient is `exp((2s + 2)t) · H_s(r(t))` with `r(t) = -tanh t`.  Its horizon value is
`H_s(1) = -8 · 2^{2s} · (s + 1)(2s + 1)`, nonzero for `Re s < -1`, while `Re(2s + 2) < 0` makes the
exponential grow on the negative ray.  Hence the coefficient is not square integrable there. -/

open Set Filter Topology MeasureTheory Complex

namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial

set_option autoImplicit false

/-- The on-shell horizon profile `H_s(u) = h_{s,0}(u) + 2s · h_{s,1}(u)`. -/
noncomputable def onShellHorizonProfile (s : ℂ) (u : ℝ) : ℂ :=
  sourceHorizonProfile s 1 0 u + 2 * s * sourceHorizonProfile s 1 1 u

/-- **The compulsory horizon boundary datum**: `H_s(1) = -8 · 2^{2s} · (s + 1)(2s + 1)`. -/
theorem onShellHorizonProfile_one (s : ℂ) :
    onShellHorizonProfile s 1 = -8 * power (2 * s) 2 * (s + 1) * (2 * s + 1) := by
  have h2 : (1 : ℝ) + 1 = 2 := by norm_num
  simp only [onShellHorizonProfile, sourceHorizonProfile, reducedHorizonPolynomial, h2,
    show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, Complex.ofReal_one]
  ring

theorem onShellHorizonProfile_one_ne_zero {s : ℂ} (hs : s.re < -1) :
    onShellHorizonProfile s 1 ≠ 0 := by
  rw [onShellHorizonProfile_one]
  have hp : power (2 * s) 2 ≠ 0 := by
    simp only [power]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have h1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : 2 * s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) h1) h2

/-- On shell, the cleared native coefficient is a horizon exponential times `H_s(r(t))`. -/
theorem clearedReducedCoefficient_onShell (s : ℂ) (t : ℝ) :
    clearedReducedCoefficient s 1 (2 * s) t =
      Complex.exp ((2 * s + 2) * (t : ℂ)) * onShellHorizonProfile s (radialUnit t) := by
  rw [clearedReducedCoefficient, clearedOnset_source_rate, reducedCoefficient_frequency_horizon,
    one_mul, onShellHorizonProfile]

/-- The compact radius tends to the horizon `u = 1` at the end of the negative ray, from inside
`[0, 1]`. -/
theorem radialUnit_tendsto_atBot : Tendsto radialUnit atBot (𝓝[Icc 0 1] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have he : Tendsto (fun t : ℝ => Real.exp (2 * t)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num : (0 : ℝ) < 2))
    have hsq : Tendsto (fun t : ℝ => 1 - 2 * Real.exp (2 * t)) atBot (𝓝 1) := by
      simpa using (he.const_mul 2).const_sub 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_lt_atBot 0] with t ht
      have h := radialUnit_one_sub t
      have hb := radialUnit_bounds t ht
      have hpos := Real.exp_pos (2 * t)
      nlinarith
    · filter_upwards [eventually_lt_atBot 0] with t ht
      exact (radialUnit_bounds t ht).2.le
  · filter_upwards [eventually_lt_atBot 0] with t ht
    have hb := radialUnit_bounds t ht
    exact ⟨hb.1.le, hb.2.le⟩

/-- **On-shell native `L²` no-go.**  For `Re s < -1`, the unit-amplitude cleared native reduced
coefficient at `w = 2s` is not in `L²` of the negative ray. -/
theorem not_memLp_clearedReducedCoefficient_onShell {s : ℂ} (hs : s.re < -1) :
    ¬ MemLp (clearedReducedCoefficient s 1 (2 * s)) 2 (volume.restrict (Iio 0)) := by
  apply GaloisForLFunctions.HTGeometry.not_memLp_two_restrict_Iio_of_atBot_norm_ge_one
  set c := ‖onShellHorizonProfile s 1‖
  have hc : 0 < c := norm_pos_iff.mpr (onShellHorizonProfile_one_ne_zero hs)
  have hH : ContinuousOn (onShellHorizonProfile s) (Icc 0 1) :=
    (sourceHorizonProfile_continuousOn s 1 0).add
      (continuousOn_const.mul (sourceHorizonProfile_continuousOn s 1 1))
  have hlim : Tendsto (fun t => ‖onShellHorizonProfile s (radialUnit t)‖) atBot (𝓝 c) :=
    ((hH 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp radialUnit_tendsto_atBot).norm
  have hb : 2 * s.re + 2 < 0 := by linarith
  have hexp : Tendsto (fun t : ℝ => Real.exp ((2 * s.re + 2) * t)) atBot atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atBot_of_neg hb)
  filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hc)),
    hexp.eventually (eventually_ge_atTop (2 / c))] with t hH hE
  rw [clearedReducedCoefficient_onShell, norm_mul, Complex.norm_exp]
  have hre : ((2 * s + 2) * (t : ℂ)).re = (2 * s.re + 2) * t := by simp
  rw [hre]
  calc (1 : ℝ) = 2 / c * (c / 2) := by field_simp
    _ ≤ Real.exp ((2 * s.re + 2) * t) * ‖onShellHorizonProfile s (radialUnit t)‖ :=
      mul_le_mul hE hH.le (by positivity) (Real.exp_pos _).le

/-- The no-go at every physical Xi rate. -/
theorem not_memLp_clearedReducedCoefficient_physicalRate (q : XiZeroCopy) (branch : Bool) :
    ¬ MemLp (clearedReducedCoefficient (D4BMModularCore.physicalRate q branch) 1
      (2 * D4BMModularCore.physicalRate q branch)) 2 (volume.restrict (Iio 0)) := by
  apply not_memLp_clearedReducedCoefficient_onShell
  have h := D4BMModularCore.currentRate_re_lt q branch
  rw [D4BMModularCore.currentRate] at h
  simp at h
  linarith

/-- The no-go at every doubled (cusp-projection) physical rate. -/
theorem not_memLp_clearedReducedCoefficient_cuspPhysicalRate (q : XiZeroCopy) (branch : Bool) :
    ¬ MemLp (clearedReducedCoefficient (D4BMCuspProjection.physicalRate q branch) 1
      (2 * D4BMCuspProjection.physicalRate q branch)) 2 (volume.restrict (Iio 0)) := by
  apply not_memLp_clearedReducedCoefficient_onShell
  linarith [(D4BMCuspProjection.physicalRate_re_bounds q branch).2]

end RHTower.D4BMJointSource
