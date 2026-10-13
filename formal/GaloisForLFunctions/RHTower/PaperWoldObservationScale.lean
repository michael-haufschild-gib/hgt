import GaloisForLFunctions.RHTower.PaperWoldObservationClock

/-! # Polynomial blindness and exponential detection

Along the literal composite exponent approach, all polynomial input lengths
erase the norm defect. Exponential input lengths retain a uniform positive gap,
although every stage is compact and has zero paper ideal cost.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

private theorem cast_power_prefix (a : ℕ) (ha : 1 ≤ a) (k : ℕ) :
    ((a ^ k - 1 : ℕ) : ℝ) + 1 = (a : ℝ) ^ k := by
  have hp : 0 < a ^ k := pow_pos (by omega) _
  exact_mod_cast Nat.sub_add_cancel (show 1 ≤ a ^ k by omega)

/-- Every fixed polynomial degree remains below the native detection scale. -/
theorem paperWoldCompositeApproach_prefix_polynomial_tendsto (k : ℕ) :
    Tendsto (fun N => paperWoldCompositePrefixDefect
      (paperWoldCompositeApproachParameter N) ((N + 1) ^ k - 1)) atTop (𝓝 0) := by
  apply (paperWoldCompositeApproach_prefix_tendsto_zero_iff _).mpr
  have hb : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hl : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hb
  have hk := hl.const_mul (k : ℝ)
  simp only [mul_zero] at hk
  convert hk using 1
  funext N
  rw [cast_power_prefix (N + 1) (by omega), Real.log_pow]
  push_cast
  ring

/-- A prefix of length `2^(N+1)` has a constant positive logarithmic clock. -/
theorem paperWoldCompositeObservationClock_exponential (N : ℕ) :
    paperWoldCompositeObservationClock (paperWoldCompositeApproachParameter N)
      (2 ^ (N + 1) - 1) = 2 * Real.log 2 := by
  rw [paperWoldCompositeObservationClock_approach, cast_power_prefix 2 (by omega), Real.log_pow]
  push_cast
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The actual exponential prefix retains a uniform gap, despite its zero compact-ideal cost. -/
theorem paperWoldCompositeApproach_prefix_exponential_gap (N : ℕ) :
    (1 / 32 : ℝ) ≤ ‖paperWoldCompositePrefixDefect
      (paperWoldCompositeApproachParameter N) (2 ^ (N + 1) - 1)‖ := by
  have h := paperWoldCompositePrefixDefect_clock_lower
    (paperWoldCompositeApproachParameter N) (2 ^ (N + 1) - 1)
  rw [paperWoldCompositeObservationClock_exponential,
    show -(2 * Real.log 2 / 2) = -Real.log 2 by ring,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  norm_num at h
  exact h

/-- Growing finite observations can detect the critical discontinuity. -/
theorem paperWoldCompositeApproach_prefix_exponential_not_tendsto :
    ¬ Tendsto (fun N => paperWoldCompositePrefixDefect
      (paperWoldCompositeApproachParameter N) (2 ^ (N + 1) - 1)) atTop (𝓝 0) := by
  intro h
  have hn := h.norm
  rw [norm_zero] at hn
  have hb : (1 / 32 : ℝ) ≤ 0 := ge_of_tendsto hn
    (Eventually.of_forall paperWoldCompositeApproach_prefix_exponential_gap)
  norm_num at hb

end
end RHTower
