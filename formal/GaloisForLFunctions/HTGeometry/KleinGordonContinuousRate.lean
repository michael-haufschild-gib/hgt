import GaloisForLFunctions.HTGeometry.KleinGordonExactRate

/-!
# The true rate governs continuous time as well

The growth statements of 409 and 412 are read at multiples of the period. Between periods nothing much
can happen: the leftover piece of time is shorter than one period and costs at most `e^{bT}` (statement
312). So the discrete rate governs continuous time too,

`‖v(t)‖ ≤ (r+ε)^{⌊t/T⌋}·‖v(0)‖·e^{bT}`   for all large `t`,

and when the rate is at least one this is an honest exponential bound with exponent `log(r+ε)/T`, the
Floquet exponent of statement 397 at the tolerance chosen.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section ContinuousRate

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The discrete rate governs continuous time**, at the cost of one period. -/
theorem eventually_norm_kgFieldStateT_le_floor_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∀ᶠ t : ℝ in atTop, ‖kgFieldStateT W g h t‖
      ≤ ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) ^ (⌊t / T⌋₊)
        * ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
  have hpow := eventually_norm_pow_le_of_spectralRadius
    (spectralRadius_kgMonodromy_ne_top hb0 hWb hWs hper) hε
  have hfloor : Tendsto (fun t : ℝ => ⌊t / T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Filter.Tendsto.atTop_div_const hT tendsto_id)
  have hev := hfloor.eventually hpow
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  refine (norm_kgFieldStateT_le_floor hb0 hWb hWs hper hT g h ht0).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h ⌊t / T⌋₊]
  refine le_trans ((kgMonodromy W b hb0 hWb hWs T ^ ⌊t / T⌋₊).le_opNorm _) ?_
  exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

set_option maxHeartbeats 1000000 in
/-- **An exponential bound at the true rate.** When the rate is at least one the discrete bound is an
honest exponential with exponent `log(r+ε)/T`. -/
theorem eventually_norm_kgFieldStateT_le_exp_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε)
    (hq : 1 ≤ (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∀ᶠ t : ℝ in atTop, ‖kgFieldStateT W g h t‖
      ≤ Real.exp (Real.log ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε)
          / T * t) * ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
  set q : ℝ := (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε with hqdef
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmain := eventually_norm_kgFieldStateT_le_floor_rate hb0 hWb hWs hper hT hε g h
  filter_upwards [hmain, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  refine ht.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hfl : ((⌊t / T⌋₊ : ℕ) : ℝ) ≤ t / T := Nat.floor_le (div_nonneg ht0 hT.le)
  have hpow : q ^ (⌊t / T⌋₊) = q ^ ((⌊t / T⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast q _).symm
  rw [hpow]
  have hmono : q ^ ((⌊t / T⌋₊ : ℕ) : ℝ) ≤ q ^ (t / T) :=
    Real.rpow_le_rpow_of_exponent_le hq hfl
  refine hmono.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos hq0]
  congr 1
  field_simp

end ContinuousRate

end GaloisForLFunctions.HTGeometry
