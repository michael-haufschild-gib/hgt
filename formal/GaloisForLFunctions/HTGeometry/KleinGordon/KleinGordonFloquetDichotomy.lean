import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFloquetStability

/-!
# The dichotomy: contraction over one period decides the clock

The stability criterion of statement 310 is about the powers of the monodromy. The crudest thing one
can know about them is the norm of the operator itself, and it already decides the two extreme cases.

Along the periods the state is contracted by `‖M‖` each time, so `‖v(nT)‖ ≤ ‖M‖ⁿ‖v(0)‖`; between
periods the leftover time is shorter than one period and costs at most `e^{bT}`. Hence

* `‖M‖ ≤ 1`: the state is bounded at every time by `e^{bT}` times its datum — the clock keeps running;
* `‖M‖ < 1`: the state tends to zero as time grows — the clock is damped out by the driving.

Both are unconditional statements about the original equation, with the constants read off from one
period.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Dichotomy

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The state is contracted by the monodromy norm each period.** -/
theorem norm_kgFieldStateT_period_le_pow (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    ‖kgFieldStateT W g h (n * T)‖
      ≤ ‖kgMonodromy W b hb0 hWb hWs T‖ ^ n * ‖kgPair E (g, h)‖ := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul]
      rw [kgFieldStateT_zero]
  | succ n ih =>
      have hsum : ((n + 1 : ℕ) : ℝ) * T = T + n * T := by push_cast; ring
      have hstep := kgFieldStateT_period hb0 hWb hWs hper g h n
      rw [hsum, hstep, ← kgMonodromy_apply (T := T) hb0 hWb hWs]
      refine le_trans ((kgMonodromy W b hb0 hWb hWs T).le_opNorm _) ?_
      have hM0 : (0 : ℝ) ≤ ‖kgMonodromy W b hb0 hWb hWs T‖ := norm_nonneg _
      calc ‖kgMonodromy W b hb0 hWb hWs T‖ * ‖kgFieldStateT W g h (n * T)‖
          ≤ ‖kgMonodromy W b hb0 hWb hWs T‖
              * (‖kgMonodromy W b hb0 hWb hWs T‖ ^ n * ‖kgPair E (g, h)‖) :=
            mul_le_mul_of_nonneg_left ih hM0
        _ = ‖kgMonodromy W b hb0 hWb hWs T‖ ^ (n + 1) * ‖kgPair E (g, h)‖ := by ring

/-- **The leftover piece of time costs one period.** -/
theorem norm_kgFieldStateT_le_floor (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) (g h : Lp ℂ 2 (volume : Measure E))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldStateT W g h t‖
      ≤ ‖kgFieldStateT W g h ((⌊t / T⌋₊ : ℝ) * T)‖ * Real.exp (b * T) := by
  set n : ℕ := ⌊t / T⌋₊ with hndef
  have hdiv0 : (0 : ℝ) ≤ t / T := div_nonneg ht hT.le
  have hnle : (n : ℝ) ≤ t / T := Nat.floor_le hdiv0
  have hnlt : t / T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnT : (n : ℝ) * T ≤ t := by
    have hmul := mul_le_mul_of_nonneg_right hnle hT.le
    rwa [div_mul_cancel₀ _ hT.ne'] at hmul
  have hltT : t < ((n : ℝ) + 1) * T := by
    have hmul := mul_lt_mul_of_pos_right hnlt hT
    rwa [div_mul_cancel₀ _ hT.ne'] at hmul
  set r : ℝ := t - (n : ℝ) * T with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrT : r ≤ T := by rw [hrdef]; nlinarith
  have hsplit : t = r + (n : ℝ) * T := by rw [hrdef]; ring
  have hshift : (fun ρ : ℝ => W (ρ + (n : ℝ) * T)) = W :=
    funext (periodic_shift_nat hper n)
  have hrestart := kgFieldStateT_restart hb0 hWb hWs g h r ((n : ℝ) * T)
  rw [hshift] at hrestart
  have hstate : kgPair E (kgFieldGradT W g h ((n : ℝ) * T), kgFieldVelT W g h ((n : ℝ) * T))
      = kgFieldStateT W g h ((n : ℝ) * T) := rfl
  have hstep : ‖kgFieldStateT W (kgFieldGradT W g h ((n : ℝ) * T))
        (kgFieldVelT W g h ((n : ℝ) * T)) r‖
      ≤ ‖kgFieldStateT W g h ((n : ℝ) * T)‖ * Real.exp (b * |r|) := by
    rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, ← hstate]
    exact norm_kgStateMildT_le hb0 hWb hWs _ _ r
  have hexp : Real.exp (b * |r|) ≤ Real.exp (b * T) := by
    rw [abs_of_nonneg hr0]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrT hb0)
  rw [hsplit, hrestart]
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

/-- **A contraction over one period keeps the clock running.** -/
theorem norm_kgFieldStateT_le_of_norm_monodromy_le_one (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T)
    (hM : ‖kgMonodromy W b hb0 hWb hWs T‖ ≤ 1) (g h : Lp ℂ 2 (volume : Measure E))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldStateT W g h t‖ ≤ ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
  refine (norm_kgFieldStateT_le_floor hb0 hWb hWs hper hT g h ht).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine (norm_kgFieldStateT_period_le_pow hb0 hWb hWs hper g h ⌊t / T⌋₊).trans ?_
  have hpow : ‖kgMonodromy W b hb0 hWb hWs T‖ ^ (⌊t / T⌋₊) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hM
  calc ‖kgMonodromy W b hb0 hWb hWs T‖ ^ (⌊t / T⌋₊) * ‖kgPair E (g, h)‖
      ≤ 1 * ‖kgPair E (g, h)‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = ‖kgPair E (g, h)‖ := one_mul _

/-- **A strict contraction over one period damps the clock out.** The state tends to zero along the
periods. -/
theorem tendsto_kgFieldStateT_period_zero (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hM : ‖kgMonodromy W b hb0 hWb hWs T‖ < 1)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun n : ℕ => kgFieldStateT W g h (n * T)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hpow : Tendsto (fun n : ℕ => ‖kgMonodromy W b hb0 hWb hWs T‖ ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (x := ‖kgMonodromy W b hb0 hWb hWs T‖) (by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
    exact h
  have hbound : Tendsto
      (fun n : ℕ => ‖kgMonodromy W b hb0 hWb hWs T‖ ^ n * ‖kgPair E (g, h)‖) atTop (𝓝 0) := by
    simpa using hpow.mul_const (‖kgPair E (g, h)‖)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_kgFieldStateT_period_le_pow hb0 hWb hWs hper g h n) hbound

/-- **A strict contraction over one period damps the clock out**, at every time and not only along
the periods. -/
theorem tendsto_kgFieldStateT_zero (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T)
    (hM : ‖kgMonodromy W b hb0 hWb hWs T‖ < 1) (g h : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => kgFieldStateT W g h t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ t : ℝ in atTop, ‖kgFieldStateT W g h t‖
      ≤ ‖kgMonodromy W b hb0 hWb hWs T‖ ^ (⌊t / T⌋₊)
        * ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    refine (norm_kgFieldStateT_le_floor hb0 hWb hWs hper hT g h ht).trans ?_
    exact mul_le_mul_of_nonneg_right
      (norm_kgFieldStateT_period_le_pow hb0 hWb hWs hper g h ⌊t / T⌋₊) (Real.exp_pos _).le
  have hfloor : Tendsto (fun t : ℝ => ⌊t / T⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Filter.Tendsto.atTop_div_const hT tendsto_id)
  have hpow : Tendsto (fun n : ℕ => ‖kgMonodromy W b hb0 hWb hWs T‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])
  have hcomp : Tendsto (fun t : ℝ => ‖kgMonodromy W b hb0 hWb hWs T‖ ^ (⌊t / T⌋₊))
      atTop (𝓝 0) := hpow.comp hfloor
  have hbound : Tendsto (fun t : ℝ => ‖kgMonodromy W b hb0 hWb hWs T‖ ^ (⌊t / T⌋₊)
      * ‖kgPair E (g, h)‖ * Real.exp (b * T)) atTop (𝓝 0) := by
    simpa using (hcomp.mul_const (‖kgPair E (g, h)‖)).mul_const (Real.exp (b * T))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle hbound

end Dichotomy

end GaloisForLFunctions.HTGeometry
