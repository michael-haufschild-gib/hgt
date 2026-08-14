import GaloisForLFunctions.RHTower.RouteEGibbsTerminalChamber

/-!
# The coherent wide batch at the terminal frequency

At the terminal frequency `t_X = π/log X` the critical cosine sum over all primes below `X` is

```text
∑_{p ≤ X} p^{-1/2} cos(t_X log p) = -(2√X/log X)(1 + o(1)),
```

because `t_X log p = π - π v_p/log X` with `v_p = log X - log p`, so the cosine is `-1` up to
`π² v_p²/(2 (log X)²)`, and the prime window law evaluates both the constant and the quadratic
window moments.  This is the linear grade of the batch rapidity.

The initial prefix is bounded away from zero at the same frequency: on the critical line the
signed/unsigned Euler pair has modulus `∏_{p ≤ Y}|1 - p^{-1-2it}| ≥ ∏_{p ≤ Y}(1 - p^{-1}) > 0`,
so no prefix cancellation can remove the terminal lobe.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## The critical cosine sum -/

/-- The critical cosine sum `∑_{2 < p ≤ X} p^{-1/2} cos(t_X log p)`. -/
def criticalCosSum (X : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊X⌋₊,
    (if k.Prime then (k : ℝ) ^ (-(1 : ℝ) / 2) *
      Real.cos (terminalFrequency X * Real.log k) else 0)

theorem abs_criticalCosSum_add_windowSum_le {X : ℝ} (hX : Real.exp 3 ≤ X) :
    |criticalCosSum X + primeWindowSumNoLog (1 / 2) 0 X|
      ≤ Real.pi ^ 2 / (2 * Real.log X ^ 2) * primeWindowSumNoLog (1 / 2) 2 X := by
  have h3 : (1 : ℝ) < Real.exp 3 := by
    have h := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (3 : ℝ) ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 3) hX
    rwa [Real.log_exp] at h
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hsum : criticalCosSum X + primeWindowSumNoLog (1 / 2) 0 X
      = ∑ k ∈ Finset.Ioc 2 ⌊X⌋₊,
        (if k.Prime then (k : ℝ) ^ (-(1 : ℝ) / 2) *
          (Real.cos (terminalFrequency X * Real.log k) + 1) else 0) := by
    rw [criticalCosSum, primeWindowSumNoLog, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp, if_pos hp, pow_zero, mul_one]
      have hexp : ((1 : ℝ) / 2 - 1) = -(1 : ℝ) / 2 := by norm_num
      rw [hexp]
      ring
    · rw [if_neg hp, if_neg hp, if_neg hp]
      ring
  have hbound : Real.pi ^ 2 / (2 * Real.log X ^ 2) * primeWindowSumNoLog (1 / 2) 2 X
      = ∑ k ∈ Finset.Ioc 2 ⌊X⌋₊,
        (if k.Prime then Real.pi ^ 2 / (2 * Real.log X ^ 2) *
          ((k : ℝ) ^ (-(1 : ℝ) / 2) * (Real.log X - Real.log k) ^ 2) else 0) := by
    rw [primeWindowSumNoLog, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      norm_num
    · rw [if_neg hp, if_neg hp, mul_zero]
  rw [hsum, hbound]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k hk => ?_)
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp]
    rw [Finset.mem_Ioc] at hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℕ) < k := by omega
      exact_mod_cast this
    have hkX : (k : ℝ) ≤ X := by
      have h : (k : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hk.2
      exact le_trans h (Nat.floor_le hX0.le)
    have hrp : (0 : ℝ) ≤ (k : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hk0.le _
    have hv0 : (0 : ℝ) ≤ Real.log X - Real.log k := by
      have := Real.log_le_log hk0 hkX
      linarith
    -- the phase identity
    have hphase : terminalFrequency X * Real.log k
        = Real.pi - Real.pi * (Real.log X - Real.log k) / Real.log X := by
      rw [terminalFrequency]
      field_simp
      ring
    have hcos : Real.cos (terminalFrequency X * Real.log k)
        = -Real.cos (Real.pi * (Real.log X - Real.log k) / Real.log X) := by
      rw [hphase, Real.cos_pi_sub]
    have hquad : 1 - Real.cos (Real.pi * (Real.log X - Real.log k) / Real.log X)
        ≤ (Real.pi * (Real.log X - Real.log k) / Real.log X) ^ 2 / 2 := by
      have h := Real.one_sub_sq_div_two_le_cos
        (x := Real.pi * (Real.log X - Real.log k) / Real.log X)
      linarith
    have hval : (Real.pi * (Real.log X - Real.log k) / Real.log X) ^ 2 / 2
        = Real.pi ^ 2 / (2 * Real.log X ^ 2) * (Real.log X - Real.log k) ^ 2 := by
      field_simp
    have hnonneg : 0 ≤ 1 - Real.cos (Real.pi * (Real.log X - Real.log k) / Real.log X) := by
      have := Real.cos_le_one (Real.pi * (Real.log X - Real.log k) / Real.log X)
      linarith
    rw [hcos]
    have habs : |(k : ℝ) ^ (-(1 : ℝ) / 2) *
        (-Real.cos (Real.pi * (Real.log X - Real.log k) / Real.log X) + 1)|
        = (k : ℝ) ^ (-(1 : ℝ) / 2) *
          (1 - Real.cos (Real.pi * (Real.log X - Real.log k) / Real.log X)) := by
      rw [abs_mul, abs_of_nonneg hrp, abs_of_nonneg (by linarith)]
      ring
    rw [habs]
    calc (k : ℝ) ^ (-(1 : ℝ) / 2) *
        (1 - Real.cos (Real.pi * (Real.log X - Real.log k) / Real.log X))
        ≤ (k : ℝ) ^ (-(1 : ℝ) / 2) *
          (Real.pi ^ 2 / (2 * Real.log X ^ 2) * (Real.log X - Real.log k) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hrp
          rw [← hval]
          exact hquad
      _ = Real.pi ^ 2 / (2 * Real.log X ^ 2) *
          ((k : ℝ) ^ (-(1 : ℝ) / 2) * (Real.log X - Real.log k) ^ 2) := by ring
  · rw [if_neg hp, if_neg hp, abs_zero]

/-- **The critical cosine sum.**  `∑_{p ≤ X} p^{-1/2} cos(t_X log p) = -(2√X/log X)(1+o(1))`. -/
theorem tendsto_criticalCosSum :
    Tendsto (fun X : ℝ => criticalCosSum X * Real.log X / X ^ ((1 : ℝ) / 2)) atTop
      (nhds (-2)) := by
  have ha0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hN0 := tendsto_logY_mul_primeWindowSumNoLog ha0 0
  have hN2 := tendsto_logY_mul_primeWindowSumNoLog ha0 2
  have hc0 : (Nat.factorial 0 : ℝ) / ((1 : ℝ) / 2) ^ (0 + 1) = 2 := by
    simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    norm_num
  have hc2 : (Nat.factorial 2 : ℝ) / ((1 : ℝ) / 2) ^ (2 + 1) = 16 := by
    norm_num [Nat.factorial]
  rw [hc0] at hN0
  rw [hc2] at hN2
  -- the error term
  have herr : Tendsto (fun X : ℝ =>
      Real.pi ^ 2 / (2 * Real.log X ^ 2) *
        (Real.log X * primeWindowSumNoLog (1 / 2) 2 X / X ^ ((1 : ℝ) / 2))) atTop (nhds 0) := by
    have hinv : Tendsto (fun X : ℝ => Real.pi ^ 2 / (2 * Real.log X ^ 2)) atTop (nhds 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      have hL2 : Tendsto (fun X : ℝ => Real.log X ^ 2) atTop atTop := by
        have h := Filter.Tendsto.atTop_mul_atTop₀ Real.tendsto_log_atTop Real.tendsto_log_atTop
        refine h.congr fun X => ?_
        ring
      exact hL2.const_mul_atTop (by norm_num)
    have h := hinv.mul hN2
    rwa [zero_mul] at h
  have hmain := hN0.neg
  have hsum := hmain.add (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (nhds 0))
  rw [add_zero] at hsum
  -- squeeze
  have hsqueeze : Tendsto (fun X : ℝ =>
      criticalCosSum X * Real.log X / X ^ ((1 : ℝ) / 2)
        + Real.log X * primeWindowSumNoLog (1 / 2) 0 X / X ^ ((1 : ℝ) / 2)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [eventually_ge_atTop (Real.exp 3)] with X hX
    have h3 : (1 : ℝ) < Real.exp 3 := by
      have h := Real.add_one_le_exp (3 : ℝ)
      linarith
    have hX1 : (1 : ℝ) < X := by linarith
    have hX0 : (0 : ℝ) < X := by linarith
    have hlogX : (3 : ℝ) ≤ Real.log X := by
      have h := Real.log_le_log (Real.exp_pos 3) hX
      rwa [Real.log_exp] at h
    have hlogXpos : (0 : ℝ) < Real.log X := by linarith
    have hXhalf : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hX0 _
    have hbound := abs_criticalCosSum_add_windowSum_le hX
    have hval : criticalCosSum X * Real.log X / X ^ ((1 : ℝ) / 2)
        + Real.log X * primeWindowSumNoLog (1 / 2) 0 X / X ^ ((1 : ℝ) / 2)
        = (criticalCosSum X + primeWindowSumNoLog (1 / 2) 0 X) * Real.log X /
          X ^ ((1 : ℝ) / 2) := by
      field_simp
    rw [Real.norm_eq_abs, hval, abs_div, abs_mul, abs_of_pos hXhalf, abs_of_pos hlogXpos]
    have hstep : |criticalCosSum X + primeWindowSumNoLog (1 / 2) 0 X| * Real.log X /
        X ^ ((1 : ℝ) / 2)
        ≤ (Real.pi ^ 2 / (2 * Real.log X ^ 2) * primeWindowSumNoLog (1 / 2) 2 X) * Real.log X /
          X ^ ((1 : ℝ) / 2) := by
      apply div_le_div_of_nonneg_right _ hXhalf.le
      exact mul_le_mul_of_nonneg_right hbound hlogXpos.le
    have hrw : (Real.pi ^ 2 / (2 * Real.log X ^ 2) * primeWindowSumNoLog (1 / 2) 2 X) *
        Real.log X / X ^ ((1 : ℝ) / 2)
        = Real.pi ^ 2 / (2 * Real.log X ^ 2) *
          (Real.log X * primeWindowSumNoLog (1 / 2) 2 X / X ^ ((1 : ℝ) / 2)) := by
      field_simp
    rw [hrw] at hstep
    exact hstep
  have hfinal := hsqueeze.sub hN0
  rw [zero_sub] at hfinal
  refine hfinal.congr fun X => ?_
  ring

/-! ## The prefix modulus -/

/-- **The prefix modulus does not vanish.**  On the critical line the signed/unsigned Euler pair
of an initial prime prefix has modulus at least `∏_{p ∈ S}(1 - 1/p)`. -/
theorem prefixModulus_ge (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (t : ℝ) :
    ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
      ≤ ∏ p ∈ S, ‖1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * Real.log p) : ℝ) : ℂ) * Complex.I)‖ := by
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hprime := hS p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  · have hprime := hS p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hnorm : ‖(((p : ℝ)⁻¹ : ℝ) : ℂ) *
        Complex.exp (((-(2 * t * Real.log p) : ℝ) : ℂ) * Complex.I)‖ = (p : ℝ)⁻¹ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (p : ℝ)⁻¹)]
      rw [Complex.norm_exp_ofReal_mul_I, mul_one]
    have h := norm_sub_norm_le (1 : ℂ) ((((p : ℝ)⁻¹ : ℝ) : ℂ) *
      Complex.exp (((-(2 * t * Real.log p) : ℝ) : ℂ) * Complex.I))
    rw [norm_one, hnorm] at h
    linarith

end

end RHTower
