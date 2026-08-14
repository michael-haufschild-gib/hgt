import GaloisForLFunctions.RHTower.RouteEGibbsPrefixPhase

/-!
# Stability of the prefix modulus

On the critical line the signed/unsigned Euler pair of an initial prefix has modulus

```text
∏_{p ≤ Y} |1 - p^{-1-2it}|,
```

whose local square is exactly `(1 - 1/p)² + (2/p)(1 - cos(2t log p))`.  Hence the modulus is
between `∏_{p ≤ Y}(1 - 1/p)` and that product times `exp(8t²(log Y)² ∑_{p ≤ Y} 1/p)`, so at the
terminal frequency `t_X = π/log X` with prefix `Y = (log X)^A` the ratio tends to one: the prefix
modulus is stable, and by Mertens' third theorem it is of exact order `1/log Y`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The prefix modulus `∏_{p ≤ Y}|1 - p^{-1-2it}|`. -/
def prefixModulus (Y t : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
    ‖1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) * Complex.exp (((-(2 * t * Real.log p) : ℝ) : ℂ) * Complex.I)‖

/-- The exact local modulus square. -/
theorem norm_one_sub_smul_exp_sq (u θ : ℝ) :
    ‖1 - ((u : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ ^ 2
      = (1 - u) ^ 2 + 2 * u * (1 - Real.cos θ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (1 - ((u : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).re
      = 1 - u * Real.cos θ := by
    rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg]
    ring
  have him : (1 - ((u : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).im
      = u * Real.sin θ := by
    rw [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    ring
  rw [hre, him]
  linear_combination (u ^ 2) * Real.sin_sq_add_cos_sq θ

/-- Each local factor is at most the positive factor times a quadratic phase correction. -/
theorem norm_one_sub_smul_exp_le {u θ : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    ‖1 - ((u : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖
      ≤ (1 - u) * (1 + 2 * u * θ ^ 2) := by
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := θ)
    linarith
  have hcos0 : 0 ≤ 1 - Real.cos θ := by
    have := Real.cos_le_one θ
    linarith
  have hsq := norm_one_sub_smul_exp_sq u θ
  have hu1 : (1 : ℝ) / 2 ≤ 1 - u := by linarith
  have hutheta : (0 : ℝ) ≤ u * θ ^ 2 := by positivity
  have hrhs0 : (0 : ℝ) ≤ (1 - u) * (1 + 2 * u * θ ^ 2) := by nlinarith
  have h2u : 2 * u * (1 - Real.cos θ) ≤ u * θ ^ 2 := by nlinarith
  have hquarter : (1 : ℝ) / 4 ≤ (1 - u) ^ 2 := by nlinarith
  have hexpand : ((1 - u) * (1 + 2 * u * θ ^ 2)) ^ 2
      = (1 - u) ^ 2 + (1 - u) ^ 2 * (4 * (u * θ ^ 2) + 4 * (u * θ ^ 2) ^ 2) := by ring
  have hstep : (1 - u) ^ 2 + u * θ ^ 2 ≤ ((1 - u) * (1 + 2 * u * θ ^ 2)) ^ 2 := by
    rw [hexpand]
    nlinarith [hquarter, hutheta, sq_nonneg (u * θ ^ 2)]
  have hsqle : ‖1 - ((u : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ ((1 - u) * (1 + 2 * u * θ ^ 2)) ^ 2 := by
    rw [hsq]
    linarith
  have hnorm0 : (0 : ℝ) ≤ ‖1 - ((u : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ :=
    norm_nonneg _
  nlinarith [hsqle, hnorm0, hrhs0]

/-- **Prefix modulus stability, upper form.** -/
theorem prefixModulus_le {Y t : ℝ} (hY : 2 ≤ Y) :
    prefixModulus Y t
      ≤ (∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - (p : ℝ)⁻¹)) *
        Real.exp (8 * t ^ 2 * Real.log Y ^ 2 * Sieve.mertensS ⌊Y⌋₊) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hterm : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      ‖1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) * Complex.exp (((-(2 * t * Real.log p) : ℝ) : ℂ) * Complex.I)‖
        ≤ (1 - (p : ℝ)⁻¹) * Real.exp (8 * t ^ 2 * Real.log Y ^ 2 * (p : ℝ)⁻¹) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hinv0 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    have hinvle : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    have hple : (p : ℝ) ≤ Y := by
      have hmem : p ≤ ⌊Y⌋₊ := (Nat.mem_primesLE.mp hp).1
      have h : (p : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmem
      exact le_trans h (Nat.floor_le hY0.le)
    have hlogp0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogple : Real.log p ≤ Real.log Y := Real.log_le_log hp0 hple
    have hbound := norm_one_sub_smul_exp_le (u := (p : ℝ)⁻¹)
      (θ := 2 * t * Real.log p) hinv0 hinvle
    have hphase : (2 * t * Real.log p) ^ 2 ≤ 4 * t ^ 2 * Real.log Y ^ 2 := by
      have hsq : Real.log p ^ 2 ≤ Real.log Y ^ 2 := pow_le_pow_left₀ hlogp0 hlogple 2
      nlinarith [sq_nonneg t, hsq]
    have hquad : 1 + 2 * (p : ℝ)⁻¹ * (2 * t * Real.log p) ^ 2
        ≤ Real.exp (8 * t ^ 2 * Real.log Y ^ 2 * (p : ℝ)⁻¹) := by
      have hle : 2 * (p : ℝ)⁻¹ * (2 * t * Real.log p) ^ 2
          ≤ 8 * t ^ 2 * Real.log Y ^ 2 * (p : ℝ)⁻¹ := by
        nlinarith [hphase, hinv0]
      have hexp := Real.add_one_le_exp (8 * t ^ 2 * Real.log Y ^ 2 * (p : ℝ)⁻¹)
      linarith
    have hpos : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by linarith
    calc ‖1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) *
          Complex.exp (((-(2 * t * Real.log p) : ℝ) : ℂ) * Complex.I)‖
        ≤ (1 - (p : ℝ)⁻¹) * (1 + 2 * (p : ℝ)⁻¹ * (2 * t * Real.log p) ^ 2) := hbound
      _ ≤ (1 - (p : ℝ)⁻¹) * Real.exp (8 * t ^ 2 * Real.log Y ^ 2 * (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hquad hpos
  have hprod : prefixModulus Y t
      ≤ ∏ p ∈ Nat.primesLE ⌊Y⌋₊,
        ((1 - (p : ℝ)⁻¹) * Real.exp (8 * t ^ 2 * Real.log Y ^ 2 * (p : ℝ)⁻¹)) :=
    Finset.prod_le_prod (fun p _ => norm_nonneg _) hterm
  refine le_trans hprod (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Sieve.mertensS, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun p _ => by rw [one_div]

/-- **Prefix modulus stability, lower form.** -/
theorem prefixModulus_ge' (Y t : ℝ) :
    (∏ p ∈ Nat.primesLE ⌊Y⌋₊, (1 - (p : ℝ)⁻¹)) ≤ prefixModulus Y t :=
  prefixModulus_ge (Nat.primesLE ⌊Y⌋₊) (fun p hp => Nat.prime_of_mem_primesLE hp) t

/-- Past `exp(exp(2/A + 1))` the prefix window is large in every needed sense. -/
theorem prefixWindow_facts {A : ℝ} (hA : 0 < A) {X : ℝ}
    (hX : Real.exp (Real.exp (2 / A + 1)) < X) :
    (1 : ℝ) < X ∧ (2 : ℝ) < Real.log X ∧ (0 : ℝ) < Real.log (Real.log X)
      ∧ (2 : ℝ) ≤ Real.log X ^ A ∧ 2 ≤ ⌊Real.log X ^ A⌋₊ := by
  have hepos : (0 : ℝ) < Real.exp (Real.exp (2 / A + 1)) := Real.exp_pos _
  have he1 : (2 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have hexpge : Real.exp 1 ≤ Real.exp (2 / A + 1) := by
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) < 2 / A := by positivity
    linarith
  have hX1 : (1 : ℝ) < X := by
    have h1 : (1 : ℝ) < Real.exp (Real.exp (2 / A + 1)) := by
      have h := Real.add_one_le_exp (Real.exp (2 / A + 1))
      have := Real.exp_pos (2 / A + 1)
      linarith
    linarith
  have hlogXge : Real.exp (2 / A + 1) ≤ Real.log X := by
    have h := Real.log_le_log hepos hX.le
    rwa [Real.log_exp] at h
  have hlogX2 : (2 : ℝ) < Real.log X := by linarith
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hloglog : (0 : ℝ) < Real.log (Real.log X) := Real.log_pos (by linarith)
  have hYtwo : (2 : ℝ) ≤ Real.log X ^ A := by
    have hmono : Real.exp (2 / A + 1) ^ A ≤ Real.log X ^ A :=
      Real.rpow_le_rpow (Real.exp_pos _).le hlogXge hA.le
    have hval : Real.exp (2 / A + 1) ^ A = Real.exp (2 + A) := by
      rw [← Real.exp_mul]
      congr 1
      field_simp
    rw [hval] at hmono
    have h2 : (2 : ℝ) ≤ Real.exp (2 + A) := by
      have hle : Real.exp 2 ≤ Real.exp (2 + A) := Real.exp_le_exp.mpr (by linarith)
      have h2e : (2 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        linarith
      linarith
    linarith
  exact ⟨hX1, hlogX2, hloglog, hYtwo, Nat.le_floor (by exact_mod_cast hYtwo)⟩

/-- **Prefix modulus stability at the terminal frequency.**  The prefix modulus is asymptotically
the positive Euler product, hence of exact order `1/log Y`. -/
theorem tendsto_prefixModulus_ratio {A : ℝ} (hA : 0 < A) :
    Tendsto (fun X : ℝ => prefixModulus (Real.log X ^ A) (terminalFrequency X) /
        ∏ p ∈ Nat.primesLE ⌊Real.log X ^ A⌋₊, (1 - (p : ℝ)⁻¹)) atTop (nhds 1) := by
  have hprodpos : ∀ N : ℕ, (0 : ℝ) < ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹) := by
    intro N
    refine Finset.prod_pos fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hp0 (by norm_num)]
      linarith
    linarith
  have hmertens0 : ∀ N : ℕ, (0 : ℝ) ≤ Sieve.mertensS N := by
    intro N
    rw [Sieve.mertensS]
    refine Finset.sum_nonneg fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    positivity
  have hmaj : Tendsto (fun X : ℝ =>
      Real.exp (8 * terminalFrequency X ^ 2 * Real.log (Real.log X ^ A) ^ 2 *
        Sieve.mertensS ⌊Real.log X ^ A⌋₊)) atTop (nhds 1) := by
    have hexp : Tendsto (fun X : ℝ =>
        8 * terminalFrequency X ^ 2 * Real.log (Real.log X ^ A) ^ 2 *
          Sieve.mertensS ⌊Real.log X ^ A⌋₊) atTop (nhds 0) := by
      have hmajor : Tendsto (fun X : ℝ =>
          8 * Real.pi ^ 2 * A ^ 3 * (Real.log (Real.log X) ^ 3 / Real.log X ^ (2 : ℝ))
            + 8 * Real.pi ^ 2 * A ^ 2 * Sieve.mertensUpperConst *
              (Real.log (Real.log X) ^ 2 / Real.log X ^ (2 : ℝ))) atTop (nhds 0) := by
        have h3 : Tendsto (fun X : ℝ =>
            Real.log (Real.log X) ^ 3 / Real.log X ^ (2 : ℝ)) atTop (nhds 0) :=
          (HTGeometry.tendsto_logPow_div_rpow (by norm_num : (0:ℝ) < 2) 3).comp
            Real.tendsto_log_atTop
        have h2 : Tendsto (fun X : ℝ =>
            Real.log (Real.log X) ^ 2 / Real.log X ^ (2 : ℝ)) atTop (nhds 0) :=
          (HTGeometry.tendsto_logPow_div_rpow (by norm_num : (0:ℝ) < 2) 2).comp
            Real.tendsto_log_atTop
        have h := (h3.const_mul (8 * Real.pi ^ 2 * A ^ 3)).add
          (h2.const_mul (8 * Real.pi ^ 2 * A ^ 2 * Sieve.mertensUpperConst))
        simp only [mul_zero, add_zero] at h
        exact h
      refine squeeze_zero' ?_ ?_ hmajor
      · filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (2 / A + 1)))] with X hX
        obtain ⟨hX1, hlogX2, hloglog, hYtwo, hfloor⟩ := prefixWindow_facts hA hX
        have hphase0 : (0 : ℝ) ≤ 8 * terminalFrequency X ^ 2 *
            Real.log (Real.log X ^ A) ^ 2 := by positivity
        exact mul_nonneg hphase0 (hmertens0 _)
      · filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (2 / A + 1)))] with X hX
        obtain ⟨hX1, hlogX2, hloglogpos, hYtwo, hfloor⟩ := prefixWindow_facts hA hX
        have hlogX : (0 : ℝ) < Real.log X := by linarith
        have hYpos : (0 : ℝ) < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
        have hfloorle : ((⌊Real.log X ^ A⌋₊ : ℕ) : ℝ) ≤ Real.log X ^ A :=
          Nat.floor_le hYpos.le
        have hfloorpos : (0 : ℝ) < ((⌊Real.log X ^ A⌋₊ : ℕ) : ℝ) := by
          have : (0 : ℕ) < ⌊Real.log X ^ A⌋₊ := by omega
          exact_mod_cast this
        have hlogfloor : Real.log ⌊Real.log X ^ A⌋₊ ≤ Real.log (Real.log X ^ A) :=
          Real.log_le_log hfloorpos hfloorle
        have hmert := Sieve.mertensS_le_logLog_add hfloor
        have hlogY : Real.log (Real.log X ^ A) = A * Real.log (Real.log X) :=
          Real.log_rpow hlogX A
        have hlogYpos : (0 : ℝ) < Real.log (Real.log X ^ A) := by
          rw [hlogY]
          positivity
        have hloglogle : Sieve.logLog ⌊Real.log X ^ A⌋₊ ≤ A * Real.log (Real.log X) := by
          rw [Sieve.logLog]
          have hlogfloorpos : (0 : ℝ) < Real.log ⌊Real.log X ^ A⌋₊ := by
            have h2 : (2 : ℝ) ≤ ((⌊Real.log X ^ A⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor
            have := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2
            have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            linarith
          calc Real.log (Real.log ⌊Real.log X ^ A⌋₊)
              ≤ Real.log (Real.log (Real.log X ^ A)) :=
                Real.log_le_log hlogfloorpos hlogfloor
            _ ≤ Real.log (Real.log X ^ A) := by
                have := Real.log_le_sub_one_of_pos hlogYpos
                linarith
            _ = A * Real.log (Real.log X) := hlogY
        have hmertle : Sieve.mertensS ⌊Real.log X ^ A⌋₊
            ≤ A * Real.log (Real.log X) + Sieve.mertensUpperConst := by linarith
        have hL2 : Real.log X ^ (2 : ℝ) = Real.log X * Real.log X := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          ring
        have hphase : 8 * terminalFrequency X ^ 2 * Real.log (Real.log X ^ A) ^ 2
            = 8 * Real.pi ^ 2 * A ^ 2 * Real.log (Real.log X) ^ 2 /
              (Real.log X * Real.log X) := by
          rw [terminalFrequency, hlogY]
          field_simp
        rw [hphase, hL2]
        have hcoef : (0 : ℝ) ≤ 8 * Real.pi ^ 2 * A ^ 2 * Real.log (Real.log X) ^ 2 /
            (Real.log X * Real.log X) := by positivity
        calc 8 * Real.pi ^ 2 * A ^ 2 * Real.log (Real.log X) ^ 2 /
              (Real.log X * Real.log X) * Sieve.mertensS ⌊Real.log X ^ A⌋₊
            ≤ 8 * Real.pi ^ 2 * A ^ 2 * Real.log (Real.log X) ^ 2 /
              (Real.log X * Real.log X) *
                (A * Real.log (Real.log X) + Sieve.mertensUpperConst) :=
              mul_le_mul_of_nonneg_left hmertle hcoef
          _ = 8 * Real.pi ^ 2 * A ^ 3 *
                (Real.log (Real.log X) ^ 3 / (Real.log X * Real.log X))
              + 8 * Real.pi ^ 2 * A ^ 2 * Sieve.mertensUpperConst *
                (Real.log (Real.log X) ^ 2 / (Real.log X * Real.log X)) := by
              field_simp
    have h := (Real.continuous_exp.tendsto 0).comp hexp
    rw [Real.exp_zero] at h
    simpa [Function.comp_def] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj ?_ ?_
  · filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (2 / A + 1)))] with X hX
    rw [le_div_iff₀ (hprodpos _), one_mul]
    exact prefixModulus_ge' _ _
  · filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (2 / A + 1)))] with X hX
    obtain ⟨hX1, hlogX2, hloglog, hYtwo, hfloor⟩ := prefixWindow_facts hA hX
    rw [div_le_iff₀ (hprodpos _)]
    have h := prefixModulus_le (Y := Real.log X ^ A) (t := terminalFrequency X) hYtwo
    calc prefixModulus (Real.log X ^ A) (terminalFrequency X)
        ≤ (∏ p ∈ Nat.primesLE ⌊Real.log X ^ A⌋₊, (1 - (p : ℝ)⁻¹)) *
          Real.exp (8 * terminalFrequency X ^ 2 * Real.log (Real.log X ^ A) ^ 2 *
            Sieve.mertensS ⌊Real.log X ^ A⌋₊) := h
      _ = Real.exp (8 * terminalFrequency X ^ 2 * Real.log (Real.log X ^ A) ^ 2 *
            Sieve.mertensS ⌊Real.log X ^ A⌋₊) *
          ∏ p ∈ Nat.primesLE ⌊Real.log X ^ A⌋₊, (1 - (p : ℝ)⁻¹) := by ring

end

end RHTower
