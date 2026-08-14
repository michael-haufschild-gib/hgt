import GaloisForLFunctions.RHTower.RouteESaddlePntTransport

/-!
# Transport of the full-aperture antiscale energy

At the source-selected antiscale frequency

```text
t = π/log Y + π/(a (log Y)²)
```

the transverse Euler energy of the positive squared law is

```text
F(Y) = ∑_{p ≤ Y} p^{a-1} |1 + p^{it}|² = (π²/a³) (Y^a/(log Y)³) (1 + o(1)),
```

which is the exponential moment `∫_0^∞ e^{-av}(π/a - πv)² dv = π²/a³` of the logarithmic window
variable.  Writing `θ_p = t log p - π` the antiscale phase is exactly `(A - B v_p)/log Y` with
`A = π/a`, `B = π + π/(a log Y)` and `v_p = log Y - log p`, so the prime window law evaluates the
quadratic model, and the uniform bound `|2 - 2cos θ - θ²| ≤ 5θ⁴` makes the trigonometric
remainder `O(Y^a/(log Y)^5)`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Elementary bounds -/

/-- The quadratic model of `2 - 2cos` has a uniform quartic error. -/
theorem abs_two_sub_two_cos_sub_sq_le (θ : ℝ) : |2 - 2 * Real.cos θ - θ ^ 2| ≤ 5 * θ ^ 4 := by
  rcases le_total |θ| 1 with hsmall | hlarge
  · have h := Real.cos_bound hsmall
    have habs : |2 - 2 * Real.cos θ - θ ^ 2| = 2 * |Real.cos θ - (1 - θ ^ 2 / 2)| := by
      rw [← abs_neg, ← abs_two, ← abs_mul]
      congr 1
      ring
    have habs4 : |θ| ^ 4 = θ ^ 4 := by
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [habs]
    calc 2 * |Real.cos θ - (1 - θ ^ 2 / 2)| ≤ 2 * (|θ| ^ 4 * (5 / 96)) := by linarith
      _ = θ ^ 4 * (5 / 48) := by rw [habs4]; ring
      _ ≤ 5 * θ ^ 4 := by
          have h4 : (0 : ℝ) ≤ θ ^ 4 := by positivity
          linarith
  · have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hsq : (1 : ℝ) ≤ θ ^ 2 := by
      have h1 : (1 : ℝ) ≤ |θ| := hlarge
      nlinarith [abs_nonneg θ, sq_abs θ]
    have hq : θ ^ 2 ≤ θ ^ 4 := by nlinarith [sq_nonneg θ]
    have hbound : |2 - 2 * Real.cos θ - θ ^ 2| ≤ 4 + θ ^ 2 := by
      have h1 : |2 - 2 * Real.cos θ| ≤ 4 := by
        have := abs_sub_abs_le_abs_sub (2 : ℝ) (2 * Real.cos θ)
        calc |2 - 2 * Real.cos θ| ≤ |(2 : ℝ)| + |2 * Real.cos θ| := abs_sub _ _
          _ ≤ 2 + 2 * 1 := by
              rw [abs_two, abs_mul, abs_two]
              linarith
          _ = 4 := by norm_num
      calc |2 - 2 * Real.cos θ - θ ^ 2| ≤ |2 - 2 * Real.cos θ| + |θ ^ 2| := abs_sub _ _
        _ ≤ 4 + θ ^ 2 := by
            rw [abs_of_nonneg (sq_nonneg θ)]
            linarith
    nlinarith [hbound, hq, hsq]

/-- A quartic difference is dominated by the two quartic terms. -/
theorem sub_pow_four_le (x y : ℝ) : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg x, sq_nonneg y,
    sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x ^ 2 + y ^ 2)]

/-! ## The antiscale frequency and energy -/

/-- The source-selected antiscale frequency `t = π/log Y + π/(a (log Y)²)`. -/
def antiscaleFrequency (a Y : ℝ) : ℝ :=
  Real.pi / Real.log Y + Real.pi / (a * Real.log Y ^ 2)

/-- The transverse antiscale energy over the window `(2, Y]`. -/
def antiscaleEnergyIoc (a t Y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
    (if k.Prime then (k : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log k)) else 0)

/-- The transverse antiscale energy `∑_{p ≤ Y} p^(a-1) |1 + p^{it}|²`. -/
def antiscaleEnergy (a t Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log p))

/-- The transverse factor is the squared modulus of the Euler phase. -/
theorem two_add_two_cos_eq_normSq (φ : ℝ) :
    2 + 2 * Real.cos φ = ‖1 + Complex.exp (φ * Complex.I)‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (1 + Complex.exp (φ * Complex.I)).re = 1 + Real.cos φ := by
    rw [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
  have him : (1 + Complex.exp (φ * Complex.I)).im = Real.sin φ := by
    rw [Complex.add_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_add]
  rw [hre, him]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem antiscaleEnergy_eq_add {a t Y : ℝ} (hY : 2 ≤ Y) :
    antiscaleEnergy a t Y
      = (2 : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (t * Real.log 2)) + antiscaleEnergyIoc a t Y := by
  have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  rw [antiscaleEnergy, sum_primesLE_eq_add_sum_Ioc _ hfloor, antiscaleEnergyIoc]
  norm_num

/-! ## The quadratic model -/

/-- The quadratic model of the antiscale energy, an exact combination of window sums. -/
def antiscaleQuadratic (a Y : ℝ) : ℝ :=
  (1 / Real.log Y ^ 2) *
    ((Real.pi / a) ^ 2 * primeWindowSumNoLog a 0 Y
      - 2 * (Real.pi / a) * (Real.pi + Real.pi / (a * Real.log Y)) * primeWindowSumNoLog a 1 Y
      + (Real.pi + Real.pi / (a * Real.log Y)) ^ 2 * primeWindowSumNoLog a 2 Y)

/-- The antiscale phase is exactly the window affine form divided by `log Y`. -/
theorem antiscaleFrequency_mul_log_sub_pi {a Y : ℝ} (ha : a ≠ 0) (hY : Real.log Y ≠ 0) (x : ℝ) :
    antiscaleFrequency a Y * x - Real.pi
      = ((Real.pi / a)
          - (Real.pi + Real.pi / (a * Real.log Y)) * (Real.log Y - x)) / Real.log Y := by
  rw [antiscaleFrequency]
  field_simp
  ring

theorem antiscaleQuadratic_eq_sum {a Y : ℝ} (ha : a ≠ 0) (hY : Real.log Y ≠ 0) :
    antiscaleQuadratic a Y
      = ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
          (if k.Prime then (k : ℝ) ^ (a - 1) *
            (((Real.pi / a) - (Real.pi + Real.pi / (a * Real.log Y)) *
              (Real.log Y - Real.log k)) / Real.log Y) ^ 2 else 0) := by
  rw [antiscaleQuadratic, primeWindowSumNoLog, primeWindowSumNoLog, primeWindowSumNoLog,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp, if_pos hp, if_pos hp]
    field_simp
    ring
  · rw [if_neg hp, if_neg hp, if_neg hp, if_neg hp]
    ring

/-- **The trigonometric remainder of the antiscale energy.** -/
theorem abs_antiscaleEnergyIoc_sub_quadratic_le {a Y : ℝ} (ha0 : 0 < a) (hY : 2 ≤ Y)
    (hlogY : 1 ≤ Real.log Y) :
    |antiscaleEnergyIoc a (antiscaleFrequency a Y) Y - antiscaleQuadratic a Y|
      ≤ 40 / Real.log Y ^ 4 *
        ((Real.pi / a) ^ 4 * primeWindowSumNoLog a 0 Y
          + (Real.pi + Real.pi / (a * Real.log Y)) ^ 4 * primeWindowSumNoLog a 4 Y) := by
  have hane : a ≠ 0 := ne_of_gt ha0
  have hlogne : Real.log Y ≠ 0 := by linarith
  have hlog0 : (0 : ℝ) < Real.log Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  set A : ℝ := Real.pi / a with hA
  set B : ℝ := Real.pi + Real.pi / (a * Real.log Y) with hB
  have hApos : 0 < A := by
    rw [hA]
    positivity
  have hBpos : 0 < B := by
    rw [hB]
    have : (0 : ℝ) < Real.pi / (a * Real.log Y) := by positivity
    have := Real.pi_pos
    linarith
  -- the difference is a single sum
  have hdiff : antiscaleEnergyIoc a (antiscaleFrequency a Y) Y - antiscaleQuadratic a Y
      = ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
          (if k.Prime then (k : ℝ) ^ (a - 1) *
            ((2 - 2 * Real.cos ((A - B * (Real.log Y - Real.log k)) / Real.log Y))
              - ((A - B * (Real.log Y - Real.log k)) / Real.log Y) ^ 2) else 0) := by
    rw [antiscaleEnergyIoc, antiscaleQuadratic_eq_sum hane hlogne, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp, if_pos hp]
      have hphase := antiscaleFrequency_mul_log_sub_pi (a := a) (Y := Y) hane hlogne (Real.log k)
      have hcos : Real.cos (antiscaleFrequency a Y * Real.log k)
          = -Real.cos ((A - B * (Real.log Y - Real.log k)) / Real.log Y) := by
        have hsub : (A - B * (Real.log Y - Real.log k)) / Real.log Y
            = antiscaleFrequency a Y * Real.log k - Real.pi := by
          rw [hA, hB]
          exact hphase.symm
        rw [hsub, Real.cos_sub_pi, neg_neg]
      rw [hcos]
      ring
    · rw [if_neg hp, if_neg hp, if_neg hp]
      ring
  -- termwise bound
  have hterm : ∀ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
      |(if k.Prime then (k : ℝ) ^ (a - 1) *
        ((2 - 2 * Real.cos ((A - B * (Real.log Y - Real.log k)) / Real.log Y))
          - ((A - B * (Real.log Y - Real.log k)) / Real.log Y) ^ 2) else 0)|
        ≤ 40 / Real.log Y ^ 4 *
          (if k.Prime then (k : ℝ) ^ (a - 1) *
            (A ^ 4 + B ^ 4 * (Real.log Y - Real.log k) ^ 4) else 0) := by
    intro k hk
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      rw [Finset.mem_Ioc] at hk
      have hk0 : (0 : ℝ) < (k : ℝ) := by
        have : (0 : ℕ) < k := by omega
        exact_mod_cast this
      have hrp : (0 : ℝ) ≤ (k : ℝ) ^ (a - 1) := Real.rpow_nonneg hk0.le _
      set θ : ℝ := (A - B * (Real.log Y - Real.log k)) / Real.log Y with hθ
      have hquart : θ ^ 4 ≤ 8 * (A ^ 4 + B ^ 4 * (Real.log Y - Real.log k) ^ 4) /
          Real.log Y ^ 4 := by
        have hnum : (A - B * (Real.log Y - Real.log k)) ^ 4
            ≤ 8 * (A ^ 4 + (B * (Real.log Y - Real.log k)) ^ 4) :=
          sub_pow_four_le A (B * (Real.log Y - Real.log k))
        have hpow : θ ^ 4 = (A - B * (Real.log Y - Real.log k)) ^ 4 / Real.log Y ^ 4 := by
          rw [hθ, div_pow]
        rw [hpow]
        have hden : (0 : ℝ) < Real.log Y ^ 4 := by positivity
        rw [div_le_div_iff₀ hden hden]
        have hexp : (B * (Real.log Y - Real.log k)) ^ 4
            = B ^ 4 * (Real.log Y - Real.log k) ^ 4 := by ring
        nlinarith [hnum, hexp, hden]
      have hbase := abs_two_sub_two_cos_sub_sq_le θ
      calc |(k : ℝ) ^ (a - 1) * ((2 - 2 * Real.cos θ) - θ ^ 2)|
          = (k : ℝ) ^ (a - 1) * |(2 - 2 * Real.cos θ) - θ ^ 2| := by
            rw [abs_mul, abs_of_nonneg hrp]
        _ ≤ (k : ℝ) ^ (a - 1) * (5 * θ ^ 4) := by
            refine mul_le_mul_of_nonneg_left ?_ hrp
            have : |2 - 2 * Real.cos θ - θ ^ 2| = |(2 - 2 * Real.cos θ) - θ ^ 2| := by ring_nf
            linarith [hbase, this]
        _ ≤ (k : ℝ) ^ (a - 1) *
            (5 * (8 * (A ^ 4 + B ^ 4 * (Real.log Y - Real.log k) ^ 4) / Real.log Y ^ 4)) := by
            refine mul_le_mul_of_nonneg_left ?_ hrp
            linarith [hquart]
        _ = 40 / Real.log Y ^ 4 *
            ((k : ℝ) ^ (a - 1) * (A ^ 4 + B ^ 4 * (Real.log Y - Real.log k) ^ 4)) := by
            ring
    · rw [if_neg hp, if_neg hp]
      simp
  -- assemble
  have hrhs : 40 / Real.log Y ^ 4 *
      (A ^ 4 * primeWindowSumNoLog a 0 Y + B ^ 4 * primeWindowSumNoLog a 4 Y)
      = ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊, 40 / Real.log Y ^ 4 *
        (if k.Prime then (k : ℝ) ^ (a - 1) *
          (A ^ 4 + B ^ 4 * (Real.log Y - Real.log k) ^ 4) else 0) := by
    rw [primeWindowSumNoLog, primeWindowSumNoLog, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp, if_pos hp]
      ring
    · rw [if_neg hp, if_neg hp, if_neg hp]
      ring
  rw [hdiff, hrhs]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)

/-! ## The transported asymptotic -/

/-- **Full-aperture antiscale energy.**  At the source-selected antiscale frequency the transverse
Euler energy is `(π²/a³) Y^a/(log Y)³ (1 + o(1))`. -/
theorem tendsto_antiscaleEnergy {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun Y : ℝ =>
      antiscaleEnergy a (antiscaleFrequency a Y) Y * Real.log Y ^ 3 / Y ^ a) atTop
      (nhds (Real.pi ^ 2 / a ^ 3)) := by
  have hane : a ≠ 0 := ne_of_gt ha0
  -- window limits
  have hN0 := tendsto_logY_mul_primeWindowSumNoLog ha0 0
  have hN1 := tendsto_logY_mul_primeWindowSumNoLog ha0 1
  have hN2 := tendsto_logY_mul_primeWindowSumNoLog ha0 2
  have hN4 := tendsto_logY_mul_primeWindowSumNoLog ha0 4
  have hBlim : Tendsto (fun Y : ℝ => Real.pi + Real.pi / (a * Real.log Y)) atTop
      (nhds Real.pi) := by
    have h : Tendsto (fun Y : ℝ => Real.pi / (a * Real.log Y)) atTop (nhds 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact Filter.Tendsto.const_mul_atTop ha0 Real.tendsto_log_atTop
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi) atTop (nhds Real.pi)).add h
    rwa [add_zero] at h2
  -- the quadratic model converges to the exponential moment
  have hquad : Tendsto (fun Y : ℝ => antiscaleQuadratic a Y * Real.log Y ^ 3 / Y ^ a) atTop
      (nhds (Real.pi ^ 2 / a ^ 3)) := by
    have h0 := hN0.const_mul ((Real.pi / a) ^ 2)
    have h1 := ((hBlim.const_mul (2 * (Real.pi / a))).mul hN1)
    have h2 := ((hBlim.mul hBlim).mul hN2)
    have hsum := (h0.sub h1).add h2
    have hval : (Real.pi / a) ^ 2 * ((Nat.factorial 0 : ℝ) / a ^ (0 + 1))
        - 2 * (Real.pi / a) * Real.pi * ((Nat.factorial 1 : ℝ) / a ^ (1 + 1))
        + Real.pi * Real.pi * ((Nat.factorial 2 : ℝ) / a ^ (2 + 1))
        = Real.pi ^ 2 / a ^ 3 := by
      simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one,
        Nat.cast_ofNat, zero_add, pow_one]
      field_simp
      ring
    rw [hval] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog0 : (0 : ℝ) < Real.log Y := Real.log_pos (by linarith)
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    rw [antiscaleQuadratic]
    field_simp
  -- the trigonometric remainder vanishes
  have hrem : Tendsto (fun Y : ℝ =>
      (antiscaleEnergyIoc a (antiscaleFrequency a Y) Y - antiscaleQuadratic a Y)
        * Real.log Y ^ 3 / Y ^ a) atTop (nhds 0) := by
    have hmaj : Tendsto (fun Y : ℝ =>
        40 / Real.log Y ^ 2 *
          ((Real.pi / a) ^ 4 * (Real.log Y * primeWindowSumNoLog a 0 Y / Y ^ a)
            + (Real.pi + Real.pi / (a * Real.log Y)) ^ 4 *
              (Real.log Y * primeWindowSumNoLog a 4 Y / Y ^ a))) atTop (nhds 0) := by
      have hL2 : Tendsto (fun Y : ℝ => Real.log Y ^ 2) atTop atTop := by
        have h := Filter.Tendsto.atTop_mul_atTop₀ Real.tendsto_log_atTop Real.tendsto_log_atTop
        refine h.congr fun Y => ?_
        ring
      have hinv : Tendsto (fun Y : ℝ => 40 / Real.log Y ^ 2) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hL2
      have hb4 : Tendsto (fun Y : ℝ => (Real.pi + Real.pi / (a * Real.log Y)) ^ 4) atTop
          (nhds (Real.pi ^ 4)) := hBlim.pow 4
      have hsum := (hN0.const_mul ((Real.pi / a) ^ 4)).add (hb4.mul hN4)
      have h := hinv.mul hsum
      rwa [zero_mul] at h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with Y hY
    have hY2 : (2 : ℝ) ≤ Y := by linarith
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log Y := by
      have h16 : Real.log 16 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
      have : (1 : ℝ) < Real.log 16 := by
        have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hlog16 : Real.log 16 = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
        rw [hlog16]
        linarith
      linarith
    have hlog0 : (0 : ℝ) < Real.log Y := by linarith
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    have hbound := abs_antiscaleEnergyIoc_sub_quadratic_le ha0 hY2 hlog1
    have hexpand : 40 / Real.log Y ^ 4 *
        ((Real.pi / a) ^ 4 * primeWindowSumNoLog a 0 Y
          + (Real.pi + Real.pi / (a * Real.log Y)) ^ 4 * primeWindowSumNoLog a 4 Y)
        * Real.log Y ^ 3 / Y ^ a
        = 40 / Real.log Y ^ 2 *
          ((Real.pi / a) ^ 4 * (Real.log Y * primeWindowSumNoLog a 0 Y / Y ^ a)
            + (Real.pi + Real.pi / (a * Real.log Y)) ^ 4 *
              (Real.log Y * primeWindowSumNoLog a 4 Y / Y ^ a)) := by
      field_simp
    rw [Real.norm_eq_abs]
    calc |(antiscaleEnergyIoc a (antiscaleFrequency a Y) Y - antiscaleQuadratic a Y)
            * Real.log Y ^ 3 / Y ^ a|
        = |antiscaleEnergyIoc a (antiscaleFrequency a Y) Y - antiscaleQuadratic a Y|
            * Real.log Y ^ 3 / Y ^ a := by
          rw [abs_div, abs_mul, abs_of_pos hYa, abs_of_pos (by positivity : (0:ℝ) < Real.log Y ^ 3)]
      _ ≤ 40 / Real.log Y ^ 4 *
            ((Real.pi / a) ^ 4 * primeWindowSumNoLog a 0 Y
              + (Real.pi + Real.pi / (a * Real.log Y)) ^ 4 * primeWindowSumNoLog a 4 Y)
            * Real.log Y ^ 3 / Y ^ a := by
          apply div_le_div_of_nonneg_right _ hYa.le
          exact mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = 40 / Real.log Y ^ 2 *
            ((Real.pi / a) ^ 4 * (Real.log Y * primeWindowSumNoLog a 0 Y / Y ^ a)
              + (Real.pi + Real.pi / (a * Real.log Y)) ^ 4 *
                (Real.log Y * primeWindowSumNoLog a 4 Y / Y ^ a)) := hexpand
  -- the boundary prime
  have hbdry : Tendsto (fun Y : ℝ =>
      (2 : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (antiscaleFrequency a Y * Real.log 2))
        * Real.log Y ^ 3 / Y ^ a) atTop (nhds 0) := by
    have hmaj : Tendsto (fun Y : ℝ => 4 * (2 : ℝ) ^ (a - 1) * (Real.log Y ^ 3 / Y ^ a)) atTop
        (nhds 0) := by
      have h := (HTGeometry.tendsto_logPow_div_rpow ha0 3).const_mul (4 * (2 : ℝ) ^ (a - 1))
      rwa [mul_zero] at h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
    have hY0 : (0 : ℝ) < Y := by linarith
    have hlog0 : (0 : ℝ) < Real.log Y := Real.log_pos (by linarith)
    have hYa : (0 : ℝ) < Y ^ a := Real.rpow_pos_of_pos hY0 a
    have hcos : |2 + 2 * Real.cos (antiscaleFrequency a Y * Real.log 2)| ≤ 4 := by
      have h := Real.neg_one_le_cos (antiscaleFrequency a Y * Real.log 2)
      have h2 := Real.cos_le_one (antiscaleFrequency a Y * Real.log 2)
      rw [abs_le]
      constructor <;> linarith
    have h2a : (0 : ℝ) < (2 : ℝ) ^ (a - 1) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.norm_eq_abs]
    calc |(2 : ℝ) ^ (a - 1) * (2 + 2 * Real.cos (antiscaleFrequency a Y * Real.log 2))
            * Real.log Y ^ 3 / Y ^ a|
        = (2 : ℝ) ^ (a - 1) * |2 + 2 * Real.cos (antiscaleFrequency a Y * Real.log 2)|
            * Real.log Y ^ 3 / Y ^ a := by
          rw [abs_div, abs_mul, abs_mul, abs_of_pos hYa, abs_of_pos h2a,
            abs_of_pos (by positivity : (0:ℝ) < Real.log Y ^ 3)]
      _ ≤ (2 : ℝ) ^ (a - 1) * 4 * Real.log Y ^ 3 / Y ^ a := by
          apply div_le_div_of_nonneg_right _ hYa.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hcos h2a.le
      _ = 4 * (2 : ℝ) ^ (a - 1) * (Real.log Y ^ 3 / Y ^ a) := by ring
  -- assemble
  have hsum := (hbdry.add hrem).add hquad
  rw [zero_add, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  rw [antiscaleEnergy_eq_add hY]
  ring

/-! ## The archimedean factor -/

/-- The antiscale frequency tends to zero. -/
theorem tendsto_antiscaleFrequency {a : ℝ} (ha0 : 0 < a) :
    Tendsto (fun Y : ℝ => antiscaleFrequency a Y) atTop (nhds 0) := by
  have h1 : Tendsto (fun Y : ℝ => Real.pi / Real.log Y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hL2 : Tendsto (fun Y : ℝ => Real.log Y ^ 2) atTop atTop := by
    have h := Filter.Tendsto.atTop_mul_atTop₀ Real.tendsto_log_atTop Real.tendsto_log_atTop
    refine h.congr fun Y => ?_
    ring
  have haL2 : Tendsto (fun Y : ℝ => a * Real.log Y ^ 2) atTop atTop := hL2.const_mul_atTop ha0
  have h2 : Tendsto (fun Y : ℝ => Real.pi / (a * Real.log Y ^ 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop haL2
  have h := h1.add h2
  rw [add_zero] at h
  exact h

/-- **Gamma completion does not attenuate the escape.**  The antiscale frequency tends to zero, so
the archimedean factor converges to its real value. -/
theorem tendsto_gamma_normSq_antiscale {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun Y : ℝ =>
      ‖Complex.Gamma (((1 - a : ℝ) : ℂ) + ((antiscaleFrequency a Y : ℝ) : ℂ) * Complex.I)‖ ^ 2)
      atTop (nhds (‖Complex.Gamma (((1 - a : ℝ) : ℂ))‖ ^ 2)) := by
  have hne : ∀ m : ℕ, ((1 - a : ℝ) : ℂ) ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ : ContinuousAt Complex.Gamma ((1 - a : ℝ) : ℂ) :=
    (Complex.differentiableAt_Gamma _ hne).continuousAt
  have hfreq := tendsto_antiscaleFrequency ha0
  have harg : Tendsto
      (fun Y : ℝ => ((1 - a : ℝ) : ℂ) + ((antiscaleFrequency a Y : ℝ) : ℂ) * Complex.I) atTop
      (nhds (((1 - a : ℝ) : ℂ))) := by
    have hc : Tendsto (fun Y : ℝ => ((antiscaleFrequency a Y : ℝ) : ℂ)) atTop (nhds 0) := by
      have hof := Complex.continuous_ofReal.tendsto (0 : ℝ)
      have hcomp := hof.comp hfreq
      simpa [Function.comp_def] using hcomp
    have h2 : Tendsto
        (fun Y : ℝ => ((1 - a : ℝ) : ℂ) + ((antiscaleFrequency a Y : ℝ) : ℂ) * Complex.I) atTop
        (nhds (((1 - a : ℝ) : ℂ) + 0 * Complex.I)) :=
      tendsto_const_nhds.add (hc.mul_const Complex.I)
    simpa using h2
  have hgamma := hΓ.tendsto.comp harg
  exact (hgamma.norm).pow 2

end

end RHTower
