import GaloisForLFunctions.RHTower.Sieve.ExpBaseSchedule
import GaloisForLFunctions.RHTower.Sieve.ExceptionalMeasureLimit
import GaloisForLFunctions.RHTower.Sieve.LadderBlockPrimeCount

/-!
# The exceptional measure at the two-range schedule

Instantiating `Sieve/ExceptionalMeasureLimit.measureReal_annulusLarge_le_growing` at the low ladder
with an exponential bottom.  Every block sits between `exp((log x)^a)` and `h = exp((log x)^β)`, so

```text
   #B_j ≥ R_j·η/(4 log R_j)  (the prime number theorem with error term) ,
   g_j  = log(#B_j·θ²/k) ≥ log R_j − (c + 2A + β + 1 − a)·log log x − log 12 ≥ (log x)^a/2 ,
   n_j  = log NA_j ≤ log R_j + log 2 ,   so  g_j − n_j ≥ −(c + 2A + β + 2)·log log x .
```

Both estimates are uniform in `j`; the first uses only the *bottom* of the ladder and the second
only the *ratio* `NA_j/#B_j ≍ log R_j/η`, which is polylogarithmic at every step.  With
`k = ⌈2(log x)^{1−a}⌉` the trivial term drops below `W/x` and the diagonal one costs `x^{o(1)}`.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory

noncomputable section

/-- The moment order: it grows like `(log x)^{1−a}`. -/
def momentOrder (a x : ℝ) : ℕ := ⌈2 * (Real.log x) ^ (1 - a)⌉₊

theorem one_le_momentOrder {a x : ℝ} (hx : 1 < x) : 1 ≤ momentOrder a x := by
  rw [momentOrder]
  refine Nat.one_le_ceil_iff.2 ?_
  have := Real.rpow_pos_of_pos (Real.log_pos hx) (1 - a)
  linarith

theorem momentOrder_ge {a x : ℝ} : 2 * (Real.log x) ^ (1 - a) ≤ ((momentOrder a x : ℕ) : ℝ) :=
  Nat.le_ceil _

theorem momentOrder_le {a x : ℝ} (_hx : 1 < x) (hbig : 1 ≤ (Real.log x) ^ (1 - a)) :
    ((momentOrder a x : ℕ) : ℝ) ≤ 3 * (Real.log x) ^ (1 - a) := by
  rw [momentOrder]
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * (Real.log x) ^ (1 - a) by linarith)
  linarith

set_option maxHeartbeats 4000000 in
/-- **The two exponents of the moment bound, uniformly over the ladder.** -/
theorem expBlock_moment_bounds {a c A β : ℝ} (ha : 0 < a) (hab : a < β)
    (ha1 : a < 1) (hc : 0 < c) (_hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (expSteps a c β x),
      0 < ((geomBlock (primesRange (highBase a x) (expTop a c β x))
            ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
        ∧ (Real.log x) ^ a / 2
            ≤ Real.log (((geomBlock (primesRange (highBase a x) (expTop a c β x))
                ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
              * lowTheta A x ^ 2 / ((momentOrder a x : ℕ) : ℝ))
        ∧ Real.log ((⌊((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (j + 1)⌋₊ : ℕ) : ℝ)
            ≤ Real.log 2 + (Real.log x) ^ β
        ∧ -((c + 2 * A + β + 2) * Real.log (Real.log x))
            ≤ Real.log (((geomBlock (primesRange (highBase a x) (expTop a c β x))
                ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
              * lowTheta A x ^ 2 / ((momentOrder a x : ℕ) : ℝ))
              - Real.log ((⌊((highBase a x : ℕ) : ℝ)
                  * (1 + lowEta c x) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by
  obtain ⟨C, c₀, hc₀, hC, hcnt⟩ := exists_card_windowPrimes_ge
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 hcnt
  -- the two decays that make the prime count applicable
  have hd1 : Tendsto (fun x : ℝ =>
      (Real.log x) ^ c * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a / 2))))) atTop (𝓝 0) := by
    have h := tendsto_logRpow_mul_expSaving (d := a / 2) (s := c₀) (by linarith) hc₀ c
    have := h.const_mul (16 * C)
    rw [show ((16 : ℝ) * C * 0) = 0 by ring] at this
    refine this.congr fun x => ?_
    ring
  have hd2 : Tendsto (fun x : ℝ =>
      (Real.log x) ^ c * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a)))) atTop (𝓝 0) := by
    have h := tendsto_logRpow_mul_expSaving (d := a) (s := (1 : ℝ) / 4) ha (by norm_num) c
    have := h.const_mul (96 : ℝ)
    rw [show ((96 : ℝ) * 0) = 0 by ring] at this
    refine this.congr fun x => ?_
    ring
  have hzero := tendsto_lowEta (c := c) hc
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  have hpow1a : Tendsto (fun x : ℝ => (Real.log x) ^ (1 - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  have hcarda := tendsto_cardLength (β := a) ha
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  -- the slack that absorbs every logarithmic correction
  have hslack : Tendsto (fun x : ℝ =>
      (Real.log x) ^ (-a) * ((c + 2 * A + β + 3 - a) * Real.log (Real.log x) + 12))
      atTop (𝓝 0) := by
    have h1 := tendsto_logMonomial (e := -a) (by linarith) 1
    have h2 := tendsto_rpow_log_of_neg (c := -a) (by linarith)
    have h := (h1.const_mul (c + 2 * A + β + 3 - a)).add (h2.const_mul (12 : ℝ))
    rw [show ((c + 2 * A + β + 3 - a) * 0 + 12 * 0) = 0 by ring] at h
    refine h.congr fun x => ?_
    rw [pow_one]
    ring
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hd1,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hd2,
    hcarda.eventually_ge_atTop (max y₀ (Real.exp 2)),
    hpowa.eventually_ge_atTop (2 : ℝ),
    hpow1a.eventually_ge_atTop (1 : ℝ),
    hll.eventually_ge_atTop (6 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hslack,
    expTop_le_cardLength (a := a) (c := c) (β := β) ha hab hc,
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc]
    with x hx1 hη1 hdec1 hdec2 hbigcard hpa2 hp1a1 hu6 hsl htop hlow2
  intro j hj
  have hjL : j + 1 ≤ expSteps a c β x := Finset.mem_range.1 hj
  set u : ℝ := Real.log (Real.log x) with hudef
  set R : ℝ := ((highBase a x : ℕ) : ℝ) with hRdef
  set η : ℝ := lowEta c x with hηdef
  set k : ℝ := ((momentOrder a x : ℕ) : ℝ) with hkdef
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη0 : (0 : ℝ) < η := lowEta_pos hx1
  have hRlo : cardLength a x ≤ R := (highBase_bounds (a := a) hx1).1
  have hRj0' : (0 : ℝ) < R := lt_of_lt_of_le (cardLength_pos a x) hRlo
  have hRj0 : (0 : ℝ) < R * (1 + η) ^ j := by
    have : (0 : ℝ) < R := lt_of_lt_of_le (cardLength_pos a x) hRlo
    positivity
  have hpowj : (1 : ℝ) ≤ (1 + η) ^ j := one_le_pow₀ (by linarith)
  have hRjlo : cardLength a x ≤ R * (1 + η) ^ j := by nlinarith [hRlo, hpowj, cardLength_pos a x]
  have hRjy₀ : max y₀ (Real.exp 2) ≤ R * (1 + η) ^ j := le_trans hbigcard hRjlo
  have hlogRjlo : (Real.log x) ^ a ≤ Real.log (R * (1 + η) ^ j) := by
    have := Real.log_le_log (cardLength_pos a x) hRjlo
    rwa [log_cardLength] at this
  have hlogRj0 : (0 : ℝ) < Real.log (R * (1 + η) ^ j) := by linarith [hpa2, hlogRjlo]
  -- the upper end of the ladder
  have hmono : (1 + η) ^ (j + 1) ≤ (1 + η) ^ (expSteps a c β x) :=
    pow_le_pow_right₀ (by linarith) hjL
  have hRj1hi : R * (1 + η) ^ (j + 1) ≤ cardLength β x :=
    le_trans (mul_le_mul_of_nonneg_left hmono (by linarith [hRj0])) htop
  have hRjhi : R * (1 + η) ^ j ≤ cardLength β x := by
    have h1 : (1 + η) ^ j ≤ (1 + η) ^ (j + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    nlinarith [h1, hRj1hi, hRj0]
  have hlogRjhi : Real.log (R * (1 + η) ^ j) ≤ (Real.log x) ^ β := by
    have := Real.log_le_log hRj0 hRjhi
    rwa [log_cardLength] at this
  -- the prime count applies at every step
  have hsqrtlo : (Real.log x) ^ (a / 2) ≤ Real.sqrt (Real.log (R * (1 + η) ^ j)) := by
    have h1 : Real.sqrt ((Real.log x) ^ a) ≤ Real.sqrt (Real.log (R * (1 + η) ^ j)) :=
      Real.sqrt_le_sqrt hlogRjlo
    have h2 : Real.sqrt ((Real.log x) ^ a) = (Real.log x) ^ (a / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlogx.le]
      congr 1
      ring
    linarith [h1, h2]
  have hηinv : η * (Real.log x) ^ c = 1 := by
    rw [hηdef, lowEta, ← Real.rpow_add hlogx]
    simp
  have hηpow : (0 : ℝ) < (Real.log x) ^ c := Real.rpow_pos_of_pos hlogx c
  have hterm1 : 16 * C * Real.exp (-c₀ * Real.sqrt (Real.log (R * (1 + η) ^ j))) ≤ η / 2 := by
    have hmono : Real.exp (-c₀ * Real.sqrt (Real.log (R * (1 + η) ^ j)))
        ≤ Real.exp (-(c₀ * (Real.log x) ^ (a / 2))) :=
      Real.exp_le_exp.2 (by nlinarith [hsqrtlo, hc₀])
    have hstep : 16 * C * Real.exp (-c₀ * Real.sqrt (Real.log (R * (1 + η) ^ j)))
        ≤ 16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a / 2))) := by
      nlinarith [hmono, hC, Real.exp_pos (-(c₀ * (Real.log x) ^ (a / 2)))]
    have hmul := mul_le_mul_of_nonneg_left hdec1 (le_of_lt hη0)
    have hid : η * ((Real.log x) ^ c * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a / 2)))))
        = 16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a / 2))) := by
      rw [show η * ((Real.log x) ^ c * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a / 2)))))
          = (η * (Real.log x) ^ c) * (16 * C * Real.exp (-(c₀ * (Real.log x) ^ (a / 2)))) by ring,
        hηinv, one_mul]
    rw [hid] at hmul
    linarith [hstep, hmul]
  have hq0 : (0 : ℝ) < (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hRj0 _
  have hlogq : Real.log (R * (1 + η) ^ j) ≤ 4 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div hRj0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    have hid : (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4)
        = 4 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by ring
    linarith [h, hid]
  have hexpq : Real.exp ((Real.log x) ^ a / 4) ≤ (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
    have h1 : (cardLength a x) ^ ((1 : ℝ) / 4) ≤ (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (cardLength_pos a x).le hRjlo (by norm_num)
    have h2 : (cardLength a x) ^ ((1 : ℝ) / 4) = Real.exp ((Real.log x) ^ a / 4) := by
      rw [cardLength, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    linarith [h1, h2]
  have hsq : Real.sqrt (R * (1 + η) ^ j)
      = (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hRj0, Real.sqrt_eq_rpow]
    norm_num
  have hterm2 : 24 * Real.log (R * (1 + η) ^ j) / Real.sqrt (R * (1 + η) ^ j) ≤ η / 2 := by
    have hstep : 24 * Real.log (R * (1 + η) ^ j) / Real.sqrt (R * (1 + η) ^ j)
        ≤ 96 * Real.exp (-(1 / 4 * (Real.log x) ^ a)) := by
      rw [hsq]
      have hA : 24 * Real.log (R * (1 + η) ^ j) ≤ 96 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by
        linarith [hlogq]
      calc 24 * Real.log (R * (1 + η) ^ j)
              / ((R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4))
          ≤ 96 * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4)
              / ((R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) * (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4)) :=
            div_le_div_of_nonneg_right hA (by positivity)
        _ = 96 / (R * (1 + η) ^ j) ^ ((1 : ℝ) / 4) := by field_simp
        _ ≤ 96 / Real.exp ((Real.log x) ^ a / 4) :=
            div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hexpq
        _ = 96 * Real.exp (-(1 / 4 * (Real.log x) ^ a)) := by
            rw [show -(1 / 4 * (Real.log x) ^ a) = -((Real.log x) ^ a / 4) by ring,
              Real.exp_neg]
            field_simp
    have hmul := mul_le_mul_of_nonneg_left hdec2 (le_of_lt hη0)
    have hid : η * ((Real.log x) ^ c * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a))))
        = 96 * Real.exp (-(1 / 4 * (Real.log x) ^ a)) := by
      rw [show η * ((Real.log x) ^ c * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a))))
          = (η * (Real.log x) ^ c) * (96 * Real.exp (-(1 / 4 * (Real.log x) ^ a))) by ring,
        hηinv, one_mul]
    rw [hid] at hmul
    linarith [hstep, hmul]
  have hcountj := card_geomBlock_primesRange_ge (C := C) (c := c₀) (y₀ := y₀) hy₀
    (z₀ := highBase a x) (L := expSteps a c β x) (j := j) (R := R) (η := η)
    rfl hRj0' hη0 hη1 hjL (le_trans (le_max_left _ _) hRjy₀) (by linarith [hterm1, hterm2])
  -- the block is large
  set m : ℝ := ((geomBlock (primesRange (highBase a x) (expTop a c β x)) R (1 + η) j).card : ℝ)
    with hmdef
  have hmlo : R * (1 + η) ^ j * η / (4 * Real.log (R * (1 + η) ^ j)) ≤ m := hcountj
  have hmpos : (0 : ℝ) < R * (1 + η) ^ j * η / (4 * Real.log (R * (1 + η) ^ j)) := by positivity
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hmpos hmlo
  -- the logarithms
  have hθ0 : (0 : ℝ) < lowTheta A x := lowTheta_pos hx1
  have hk0 : (0 : ℝ) < k := by
    have := one_le_momentOrder (a := a) hx1
    have : (1 : ℝ) ≤ k := by rw [hkdef]; exact_mod_cast this
    linarith
  have hlogm : Real.log (R * (1 + η) ^ j) + (-c) * u - Real.log 4
      - Real.log (Real.log (R * (1 + η) ^ j)) ≤ Real.log m := by
    have hstep := Real.log_le_log hmpos hmlo
    have hid : Real.log (R * (1 + η) ^ j * η / (4 * Real.log (R * (1 + η) ^ j)))
        = Real.log (R * (1 + η) ^ j) + (-c) * u - Real.log 4
          - Real.log (Real.log (R * (1 + η) ^ j)) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (ne_of_gt hRj0) (ne_of_gt hη0),
        Real.log_mul (by norm_num) (ne_of_gt hlogRj0), hηdef, lowEta, Real.log_rpow hlogx]
      ring
    linarith [hstep, hid]
  have hlogθ : Real.log (lowTheta A x ^ 2) = (-(2 * A)) * u := by
    rw [Real.log_pow, lowTheta, Real.log_rpow hlogx]
    push_cast
    ring
  have hlogk : Real.log k ≤ Real.log 3 + (1 - a) * u := by
    have hkle : k ≤ 3 * (Real.log x) ^ (1 - a) := by
      rw [hkdef]
      exact momentOrder_le hx1 hp1a1
    have hstep := Real.log_le_log hk0 hkle
    have hid : Real.log (3 * (Real.log x) ^ (1 - a)) = Real.log 3 + (1 - a) * u := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hlogx _)),
        Real.log_rpow hlogx]
    linarith [hstep, hid]
  have hloglogRj : Real.log (Real.log (R * (1 + η) ^ j)) ≤ β * u := by
    have hstep := Real.log_le_log hlogRj0 hlogRjhi
    rwa [Real.log_rpow hlogx] at hstep
  have hMj : Real.log (m * lowTheta A x ^ 2 / k)
      = Real.log m + Real.log (lowTheta A x ^ 2) - Real.log k := by
    rw [Real.log_div (by positivity) (ne_of_gt hk0),
      Real.log_mul (ne_of_gt hm0) (by positivity)]
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hMjlo : Real.log (R * (1 + η) ^ j) - (c + 2 * A + β + 1 - a) * u - 5
      ≤ Real.log (m * lowTheta A x ^ 2 / k) := by
    rw [hMj, hlogθ]
    linarith [hlogm, hlogk, hloglogRj, hlog4, hlog3]
  -- the ladder top
  have hNAle : ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ R * (1 + η) ^ (j + 1) :=
    Nat.floor_le (by positivity)
  have hNA2 : (2 : ℝ) ≤ ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by
    have hR2 : (2 : ℝ) ≤ R := by
      rw [hRdef]
      exact_mod_cast hlow2.1
    have hpj : (1 : ℝ) ≤ (1 + η) ^ (j + 1) := one_le_pow₀ (by linarith)
    have : (2 : ℕ) ≤ ⌊R * (1 + η) ^ (j + 1)⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      nlinarith [hR2, hpj]
    exact_mod_cast this
  have hNA0 : (0 : ℝ) < ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by linarith
  have hlogNAhi : Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ Real.log 2 + (Real.log x) ^ β := by
    have hstep := Real.log_le_log hNA0 (le_trans hNAle hRj1hi)
    rw [log_cardLength] at hstep
    have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hlogNAj : Real.log ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ)
      ≤ Real.log (R * (1 + η) ^ j) + 1 := by
    have hid : R * (1 + η) ^ (j + 1) = R * (1 + η) ^ j * (1 + η) := by ring
    have hNAle2 : ((⌊R * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) ≤ R * (1 + η) ^ j * (1 + η) := by
      rw [← hid]
      exact hNAle
    have hstep := Real.log_le_log hNA0 hNAle2
    rw [Real.log_mul (ne_of_gt hRj0) (by linarith)] at hstep
    have hlogr : Real.log (1 + η) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + η by linarith)
      linarith
    linarith
  -- the two conclusions
  have hsl' : (c + 2 * A + β + 3 - a) * u + 12 ≤ (Real.log x) ^ a / 2 := by
    have hpa0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have hinv : (Real.log x) ^ (-a) * (Real.log x) ^ a = 1 := by
      rw [← Real.rpow_add hlogx]
      simp
    have hmul := mul_le_mul_of_nonneg_right hsl hpa0.le
    have hid : (Real.log x) ^ (-a) * ((c + 2 * A + β + 3 - a) * u + 12) * (Real.log x) ^ a
        = ((Real.log x) ^ (-a) * (Real.log x) ^ a) * ((c + 2 * A + β + 3 - a) * u + 12) := by ring
    rw [hid, hinv, one_mul] at hmul
    linarith [hmul]
  refine ⟨hm0, ?_, hlogNAhi, ?_⟩
  · linarith [hMjlo, hlogRjlo, hsl']
  · linarith [hMjlo, hlogNAj, hu6, mul_nonneg ha.le (show (0 : ℝ) ≤ u by linarith)]

/-- **The exceptional half of the annulus at the two-range schedule.**  The bound is
`L·(2W/x + x^{o(1)})`: the trivial term is killed by the growing moment order and the diagonal one
costs only `exp(k·D·log log x)`. -/
theorem measureReal_annulusLarge_schedule {a c A β : ℝ} (ha : 0 < a) (hab : a < β) (hβ1 : β < 1)
    (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, ∀ w₀ : ℝ,
      volume.real (annulusLarge
          (allBlocksSmall (primesRange (highBase a x) (expTop a c β x))
            ((highBase a x : ℕ) : ℝ) (lowEta c x) (expSteps a c β x)
            (fun j => ((geomBlock (primesRange (highBase a x) (expTop a c β x))
                ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ) * lowTheta A x)
            (twoRangeTop β x)) (twoRangeTop β x) w₀)
        ≤ ((expSteps a c β x : ℕ) : ℝ)
          * (2 * twoRangeTop β x / x
            + 2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + (Real.log x) ^ β))
              * Real.exp (((momentOrder a x : ℕ) : ℝ)
                  * ((c + 2 * A + β + 2) * Real.log (Real.log x)))) := by
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    expBlock_moment_bounds (a := a) (c := c) (A := A) (β := β) ha hab (by linarith) hc hA,
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc,
    one_le_twoRangeCut (β := β) (by linarith) hβ1,
    hll.eventually_ge_atTop (0 : ℝ)] with x hx1 hblock hlow2 hcut1 hu0
  intro w₀
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx1
  have hθ0 : (0 : ℝ) < lowTheta A x := lowTheta_pos hx1
  have hR2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast hlow2.1
  have hR0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) ≤ twoRangeTop β x := by
    rw [twoRangeTop]
    nlinarith [hcut1, hu0]
  have hNA : ∀ j ∈ Finset.range (expSteps a c β x),
      1 ≤ ⌊((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (j + 1)⌋₊ := by
    intro j _
    refine Nat.le_floor ?_
    have hpj : (1 : ℝ) ≤ (1 + lowEta c x) ^ (j + 1) := one_le_pow₀ (by linarith)
    push_cast
    nlinarith [hR2, hpj]
  exact measureReal_annulusLarge_le_growing (P := primesRange (highBase a x) (expTop a c β x))
    (R := ((highBase a x : ℕ) : ℝ)) (η := lowEta c x) (θ := lowTheta A x)
    (W := twoRangeTop β x) (w₀ := w₀) (nmax := Real.log 2 + (Real.log x) ^ β)
    (D := c + 2 * A + β + 2) (a₀ := a) (L := expSteps a c β x) (k := momentOrder a x)
    hR0 hη0.le (one_le_momentOrder hx1) hW0 hθ0
    (by
      have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h2 : (0 : ℝ) ≤ (Real.log x) ^ β := Real.rpow_nonneg hlogx.le β
      linarith)
    hx1 (by linarith) hu0
    (fun p hp => ((mem_primesRange).1 hp).1)
    hNA (fun j hj => (hblock j hj).1) momentOrder_ge
    (fun j hj => (hblock j hj).2.1) (fun j hj => (hblock j hj).2.2.1)
    (fun j hj => (hblock j hj).2.2.2)

end

end RHTower.Sieve
