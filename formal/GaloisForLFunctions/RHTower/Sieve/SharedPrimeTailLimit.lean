import GaloisForLFunctions.RHTower.Sieve.SharedPrimeTail
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The shared-prime tail vanishes after normalisation

Dividing the shared-prime tail bound by `h·√x` leaves

    (1/P) + [ mertensS(2√x)/h + mertensS(2√x)/√x + 2/h ],

and the bracket tends to zero as soon as `h/log log(3x) → ∞`: Mertens' second theorem bounds the
prime-reciprocal sum by `log log(3x) + C`, the first term is then the reciprocal of the growth
hypothesis, and the other two are smaller still.

So the whole shared-prime tail over the primes above `P` contributes at most `1/P` in the limit,
uniformly in the interval data.  This is the `O`-term of the card's equation `(11)`.
-/

namespace RHTower.Sieve

open Finset Nat Filter Topology

/-- The prime-reciprocal sum at the balanced height, against `log log(3x)`. -/
theorem mertensS_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    mertensS ⌊2 * Real.sqrt x⌋₊ ≤ Real.log (Real.log (3 * x)) + mertensSecondUpperConst := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hx
  have h2s : (2 : ℝ) ≤ 2 * Real.sqrt x := by linarith
  have hQ2 : 2 ≤ ⌊2 * Real.sqrt x⌋₊ := by
    refine Nat.le_floor ?_
    exact_mod_cast h2s
  have hQle : ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x :=
    Nat.floor_le (by linarith)
  have hsq3 : 2 * Real.sqrt x ≤ 3 * x := by
    have hsx : Real.sqrt x ≤ x := by
      nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x, hs1]
    linarith
  have hQ3 : ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ 3 * x := le_trans hQle hsq3
  have hQpos : (0 : ℝ) < ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQ2
    linarith
  have hlogQ : (0 : ℝ) < Real.log ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hQ2
    linarith
  have hlogle : Real.log ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ Real.log (3 * x) :=
    Real.log_le_log hQpos hQ3
  have hloglog : Real.log (Real.log ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ))
      ≤ Real.log (Real.log (3 * x)) := Real.log_le_log hlogQ hlogle
  have hmert := mertensS_le hQ2
  rw [logLog] at hmert
  linarith

/-- **The normalised shared-prime tail.**  Everything beyond `1/P` is the excess term. -/
theorem shared_prime_tail_normalized_le {P : ℕ} (hP : 1 ≤ P) {x hx : ℝ}
    (hx1 : 1 ≤ x) (hh : 0 < hx) :
    (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊,
        (Real.sqrt x / (p : ℝ) + 1) * (hx / (p : ℝ) + 1)) / (hx * Real.sqrt x)
      ≤ 1 / (P : ℝ)
        + ((Real.sqrt x + hx) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
          / (hx * Real.sqrt x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hden : (0 : ℝ) < hx * Real.sqrt x := by positivity
  have hbase := sum_pair_tail_le (P := P) hP ⌊2 * Real.sqrt x⌋₊
    (l₁ := Real.sqrt x) (l₂ := hx) hs0.le hh.le
  have hQle : ((⌊2 * Real.sqrt x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.sqrt x :=
    Nat.floor_le (by positivity)
  have hstep : ∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊,
      (Real.sqrt x / (p : ℝ) + 1) * (hx / (p : ℝ) + 1)
      ≤ Real.sqrt x * hx / (P : ℝ)
        + ((Real.sqrt x + hx) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x) := by
    linarith [hbase, hQle]
  rw [div_le_iff₀ hden]
  have hrw : (1 / (P : ℝ)
        + ((Real.sqrt x + hx) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
          / (hx * Real.sqrt x)) * (hx * Real.sqrt x)
      = Real.sqrt x * hx / (P : ℝ)
        + ((Real.sqrt x + hx) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x) := by
    field_simp
  rw [hrw]
  exact hstep

/-- The excess term, split. -/
theorem excess_eq {x hx : ℝ} (hx0 : 0 < x) (hh : 0 < hx) :
    ((Real.sqrt x + hx) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x) / (hx * Real.sqrt x)
      = mertensS ⌊2 * Real.sqrt x⌋₊ / hx + mertensS ⌊2 * Real.sqrt x⌋₊ / Real.sqrt x
        + 2 / hx := by
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  field_simp

/-- The prime-reciprocal sum is nonnegative. -/
theorem mertensS_nonneg_sharedPrimeTailLimit (N : ℕ) : 0 ≤ mertensS N := by
  rw [mertensS]
  refine Finset.sum_nonneg ?_
  intro p _
  positivity

/-- The growth hypothesis forces the window length to grow. -/
theorem tendsto_of_growth {h : ℝ → ℝ}
    (hgrow : Tendsto (fun x => h x / Real.log (Real.log (3 * x))) atTop atTop) :
    Tendsto h atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ hgrow
  filter_upwards [hgrow.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.exp (Real.exp 1))] with x h1 h2
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) h2
  have hlog3x : Real.exp 1 ≤ Real.log (3 * x) := by
    have hle : Real.exp (Real.exp 1) ≤ 3 * x := by linarith
    have := Real.log_le_log (Real.exp_pos _) hle
    rwa [Real.log_exp] at this
  have hll : (1 : ℝ) ≤ Real.log (Real.log (3 * x)) := by
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have := Real.log_le_log hpos hlog3x
    rwa [Real.log_exp] at this
  have hllpos : (0 : ℝ) < Real.log (Real.log (3 * x)) := by linarith
  have hge : Real.log (Real.log (3 * x)) ≤ h x := (one_le_div hllpos).1 h1
  have hhpos : (0 : ℝ) < h x := lt_of_lt_of_le hllpos hge
  exact div_le_self hhpos.le hll

/-- `log log` against the square root. -/
theorem tendsto_loglog_div_sqrt :
    Tendsto (fun x : ℝ => Real.log (Real.log (3 * x)) / Real.sqrt x) atTop (𝓝 0) := by
  have hlogsqrt : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    have hbase : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hcomp := (hbase.comp Real.tendsto_sqrt_atTop).const_mul (2 : ℝ)
    simp only [Function.comp_apply, mul_zero] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [Real.log_sqrt hx]
    ring
  have hsqinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) := by
    have h0 := Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    refine h0.congr fun x => ?_
    simp only [Pi.inv_apply]
  have hconst : Tendsto (fun x : ℝ => Real.log 3 / Real.sqrt x) atTop (𝓝 0) := by
    have := hsqinv.const_mul (Real.log 3)
    simpa [div_eq_mul_inv, mul_zero] using this
  have hmaj : Tendsto (fun x : ℝ => Real.log 3 / Real.sqrt x + Real.log x / Real.sqrt x)
      atTop (𝓝 0) := by
    have := hconst.add hlogsqrt
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
    have h3x : Real.exp 1 ≤ 3 * x := by linarith
    have hlog : (1 : ℝ) ≤ Real.log (3 * x) := by
      have := Real.log_le_log (Real.exp_pos 1) h3x
      rwa [Real.log_exp] at this
    have : (0 : ℝ) ≤ Real.log (Real.log (3 * x)) := Real.log_nonneg hlog
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have h3x : (0 : ℝ) < 3 * x := by linarith
    have hstep : Real.log (Real.log (3 * x)) ≤ Real.log 3 + Real.log x := by
      have hlog3xpos : (0 : ℝ) < Real.log (3 * x) := Real.log_pos (by linarith)
      have hle : Real.log (Real.log (3 * x)) ≤ Real.log (3 * x) :=
        le_trans (Real.log_le_sub_one_of_pos hlog3xpos) (by linarith)
      have hmulrw : Real.log (3 * x) = Real.log 3 + Real.log x :=
        Real.log_mul (by norm_num) (ne_of_gt hxpos)
      linarith [hle, hmulrw.le, hmulrw.ge]
    rw [← add_div]
    gcongr

/-- **The excess term vanishes.** -/
theorem tendsto_shared_prime_excess {h : ℝ → ℝ}
    (hgrow : Tendsto (fun x => h x / Real.log (Real.log (3 * x))) atTop atTop) :
    Tendsto (fun x : ℝ =>
        ((Real.sqrt x + h x) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
          / (h x * Real.sqrt x)) atTop (𝓝 0) := by
  have hhtop : Tendsto h atTop atTop := tendsto_of_growth hgrow
  have hinvh : Tendsto (fun x : ℝ => 1 / h x) atTop (𝓝 0) := by
    have h0 := hhtop.inv_tendsto_atTop
    refine h0.congr fun x => ?_
    simp [Pi.inv_apply, one_div]
  have hLLh : Tendsto (fun x : ℝ => Real.log (Real.log (3 * x)) / h x) atTop (𝓝 0) := by
    have h0 := hgrow.inv_tendsto_atTop
    refine h0.congr fun x => ?_
    simp only [Pi.inv_apply]
    rw [inv_div]
  have hinvsqrt : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) := by
    have h0 := Real.tendsto_sqrt_atTop.inv_tendsto_atTop
    refine h0.congr fun x => ?_
    simp [Pi.inv_apply, one_div]
  have hmaj : Tendsto (fun x : ℝ =>
      Real.log (Real.log (3 * x)) / h x + mertensSecondUpperConst * (1 / h x)
        + Real.log (Real.log (3 * x)) / Real.sqrt x
        + mertensSecondUpperConst * (1 / Real.sqrt x) + 2 * (1 / h x)) atTop (𝓝 0) := by
    have h1 := hinvh.const_mul mertensSecondUpperConst
    have h2 := hinvsqrt.const_mul mertensSecondUpperConst
    have h3 := hinvh.const_mul (2 : ℝ)
    have := ((((hLLh.add h1).add tendsto_loglog_div_sqrt).add h2).add h3)
    simpa using this
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ), hhtop.eventually_gt_atTop (0 : ℝ)]
      with x hx hh
    have hxpos : (0 : ℝ) < x := by linarith
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hM := mertensS_nonneg_sharedPrimeTailLimit ⌊2 * Real.sqrt x⌋₊
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ), hhtop.eventually_gt_atTop (0 : ℝ)]
      with x hx hh
    have hxpos : (0 : ℝ) < x := by linarith
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hM := mertensS_nonneg_sharedPrimeTailLimit ⌊2 * Real.sqrt x⌋₊
    have hMle := mertensS_sqrt_le hx
    rw [excess_eq hxpos hh]
    have hA : mertensS ⌊2 * Real.sqrt x⌋₊ / h x
        ≤ Real.log (Real.log (3 * x)) / h x + mertensSecondUpperConst * (1 / h x) := by
      rw [div_add' _ _ _ (ne_of_gt hh)]
      · rw [div_le_div_iff_of_pos_right hh]
        field_simp
        linarith
    have hB : mertensS ⌊2 * Real.sqrt x⌋₊ / Real.sqrt x
        ≤ Real.log (Real.log (3 * x)) / Real.sqrt x
          + mertensSecondUpperConst * (1 / Real.sqrt x) := by
      rw [div_add' _ _ _ (ne_of_gt hs0)]
      · rw [div_le_div_iff_of_pos_right hs0]
        field_simp
        linarith
    have hC : (2 : ℝ) / h x = 2 * (1 / h x) := by ring
    linarith [hA, hB, hC]

/-- **The normalised tail is eventually within `ε` of `1/P`.** -/
theorem eventually_shared_prime_tail_le {h : ℝ → ℝ}
    (hgrow : Tendsto (fun x => h x / Real.log (Real.log (3 * x))) atTop atTop)
    {P : ℕ} (hP : 1 ≤ P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊,
          (Real.sqrt x / (p : ℝ) + 1) * (h x / (p : ℝ) + 1)) / (h x * Real.sqrt x)
        ≤ 1 / (P : ℝ) + ε := by
  have hhtop : Tendsto h atTop atTop := tendsto_of_growth hgrow
  have hexc := tendsto_shared_prime_excess hgrow
  filter_upwards [eventually_ge_atTop (1 : ℝ), hhtop.eventually_gt_atTop (0 : ℝ),
    hexc.eventually (eventually_lt_nhds hε)] with x hx hh hE
  have hbound := shared_prime_tail_normalized_le hP hx hh
  have hEle : ((Real.sqrt x + h x) * mertensS ⌊2 * Real.sqrt x⌋₊ + 2 * Real.sqrt x)
      / (h x * Real.sqrt x) ≤ ε := hE.le
  linarith

/-- **Card equation (11).**  For every `ε` there is a prime cut-off beyond which the shared-prime
tail is at most `ε`, uniformly in the interval data. -/
theorem exists_shared_prime_tail_small {h : ℝ → ℝ}
    (hgrow : Tendsto (fun x => h x / Real.log (Real.log (3 * x))) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, 1 ≤ P ∧ ∀ᶠ x in atTop,
      (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊,
          (Real.sqrt x / (p : ℝ) + 1) * (h x / (p : ℝ) + 1)) / (h x * Real.sqrt x) ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  refine ⟨max M 1, le_max_right _ _, ?_⟩
  have hP1 : 1 ≤ max M 1 := le_max_right _ _
  have hPpos : (0 : ℝ) < ((max M 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by exact_mod_cast hP1
    linarith
  have hPM : ((M : ℕ) : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left M 1
  have hsmall : 1 / ((max M 1 : ℕ) : ℝ) ≤ ε / 2 := by
    rw [div_le_div_iff₀ hPpos (by norm_num)]
    have h2 : 2 / ε < ((max M 1 : ℕ) : ℝ) := lt_of_lt_of_le hM hPM
    rw [div_lt_iff₀ hε] at h2
    linarith
  filter_upwards [eventually_shared_prime_tail_le hgrow hP1 (half_pos hε)] with x hx
  linarith

end RHTower.Sieve
