import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor

/-!
# The primes of a window of relative width `η`, counted from below

The moment method needs a *lower* bound for the number of primes in a ladder step
`(y, y(1+η)]`.  The prime number theorem with the classical error term supplies it as soon as `η`
is not smaller than that error:

```text
   ψ(v) − ψ(u) ≥ (v − u) − C·v·e^{−c√(log v)} − C·u·e^{−c√(log u)} ,
   θ(v) − θ(u) ≥ ψ(v) − ψ(u) − (ψ(v) − θ(v))  ≥  …  − 2√v·log v ,
   #{p ∈ (u,v]} ≥ (θ(v) − θ(u))/log v .
```

At the two-range schedule the step ratio is `η = (log x)^{−c₁}` and the ladder starts at
`exp((log x)^{a₀})`, so `e^{−c√(log y)} ≤ e^{−c(log x)^{a₀/2}}` beats every power of the logarithm
and the hypothesis is satisfied with room to spare.  Nothing beyond de la Vallée Poussin is used:
the interval is *relatively* short but absolutely enormous.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

set_option maxHeartbeats 2000000 in
/-- **A window of relative width `η` contains at least `yη/(4 log y)` primes.** -/
theorem exists_card_windowPrimes_ge :
    ∃ C c : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ y : ℝ in atTop, ∀ η : ℝ, 0 < η → η ≤ 1 →
      16 * C * Real.exp (-c * Real.sqrt (Real.log y)) + 24 * Real.log y / Real.sqrt y ≤ η →
      y * η / (4 * Real.log y) ≤ ((windowPrimes y (y * (1 + η))).card : ℝ) := by
  obtain ⟨C, c, hc, hC, hbound⟩ := RHTower.exists_psi_error_eventually
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hbound
  refine ⟨C, c, hc, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop a, Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop (16 : ℝ)]
    with y hya hye hy1 hy16
  intro η hη hη1 hηbig
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (1 : ℝ) ≤ Real.log y := by
    have := Real.log_le_log (Real.exp_pos 1) hye
    rwa [Real.log_exp] at this
  have hlogy0 : (0 : ℝ) < Real.log y := by linarith
  set v : ℝ := y * (1 + η) with hvdef
  have hyv : y ≤ v := by rw [hvdef]; nlinarith
  have hv2y : v ≤ 2 * y := by rw [hvdef]; nlinarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hva : a ≤ v := by linarith
  have hlogv : Real.log y ≤ Real.log v := Real.log_le_log hy0 hyv
  have hlogv0 : (0 : ℝ) < Real.log v := by linarith
  have hlogv2 : Real.log v ≤ 2 * Real.log y := by
    have hstep : Real.log v ≤ Real.log (2 * y) := Real.log_le_log hv0 hv2y
    have hsplit : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) (ne_of_gt hy0)
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  -- the two error bounds
  have hexpv : Real.exp (-c * Real.sqrt (Real.log v))
      ≤ Real.exp (-c * Real.sqrt (Real.log y)) := by
    refine Real.exp_le_exp.2 ?_
    have hsq : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log v) := Real.sqrt_le_sqrt hlogv
    nlinarith [hc, hsq]
  have hexp0 : (0 : ℝ) < Real.exp (-c * Real.sqrt (Real.log y)) := Real.exp_pos _
  have hu := ha y hya
  have hvv := ha v hva
  have hpsiu : Chebyshev.psi y - y ≥ -(C * (y * Real.exp (-c * Real.sqrt (Real.log y)))) :=
    neg_le_of_abs_le hu
  have hpsiv : Chebyshev.psi v - v ≤ C * (v * Real.exp (-c * Real.sqrt (Real.log v))) :=
    le_of_abs_le hvv
  have hpsivge : Chebyshev.psi v - v ≥ -(C * (v * Real.exp (-c * Real.sqrt (Real.log v)))) :=
    neg_le_of_abs_le hvv
  have hverr : C * (v * Real.exp (-c * Real.sqrt (Real.log v)))
      ≤ 2 * (C * (y * Real.exp (-c * Real.sqrt (Real.log y)))) := by
    have h1 : v * Real.exp (-c * Real.sqrt (Real.log v))
        ≤ 2 * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
      have hstep : v * Real.exp (-c * Real.sqrt (Real.log v))
          ≤ v * Real.exp (-c * Real.sqrt (Real.log y)) :=
        mul_le_mul_of_nonneg_left hexpv hv0.le
      nlinarith [hstep, hexp0, hv2y]
    nlinarith [h1, hC, hexp0, hy0]
  have hupsi : Chebyshev.psi y ≤ y + C * (y * Real.exp (-c * Real.sqrt (Real.log y))) := by
    have := le_of_abs_le hu
    linarith
  -- the prime-power excess
  have hpt : Chebyshev.psi v - Chebyshev.theta v ≤ 2 * Real.sqrt v * Real.log v :=
    Chebyshev.psi_sub_theta_le (by linarith)
  have hptu : Chebyshev.theta y ≤ Chebyshev.psi y := Chebyshev.theta_le_psi y
  have hsqv : Real.sqrt v ≤ 2 * Real.sqrt y := by
    have h2 : Real.sqrt v ≤ Real.sqrt (2 * y) := Real.sqrt_le_sqrt hv2y
    have h3 : Real.sqrt (2 * y) = Real.sqrt 2 * Real.sqrt y := Real.sqrt_mul (by norm_num) y
    have h4 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h5 : (0 : ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith [h2, h3, h4, h5]
  have hsqy0 : (0 : ℝ) < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hexcess : 2 * Real.sqrt v * Real.log v ≤ 8 * Real.sqrt y * Real.log y := by
    nlinarith [hsqv, hlogv2, hsqy0, hlogy0]
  -- the theta increment
  have htheta : y * η / 2 ≤ Chebyshev.theta v - Chebyshev.theta y := by
    have hvu : v - y = y * η := by rw [hvdef]; ring
    have hmain : Chebyshev.theta v
        ≥ v - C * (v * Real.exp (-c * Real.sqrt (Real.log v))) - 2 * Real.sqrt v * Real.log v := by
      linarith [hpsivge, hpt]
    have hηy : 16 * C * (y * Real.exp (-c * Real.sqrt (Real.log y)))
          + 24 * Real.sqrt y * Real.log y ≤ y * η := by
      have hmul := mul_le_mul_of_nonneg_left hηbig hy0.le
      have hid : y * (24 * Real.log y / Real.sqrt y) = 24 * Real.sqrt y * Real.log y := by
        calc y * (24 * Real.log y / Real.sqrt y) = (y / Real.sqrt y) * (24 * Real.log y) := by ring
          _ = Real.sqrt y * (24 * Real.log y) := by rw [Real.div_sqrt]
          _ = 24 * Real.sqrt y * Real.log y := by ring
      nlinarith [hmul, hid]
    linarith [hmain, hupsi, hptu, hverr, hexcess, hvu, hηy]
  -- the count
  have hsum : Chebyshev.theta v - Chebyshev.theta y
      = ∑ p ∈ windowPrimes y v, Real.log (p : ℝ) := theta_sub_eq_sum_Ioc hyv
  have hle : ∑ p ∈ windowPrimes y v, Real.log (p : ℝ)
      ≤ ((windowPrimes y v).card : ℝ) * Real.log v := by
    refine (Finset.sum_le_sum (g := fun _ : ℕ => Real.log v) fun p hp => ?_).trans
      (le_of_eq ?_)
    · rw [mem_windowPrimes, Finset.mem_Ioc] at hp
      have hple : (p : ℝ) ≤ v := by
        have h1 : (p : ℝ) ≤ ((⌊v⌋₊ : ℕ) : ℝ) := by exact_mod_cast hp.1.2
        exact h1.trans (Nat.floor_le hv0.le)
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have := hp.2.pos
        exact_mod_cast this
      exact Real.log_le_log hp0 hple
    · rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : y * η / 2 ≤ ((windowPrimes y v).card : ℝ) * (2 * Real.log y) := by
    have hc0 : (0 : ℝ) ≤ ((windowPrimes y v).card : ℝ) := Nat.cast_nonneg _
    nlinarith [htheta, hsum, hle, hlogv2, hc0]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hcard, hlogy0]

end

end RHTower.Sieve
