import GaloisForLFunctions.BiScaleUncertainty.MertensValuationBudget
import GaloisForLFunctions.RHTower.RobinInequalityKFree

/-!
# The growing valuation core of Robin counterexamples

At the cutoff `N = floor (log n)`, the exact Euler factors retain the defect
`Σ p^{-(v_p(n)+1)}`. The inverse product contributes `o(1/log N)` to its exponent,
and the primes beyond the cutoff cost at most `(1+o(1))/log log n`.
Consequently a Robin counterexample must contain every prime power below
`η log log n`, for each fixed `η < 1` and all sufficiently large `n`.
-/

open Filter Topology
open ArithmeticFunction (sigma)
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The total local exponent defect below an Euler-product cutoff. -/
def robinValuationDefect (n N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 0 N).filter Nat.Prime, (1 / (p : ℝ)) ^ (n.factorization p + 1)

theorem robinValuationDefect_nonneg (n N : ℕ) : 0 ≤ robinValuationDefect n N :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The large-prime tail retains the floor ratio, whose limit is one. -/
theorem one_add_inv_pow_le_exp_floor_ratio {n N c : ℕ} (hn : 16 ≤ n)
    (hNdef : N = ⌊Real.log n⌋₊) (hc : (N + 1) ^ c ≤ n) :
    (1 + 1 / (N : ℝ)) ^ c ≤
      Real.exp ((Real.log n / N) / Real.log (Real.log n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN2 : 2 ≤ N := by rw [hNdef]; exact two_le_floor_log hn
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNle : (N : ℝ) ≤ Real.log n := by
    rw [hNdef]
    exact Nat.floor_le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  have hloglog : 0 < Real.log (Real.log n) :=
    Real.log_pos (by linarith)
  have hN1 : Real.log n < (N : ℝ) + 1 := by
    rw [hNdef]
    exact Nat.lt_floor_add_one _
  have hcl : (c : ℝ) * Real.log ((N : ℝ) + 1) ≤ Real.log n := by
    have h := Real.log_le_log (by positivity)
      (show (((N + 1) ^ c : ℕ) : ℝ) ≤ n by exact_mod_cast hc)
    push_cast at h
    rwa [Real.log_pow] at h
  have hlogN1 : Real.log (Real.log n) ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by linarith) hN1.le
  have hc' : (c : ℝ) ≤ Real.log n / Real.log (Real.log n) := by
    rw [le_div_iff₀ hloglog]
    exact (mul_le_mul_of_nonneg_left hlogN1 (Nat.cast_nonneg c)).trans hcl
  calc (1 + 1 / (N : ℝ)) ^ c ≤ Real.exp (1 / N) ^ c := by
        apply pow_le_pow_left₀ (by positivity) _ c
        linarith only [Real.add_one_le_exp (1 / (N : ℝ))]
    _ = Real.exp (c * (1 / N)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((Real.log n / N) / Real.log (Real.log n)) := by
        apply Real.exp_le_exp.mpr
        calc (c : ℝ) * (1 / N) ≤
            (Real.log n / Real.log (Real.log n)) * (1 / N) := by
              exact mul_le_mul_of_nonneg_right hc' (by positivity)
          _ = (Real.log n / N) / Real.log (Real.log n) := by ring

/-- The retained floor ratio tends to one. -/
theorem tendsto_log_div_floor_log_nat :
    Tendsto (fun n : ℕ => Real.log n / (⌊Real.log n⌋₊ : ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_floor_div_atTop (R := ℝ)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).inv₀ one_ne_zero
  simpa only [Function.comp_def, inv_div, inv_one] using h

/-- An unconditional source bound with the full valuation defect retained. -/
theorem eventually_sigma_div_le_moving_defect {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((sigma 1 n : ℕ) : ℝ) / n ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) *
        Real.exp ((1 + ε) / Real.log (Real.log n) -
          robinValuationDefect n ⌊Real.log n⌋₊) := by
  have hM := tendsto_floor_log_nat.eventually
    (eventually_inv_mertens_le_exp_small (show 0 < ε / 4 by positivity))
  have hratio := (tendsto_order.mp tendsto_log_div_floor_log_nat).2
    (1 + ε / 2) (by linarith)
  filter_upwards [hM, hratio, eventually_ge_atTop 16] with n hm hr hn
  set N := ⌊Real.log n⌋₊ with hNdef
  set L := Real.log (Real.log n) with hLdef
  have hn0 : n ≠ 0 := by omega
  have hN2 : 2 ≤ N := two_le_floor_log hn
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hNle : (N : ℝ) ≤ Real.log n := Nat.floor_le (Real.log_natCast_nonneg n)
  have hxpos : 0 < Real.log n := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogNle : Real.log N ≤ L := Real.log_le_log hNpos hNle
  have hLle : L ≤ 2 * Real.log N := by
    have hfloor : Real.log n < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hxN : Real.log n ≤ (N : ℝ) ^ 2 := by nlinarith only [hfloor, hNr]
    have h := Real.log_le_log hxpos hxN
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hsmall : (ε / 4 / Real.log N) * L ≤ ε / 2 := by
    have h := mul_le_mul_of_nonneg_left hLle
      (show 0 ≤ ε / 4 / Real.log N by positivity)
    have heq : (ε / 4 / Real.log N) * (2 * Real.log N) = ε / 2 := by
      field_simp
      ring
    exact heq ▸ h
  have hexponent : ε / 4 / Real.log N + (Real.log n / N) / L ≤ (1 + ε) / L := by
    apply (le_div_iff₀ hLpos).mpr
    have heq : (ε / 4 / Real.log N + (Real.log n / N) / L) * L =
        (ε / 4 / Real.log N) * L + Real.log n / N := by field_simp
    rw [heq]
    change Real.log n / N < 1 + ε / 2 at hr
    linarith only [hsmall, hr]
  have hs := sigma_div_le_mertens_defect hn0 (show 1 ≤ N by omega)
  have ht := one_add_inv_pow_le_exp_floor_ratio hn hNdef
    (pow_card_primeFactors_gt_le hn0 N)
  change (mertensPrimeProduct N)⁻¹ ≤
    Real.exp Real.eulerMascheroniConstant * Real.log N * Real.exp (ε / 4 / Real.log N) at hm
  calc ((sigma 1 n : ℕ) : ℝ) / n ≤ (mertensPrimeProduct N)⁻¹ *
      Real.exp (-robinValuationDefect n N) *
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := hs
    _ ≤ (Real.exp Real.eulerMascheroniConstant * Real.log N *
        Real.exp (ε / 4 / Real.log N)) * Real.exp (-robinValuationDefect n N) *
          Real.exp ((Real.log n / N) / L) := by gcongr
    _ = Real.exp Real.eulerMascheroniConstant * Real.log N *
        Real.exp (ε / 4 / Real.log N + (Real.log n / N) / L -
          robinValuationDefect n N) := by
      rw [show ε / 4 / Real.log N + (Real.log n / N) / L - robinValuationDefect n N =
        (ε / 4 / Real.log N + -robinValuationDefect n N) + (Real.log n / N) / L by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ Real.exp Real.eulerMascheroniConstant * L *
        Real.exp ((1 + ε) / L - robinValuationDefect n N) := by
      gcongr

/-- Every sufficiently large Robin counterexample has a shrinking total exponent defect. -/
theorem eventually_robin_failure_defect_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
          ((sigma 1 n : ℕ) : ℝ) →
        robinValuationDefect n ⌊Real.log n⌋₊ ≤ (1 + ε) / Real.log (Real.log n) := by
  filter_upwards [eventually_sigma_div_le_moving_defect hε,
    eventually_ge_atTop 16] with n hbound hn hfail
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : (2 : ℝ) ≤ (⌊Real.log n⌋₊ : ℝ) := by exact_mod_cast two_le_floor_log hn
  have hL : 0 < Real.log (Real.log n) := Real.log_pos
    (by linarith only [hN, Nat.floor_le (Real.log_natCast_nonneg n)])
  have hlower : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) ≤
      ((sigma 1 n : ℕ) : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    calc Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) * n =
        Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by ring
      _ ≤ ((sigma 1 n : ℕ) : ℝ) := hfail
  by_contra h
  have hexp : Real.exp ((1 + ε) / Real.log (Real.log n) -
      robinValuationDefect n ⌊Real.log n⌋₊) < 1 :=
    Real.exp_lt_one_iff.mpr (sub_neg.mpr (lt_of_not_ge h))
  have hlt := mul_lt_mul_of_pos_left hexp
    (mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hL)
  linarith only [hlower, hbound, hlt]

/-- Every prime power below `η log log n` divides every sufficiently large Robin
counterexample, simultaneously in the prime and the exponent. -/
theorem eventually_robin_failure_prime_power_core {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
          ((sigma 1 n : ℕ) : ℝ) →
        ∀ p : ℕ, p.Prime → ∀ k : ℕ, (p : ℝ) ^ k ≤ η * Real.log (Real.log n) → p ^ k ∣ n := by
  set ε := (1 - η) / (2 * η) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (sub_pos.mpr hη1) (mul_pos (by norm_num) hη)
  have hcoef : (1 + ε) * η < 1 := by
    have heq : (1 + ε) * η = (1 + η) / 2 := by
      rw [hεdef]
      field_simp [hη.ne']
      ring
    rw [heq]
    linarith only [hη1]
  filter_upwards [eventually_robin_failure_defect_le hε, eventually_ge_atTop 16]
    with n hbudget hn hfail p hp k hpow
  by_cases hk : k = 0
  · simp [hk]
  have hn0 : n ≠ 0 := by omega
  have hN : (2 : ℝ) ≤ (⌊Real.log n⌋₊ : ℝ) := by exact_mod_cast two_le_floor_log hn
  have hfloor := Nat.floor_le (Real.log_natCast_nonneg n)
  have hx : 0 < Real.log n := by linarith only [hN, hfloor]
  have hL : 0 < Real.log (Real.log n) :=
    Real.log_pos (by linarith only [hN, hfloor])
  have hLcut : Real.log (Real.log n) < (⌊Real.log n⌋₊ : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hx
    linarith only [h, Nat.lt_floor_add_one (Real.log n)]
  have hηL : η * Real.log (Real.log n) ≤ Real.log (Real.log n) := by
    nlinarith only [hη1, hL]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hple : (p : ℝ) ≤ (p : ℝ) ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hp1 (show 1 ≤ k by omega)
  have hpN : p ≤ ⌊Real.log n⌋₊ := by
    exact_mod_cast (hple.trans (hpow.trans (hηL.trans hLcut.le)))
  have hmem : p ∈ (Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hpN⟩, hp⟩
  have hterm : (1 / (p : ℝ)) ^ (n.factorization p + 1) ≤
      robinValuationDefect n ⌊Real.log n⌋₊ := by
    unfold robinValuationDefect
    exact Finset.single_le_sum
      (f := fun q : ℕ => (1 / (q : ℝ)) ^ (n.factorization q + 1))
      (fun _ _ => by positivity) hmem
  by_contra hdvd
  have hv : n.factorization p < k := by
    exact lt_of_not_ge fun h => hdvd ((hp.pow_dvd_iff_le_factorization hn0).mpr h)
  have hpowa : (p : ℝ) ^ (n.factorization p + 1) ≤ η * Real.log (Real.log n) :=
    (pow_le_pow_right₀ hp1 (by omega)).trans hpow
  have hterm' : 1 / (p : ℝ) ^ (n.factorization p + 1) ≤
      (1 + ε) / Real.log (Real.log n) := by
    simpa only [one_div_pow] using hterm.trans (hbudget hfail)
  have hcross := (div_le_div_iff₀ (pow_pos hppos _) hL).mp hterm'
  have hmul := mul_le_mul_of_nonneg_left hpowa (show 0 ≤ 1 + ε by linarith)
  have hstrict := mul_lt_mul_of_pos_right hcoef hL
  nlinarith only [hcross, hmul, hstrict]

/-- Equivalently, every positive integer below `η log log n` divides a sufficiently
large Robin counterexample. This is a growing least-common-multiple core. -/
theorem eventually_robin_failure_integer_core {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
          ((sigma 1 n : ℕ) : ℝ) →
        ∀ m : ℕ, 0 < m → (m : ℝ) ≤ η * Real.log (Real.log n) → m ∣ n := by
  filter_upwards [eventually_robin_failure_prime_power_core hη hη1,
    eventually_ge_atTop 16] with n hcore hn hfail m hm hbound
  have hn0 : n ≠ 0 := by omega
  apply (Nat.factorization_prime_le_iff_dvd hm.ne' hn0).mp
  intro p hp
  have hdiv : p ^ m.factorization p ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm.ne').mpr le_rfl
  have hpbound : (p : ℝ) ^ m.factorization p ≤ η * Real.log (Real.log n) :=
    (show (p : ℝ) ^ m.factorization p ≤ m by
      exact_mod_cast Nat.le_of_dvd hm hdiv).trans hbound
  exact (hp.pow_dvd_iff_le_factorization hn0).mp
    (hcore hfail p hp (m.factorization p) hpbound)

end

end RHTower
