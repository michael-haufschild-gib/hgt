# Robin's inequality away from high powers of two, and Gronwall's theorem

- **ID:** RB-ROBIN-TWO-ADIC-GRONWALL
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (new route candidate RB: Robin/Lagarias divisor-sum receiver)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 60
- **STATUS:** MUST-589

## Receiver (classical, not formalized here)

Robin (1984): RH ⇔ `σ(n) < e^γ n log log n` for all `n > 5040`. Lagarias (2002): RH ⇔
`σ(n) ≤ H_n + e^{H_n} log H_n` for all `n`. Nicolas (1983): RH ⇔
`∏_{p ≤ x}(1 − 1/p)^{−1} > e^γ log θ(x)` for all `x ≥ 2`.

## Theorems [L] (`formal/GaloisForLFunctions/RHTower/RobinInequalityKFree.lean`)

- `eventually_sigma_lt_robin_of_not_two_pow_dvd`: for every `k ≥ 1`, eventually
  `2^k ∤ n → σ(n) < e^γ n log log n`. This covers every `k`-free class.
- `eventually_sigma_le_gronwall`: for every `ε > 0`, eventually `σ(n) ≤ (e^γ + ε) n log log n`.
- `frequently_sigma_ge_gronwall`: for every `ε > 0`, infinitely many `n` have
  `σ(n) ≥ (e^γ − ε) n log log n`.
- `eventually_sigma_lt_robin_of_defect` (cycle 61): for every `δ > 0`, eventually every `n` with
  `D(n) = Σ_{p ≤ log n} p^{−(v_p(n)+1)} ≥ δ` satisfies Robin's inequality
  (`sigma_div_le_mertens_defect`: `σ(n)/n ≤ (∏_{p≤N}(1−1/p))^{−1} e^{−D} (1+1/N)^{|S_{>N}|}`). This
  subsumes the 2-adic statement, gives the analogue at every fixed prime, and covers `n` that miss a set of
  primes `≤ log n` of harmonic mass `≥ δ`.

Axioms: `propext, Classical.choice, Quot.sound`. The only analytic input is the corpus's Mertens
third theorem `tendsto_mertensPrimeProduct_mul_log`.

## Mechanism

1. `σ(n)/n = ∏_{p∣n} (1 − p^{−(a_p+1)})/(1 − 1/p)` (`sigma_div_eq_prod`). Each factor is at most
   `(1 − 1/p)^{−1}` (`local_factor_le`). At `p = 2` with `a < k` the factor is at most
   `2(1 − 2^{−k})` (`local_factor_two_le`).
2. Split the prime factors at `N = ⌊log n⌋`.
   - **Primes `≤ N`** contribute at most `(∏_{p≤N}(1−1/p))^{−1}`
     (`prod_inv_le_inv_mertens`), and at most half of that for odd `n`
     (`prod_inv_le_half_inv_mertens`).
   - **Primes `> N`** satisfy `(N+1)^{c} ≤ n` (`pow_card_primeFactors_gt_le`), so they contribute
     `≤ (1 + 1/N)^c ≤ e^{2/log log n}` (`one_add_inv_pow_le_exp`).
3. Mertens: `(∏_{p≤N}(1−1/p))^{−1} ≤ (1+η) e^γ log N` eventually (`eventually_inv_mertens_le`).
4. **Lower half.** `n = ∏_{p≤y} p^m` gives
   `σ(n)/n ≥ (∏_{p≤y}(1−1/p))^{−1}(1 − 2^{1−m})` (`sigma_div_primorialPow_ge`), using
   `Σ_p p^{−(m+1)} ≤ 2^{1−m}Σ 1/p² ≤ 2^{1−m}`. Also `log n = mθ(y) ≤ 6my`
   (`log_primorialPow_le`). Take `m = ⌈log y⌉ + 1`, so that `log(6my) ≤ (1+η) log y`
   (`eventually_log_six_add_le`).

## RH content and residual

- The inequality is sharp (`limsup = e^γ`), so no margin argument can prove it for all `n`.
  The theorems here use margins that are available only off the extremal set: the factor
  `1 − 2^{−k}` at the prime 2, and the factor `½` for odd `n`.
- If RH fails, Robin fails for infinitely many `n` (Robin). By (a), those `n` have `v₂(n) → ∞`.
- The residual is the colossally abundant numbers: highly composite, with `v_p(n) ≈ log(p^{1+ε}…)`
  and largest prime factor `∼ log n`. There the inequality is equivalent to Nicolas's comparison
  of `∏_{p≤x}(1−1/p)^{−1}` with `e^γ log θ(x)`. That is a one-sided bound on `θ(x) − x` at the
  `√x` scale, the shared open core of MC/WL.
- Not formalized: Robin's equivalence itself (both directions need explicit prime estimates and
  the oscillation theorem).

## The primorial side (cycle 63, MUST-592)

`formal/GaloisForLFunctions/RHTower/NicolasTotientLandau.lean`:
- `div_totient_eq_prod`: `n/φ(n) = ∏_{p∣n}(1 − 1/p)^{−1}`.
- `sigma_div_le_div_totient`: `σ(n)/n ≤ n/φ(n)`.
- `div_totient_le_mertens_missing`: `n/φ(n) ≤ (∏_{p≤N}(1−1/p))^{−1} e^{−Σ_{p≤N,p∤n}1/p}(1+1/N)^{|S_{>N}|}`.
- `eventually_div_totient_lt_of_missing`: missing harmonic mass `≥ δ` ⇒ `n/φ(n) < e^γ log log n`
  eventually.
- `eventually_div_totient_le_landau`, `frequently_div_totient_ge_landau`: Landau's
  `limsup n/(φ(n) log log n) = e^γ`. The lower half comes from Gronwall's through `σ(n)/n ≤ n/φ(n)`.
- `div_totient_primorialPow`: at `∏_{p≤y}p^m`, `n/φ(n)` is exactly the inverse Mertens product.


## Update 2026-10-04
Robin's equivalence (eventual form) is now formal: `RHTower.riemannHypothesis_iff_eventually_robin` (MUST-751, card `robin-criterion-eventual.md`); Nicolas's criterion both directions: `riemannHypothesis_iff_eventually_nicolas` (MUST-750).
