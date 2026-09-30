# Weil positivity forces a harmonically dense prime deficit set

- **ID:** weil-cone-prime-deficit-set
- **Stage:** 3-formalized (MUST-588)
- **Source:** MC conjecture loop, cycle 173. It combines the multiplicative Toeplitz bound of Weil positivity (HF, `WeilPositivityMultiplicativeToeplitzBound`) with MUST-584.
- **Theorem** (`RHTower.WeilPrimeDeficit.eq_vonMangoldt_of_weilPositiveFull_of_thin_prime_deficit`). Let `lam` be full-cone Weil-positive, and suppose:
  - `Σ_{n not prime} |lam(n) − Λ(n)|/n < ∞`;
  - the prime deficit set `S⁻ = {p : lam(p) < log p}` satisfies `Σ_{p∈S⁻} log p / p < ∞`.

  Then `lam = Λ` on `n ≥ 2`. The size of the deficits on `S⁻` and the size of the excesses elsewhere are unrestricted, apart from the box bound that every cone member satisfies.
- **Corollary** (`…_of_prime_support`). A prime-supported second cone point has `Σ_{p : lam(p) < log p} log p/p = ∞`.

## Phase 1–4
- **Starting point.** After MUST-586 the prime part of the (P2) core is "Λ-size, sign-oscillating". The corpus already had:
  - the Toeplitz bound `2Σ_n lam(n) n^{−1/2} Re⟨c(n·), c⟩ ≤ (log N + C₀)‖c‖²`;
  - the Gibbs asymptotic `2P(N)/H(N) = log N − γ + o(1)`;
  - `weil_supersystem_excess_small` (`lam ≥ Λ` ⇒ excess `o(log² N)`).
- **Conjecture.** Weil positivity is asymmetric on the primes. Excess is cheap to rule out, and only a thin deficit set is needed to rule out everything.
- **Mechanism.**
  - Take the signed Gibbs resonator `c(m) = σ(m)m^{−1/2}`, where `σ` is completely multiplicative with `σ(p) = −1` exactly on `S⁻`.
  - This gives `⟨c(n·), c⟩ = σ(n)n^{−1/2}H_N(n)`, so the Toeplitz bound pairs `lam(n)σ(n)` against the Gibbs profile.
  - On the primes, `d(p)σ(p) = |d(p)|`.
  - The `Λ`-part equals the Gibbs energy minus the prime powers of `S⁻`.
- **Kill attempts.**
  1. *False?* No; the paper proof below is complete.
  2. *Circular?* No.
  3. *Implied by the corpus?* Compare with the existing results:
     - MUST-586 needs the deficit *values* to be summable;
     - the sign-set corollary needs `Σ_{S⁻}(1+log p)/√p < ∞`;
     - `weil_supersystem_excess_small` handles only `S⁻ = ∅`, and only to `o(log²N)`.

     The new law needs only *harmonic* thinness of the deficit *set*.
  4. *Insignificant?* Moderate. It sharpens the prime-supported evaporation core. The composite part still needs absolute summability, because the Toeplitz bound only sees completely multiplicative sign patterns.
- **Verdict.** SURVIVES.

## Phase 5 — paper proof
1. **Signed Toeplitz inequality.** Weil positivity gives `2Σ_{2≤n≤N} lam(n)σ(n)H_N(n)/n ≤ (log N + C₀)H(N)`, with `H_N(n) = Σ_{m≤N/n}1/m` (`exists_signed_toeplitz_le`).
2. **Termwise lower bound.** Split `lam(n)σ(n) = Λ(n)σ(n) + d(n)σ(n)`.
   - *Prime powers.* `Λ(n)σ(n)/n ≥ Λ(n)/n − 2F(n)`, where `F(n) = Λ(n)/n` if the prime of `n` lies in `S⁻` and `0` otherwise (`vonMangoldt_div_sub_le`).
   - *Primes.* `d(p)σ(p) = |d(p)|`.
   - *Non-primes.* `d(n)σ(n) ≥ −|d(n)|`.
   - With `H_N(n) ≤ H(N)`: `Σ_{2≤n≤N} lam σ H_N/n ≥ P(N) − 2H(N)ΣF + Σ_p |d(p)|H_N(p)/p − H(N)A`, where `P(N)` is the Gibbs energy and `A = Σ_{non-prime}|d|/n`.
3. **Gibbs.** For large `N`, `2P(N) ≥ (log N − γ − 1)H(N)` (`tendsto_gibbs_rayleigh`). Hence `Σ_p |d(p)|H_N(p)/p ≤ K·H(N)`, with `K = (|C₀| + γ + 1 + 4ΣF + 2A)/2`.
4. **`F` is summable** (`summable_deficitWeight`). Bound `F(n) ≤ [n ∈ S⁻] log n/n + [n not prime]Λ(n)/n`. The second term is summable by `sum_nonprime_vonMangoldt_rpow_le` at `δ = ½`.
5. **Tauberian step at `N = M²`.** For `p ≤ M`, `H_{M²}(p) ≥ H(M) ≥ log M`, and `H(M²) ≤ 1 + 2 log M`. So `Σ_{p≤M}|d(p)|/p ≤ 3K`.
6. **Conclusion.** `Σ|d|/n < ∞`, and MUST-584 gives `lam = Λ`. ∎

## Lean (formalized 2026-09-30)
Module `RHTower/WeilPrimeDeficitSetRigidity.lean`. It compiles clean under `lake env lean`, was built with `lake build --old`, `#print axioms` reports the standard three, it is wired into `RHTower.lean` after `WeilOneSidedConvergenceRigidity`, and the collision sweep is clean.
- `signMult` (the completely multiplicative sign) with `signMult_mul`, `signMult_prime_pow`, `signMult_sq`, `abs_signMult`.
- `partialHarm`, `harm_le_one_add_log`, `harm_le_partialHarm_sq`.
- `exists_signed_toeplitz_le`.
- `deficitSign`, `deficitWeight`, `vonMangoldt_div_sub_le`, `summable_nonprime_vonMangoldt_div`, `summable_deficitWeight`.
- `gibbsEnergy_eq_sum_partialHarm`.
- `summable_prime_abs_div_of_thin_deficit`, the theorem, and the prime-support corollary.

## Audit note on a corpus statement
`RHTower.weil_twisted_density_bound` (HF, `WeilPositivityMultiplicativeToeplitzBound`) states its bound "for every completely multiplicative unimodular χ", with hypotheses `∀ a b, χ(ab) = χ(a)χ(b)` over all of `ℕ` and `‖χ(m)‖ = 1` for all `m`.
- At `a = 0` these hypotheses force `χ ≡ 1`: `χ(0) = χ(0)χ(b)` and `χ(0) ≠ 0`. This was checked in a scratch Lean file.
- So the twisted corollary is vacuous beyond `χ ≡ 1`. `weil_log_density_le` (which uses `χ ≡ 1`) is unaffected.
- The present module avoids the issue by applying `weil_multiplicativeToeplitz_bound` directly to a resonator supported on `1 ≤ m ≤ N`.
- The HF file was not modified. The fix would be to require multiplicativity only for `a, b ≥ 1`.

## Significance
- **The prime part of (P2) is asymmetric.** A second cone point that is prime-supported, or whose composite deviations are absolutely harmonic, must undershoot `Λ` on a harmonically dense set of primes: `Σ_{lam(p) < log p} log p/p = ∞`.
- Excess can be arbitrary on the other primes, yet it does not help.
- The composite part remains the obstacle: completely multiplicative resonators see composite signs only through products of prime signs.

## Cycle 174 addendum — the general sign law [L]
- **Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_signMult_aligned`). Let `σ_s` be completely multiplicative with `σ_s(p) = s(p) ∈ {±1}` and `Σ_{p : s(p) = −1} log p/p < ∞`. If `d = lam − Λ` has the sign of `σ_s` except on an absolutely harmonic part, then `lam = Λ`.
- The prime-deficit law (MUST-588) is the case `s = deficitSign lam`: primes are aligned by construction, so only the non-primes need absolute harmonicity.
- **New content.** Composite deviations no longer need to be absolutely harmonic, only aligned with a multiplicative sign pattern that has a thin set of negative primes. Examples of excluded deviations:
  - a `d` that is `≥ 0` on every `n` coprime to a thin set `S` of primes;
  - a `d` whose sign on the multiples of `S` is `(−1)^{Ω_S(n)}`, where `Ω_S(n)` counts the prime factors of `n` in `S` with multiplicity.
- **Scope.** This is the final form of the Toeplitz method. Its near-top vectors are multiplicative, so it detects exactly the multiplicative sign patterns with harmonically thin negative sets, and nothing else.
