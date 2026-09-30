# Random integer prime systems are almost surely not Weil-positive

- **ID:** weil-cramer-random-primes
- **Stage:** 3-formalized (paper proof and Lean, 2026-09-30)
- **Type:** THEOREM [P + Lean] + REMARK [P]
- **Source:** `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, entry L169
- **Lean:** `RHTower.CramerModel.ae_not_weilPositiveFull_of_random`,
  `RHTower.CramerModel.ae_not_weilPositiveFull_cramer`,
  `RHTower.RoughRandomPrimes.ae_not_weilPositiveFull_of_rough_random` (L170, Granville-type models;
  module `RHTower/WeilPositivityRoughRandomPrimes`, about 560 lines)
  (module `RHTower/WeilPositivityCramerRandomPrimes`, about 510 lines; axioms `propext`,
  `Classical.choice`, `Quot.sound`)

## Statement

Let `X_n` be random variables with values in `[0, 1]`, pairwise independent on the squarefree
integers, with `E X_n ≥ c/log n` for squarefree `n ≥ 3` (`c > 0`). Let `lam_ω` be any random weights
with `lam_ω(n) = X_n(ω) log n` on squarefree `n`. Then almost surely `lam_ω` is not full-cone
Weil-positive for the archimedean datum of `ζ`.

**Cramér's model.** `X_n = 1_{n ∈ M}` with `P(n ∈ M) = 1/log n`, independent. The theorem covers
both the Cramér weights `X_n log n` and the Beurling von Mangoldt function `Λ_M` (`Λ_M(m^k) = log m`
for `m ∈ M`). On the squarefree integers these agree, and the correlated values at proper powers
play no role.

## Proof

1. **Weil side.** Every Weil-positive `lam` satisfies, for all `y`,
   `2 S_y ≤ (log y# + C₀) d(y#)`, with `S_y = Σ_{n ∣ y#, n ≥ 2} lam(n) n^{−1/2} d(y#/n)` (divisor law,
   MUST-572). The set of `ω` with `lam_ω` Weil-positive lies in `⋃_{K ∈ ℕ} B_K`, where `B_K` is the
   event that this holds with `C₀ = K` for every `y`.
2. **Mean.** `E S_y ≥ c (M_{1/2}(y#) − 2 d(y#)) = c 2^{π(y)} (P_y − 2)`, where
   `P_y = ∏_{p ≤ y}(1 + p^{−1/2}/2)`. Here `M_{1/2} = n^{−1/2} ⋆ d` is multiplicative, and the divisors
   `1, 2` cost at most `2 d(y#)`.
3. **Variance.** Pairwise independence gives `Var S_y ≤ Σ coef²`. Using `log n ≤ log y#` and
   `d(y#/n) ≤ d(y#)`, this is at most `(log y#)² d(y#) M_1(y#) ≤ (log y#)² 4^{π(y)} P_y`.
4. **Growth.** Chebyshev's bound for `θ(y)` gives `P_y ≥ y³` for large `y` (L168 estimates).
5. **Chebyshev.** For large `y` the Weil bound `(log y# + K) d(y#)` is below `E S_y`. So
   `B_K ⊆ {|S_y − E S_y| ≥ E S_y/2}`, which has probability at most
   `4 Var/(E S_y)² ≤ 16 (log 4)² y²/(c² P_y) → 0`. Hence `P(B_K) = 0` for each `K`, and the countable
   union is null. ∎

## Extension (L170, Lean): log-rough models, including Granville's

- **Hypothesis.** `E X_n ≥ c/log n` only for squarefree `n` whose prime factors all exceed `log n`.
- **Granville's model.** Integers coprime to `∏_{p ≤ A}` with `A ≤ log x` are kept with probability
  `(Q/φ(Q))/log n`. An integer whose prime factors all exceed `log n` is coprime to that product,
  so the model satisfies the hypothesis with `c = 1`.
- **Resonator.** `1_{m ∣ N}` with `N = ∏_{p ∈ S} p`, where `S` is a set of `⌊b²/(3 log b)⌋` primes in
  `(b², b³]` (these exist by Chebyshev).
  - `log N ≤ b²`, so every divisor is log-rough.
  - `Q_S ≥ exp(|S| b^{−3/2}/4) ≥ b⁶`.
- **Conclusion.** Both classical probabilistic models of the primes (Cramér 1936, Granville 1995)
  are almost surely not Weil-positive for ζ's archimedean datum.

## Remark [P]: the Cramér zeta satisfies the Beurling RH, but not Weil positivity

- For Cramér's `M`, almost surely `log Z_M(s) = −log(s − 1) + H(s)` with `H` holomorphic on
  `σ > 1/2`. The random part `Σ (X_n − 1/log n) n^{−s}` converges on `σ > 1/2` (Kolmogorov). The
  deterministic part `Σ n^{−s}/log n` continues with a logarithmic singularity at `s = 1` only. The
  higher powers converge absolutely.
- So `Z_M` is almost surely zero-free and holomorphic on `σ > 1/2` apart from the simple pole, and
  `ψ_M(x) = x + O((x log x log log x)^{1/2})`. This is RH-quality prime number theory.
- Continuation stops at `σ = 1/2` (arXiv 2410.03044, which does not discuss Weil positivity).
- Nevertheless `Λ_M` is almost surely not Weil-positive.
- **Hence, for integer Beurling systems, Weil positivity with ζ's archimedean datum is strictly
  stronger than the Beurling Riemann hypothesis.** The extra content is multiplicative:
  - the random primes include smooth squarefree composites;
  - the primorial resonance amplifies them to `exp(c√y/log y)`;
  - the cap is the archimedean `log y#`.
- The violation already occurs at the finite level `log y#`.

## What is new

- The first rigorous statement that the standard probabilistic model of the primes is incompatible
  with Weil positivity. Heuristic incompatibilities of Cramér's model are known (Maier, short
  intervals); this is a positivity-criterion one, with probability one.
- **Producer consequence.** A producer cannot be obtained by randomizing integer supports: any
  independent model that puts inclusion probability `≳ 1/log n` on squarefree composites fails almost
  surely. Models without composites are sub-systems of the prime powers, and thinnings of Λ are
  excluded by downward rigidity (L156). Extension [P]: inclusion probabilities `≥ c (log n)^{−A}`
  also fail. The loss `(log y#)^{A−1} ≤ (y log 4)^{A−1}` is polynomial in `y`, and `P_y` beats every
  power of `y`.
- **Novelty audit.** Web search (2026-09-30) found analytic-continuation results for random Cramér
  zeta functions (arXiv 2410.03044) and probabilistic readings of Weil's explicit sums
  (arXiv 2311.08519), but no Weil-positivity statement for random prime models.

## Gates
- [x] 0 → 1, 1 → 2, 2 → 3 (Lean green, wired into `RHTower`)
- [ ] 3 → 4: not planned

## Log
- 2026-09-30: L169.
