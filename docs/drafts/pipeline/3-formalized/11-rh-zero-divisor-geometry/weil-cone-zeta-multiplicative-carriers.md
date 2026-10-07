# ζ-multiplicative pole carriers in the Weil cone

- **ID:** weil-cone-zeta-multiplicative-carriers
- **Stage:** 3-formalized (MUST-821)
- **Type:** THEOREM
- **Source:** loop row 555; closes the recorded "Cannot" of MUST-815 and MUST-816 (non-constant `M`)
- **Statement:** Let `m, v : ℕ → ℝ` with `Σ|m(n)|n^{−½} < ∞`, `Σ|v(n)|n^{−½} < ∞`, `v(0) = v(1) = 0`, and let `β ∈ ℝ`. Put `λ(n) = βΛ(n) + Σ_{k∣n} m(k) + v(n)` for `n ≥ 2` and `λ(0) = λ(1) = 0`. Its Dirichlet series is `−βζ′/ζ + ζ(s)M(s) − m(1) + V(s)`. If `λ` is full-cone Weil-positive, then `λ = Λ` on `n ≥ 2`, and RH holds.
  In words: a producer cannot carry any part of its pole at `s = 1` multiplicatively in `ζ`, with an absolutely convergent multiplier on the critical line. The share `M(1)` must be `0`, and then everything collapses to `Λ`.

## Lean
- `RHTower/WeilConeZetaCarrierBoundary.lean` (namespace `RHTower.WeilZetaCarrier`):
  - `LSeries_carrierSystem`;
  - master identity `masterLeft_carrier`, residue identity `beta_add_mu` (`β + M(1) = 1`);
  - numerator `carrierNumerator` and line inequality `line_ineq_carrier`;
  - `M(1) < 0` excluded by Hardy zeros: `mu_nonneg`;
  - Fubini bounds `summable_sum_Ioc_div`, `summable_inv_sqrt_mul_tail`;
  - `M(1) = 0` gives `λ = Λ`: `eq_vonMangoldt_of_mu_eq_zero`, via the corpus `vonMangoldt_add_twoPole_eq_zero`.
- `RHTower/WeilConeZetaCarrierResonance.lean`:
  - completely multiplicative resonators `cmul`, `gA`, `hA`, `HA`;
  - `toeplitz_cmul` (from the corpus `weil_multiplicativeToeplitz_bound`) and `toeplitz_carrier`;
  - the convolution identity `sum_divisors_conv_eq`;
  - the moduli `Apow`, `Bprod` with `wL`, and the lower bound `zetaPart_ge`;
  - `M(1) > 0` excluded: `mu_nonpos`;
  - main theorems `eq_vonMangoldt_of_weilPositiveFull_carrier` and `riemannHypothesis_of_weilPositiveFull_carrier`.
- Standard axioms only. Both modules are wired after `WeilConeResonanceBudget`.

## Paper proof (as formalized)
1. **Residue.** The master identity `Z₁((s−1)(Φ − G + V − m(1)) − 1) = β((s−1)Z₁′ − Z₁) − Z₁²M` on `Re s > ½`, evaluated at `s = 1`, gives `β + M(1) = 1`.
2. **Line inequality.** `Φζ = (G + 1/(s−1) − ζM + m(1) − V)ζ + βζ′` is continuous up to the line. With `Re(ζ′ζ̄) = −θ′|ζ|²` this gives `|ζ|²(M(1)θ′ − Re(ζM) + m(1) − Re V) ≥ 0`.
3. **`M(1) < 0`.** At a zero `t₀` of `ζ` on the line (Hardy), `ζM → 0`, while `M(1)θ′(t) ≤ M(1)(log(t/2π)/2 − 4) → −∞`. Contradiction near `t₀` once `t₀` is large.
4. **`M(1) > 0`.** Apply the Weil–Toeplitz bound to `c(k) = 1_{k∣N}φ(k)`, where `φ` is completely multiplicative with `φ(p) = p^{−½}` for `p < L` and `φ(p) = 1` for `p ≥ L`, and `N = ∏_{p<L}p^J · ∏_{L≤p≤y}p`.
   - With `g = φ·n^{−½}`, `h = φ²⋆1` and `H = g⋆h`, the ζ-part equals `Σ_{k∣N} m(k)g(k)H(N/k)`. On divisors of `A_J = ∏_{p<L}p^J`, `g(k) = 1/k`, so the resonator evaluates `M` at `s = 1` on the small primes.
   - `H(A_J)` is monotone in `J` and bounded by `4^{π(L)}`, so `H(A_J/k)/H(A_J) → 1` for fixed `k`. Tails of `Σ|m|/k` and `Σ|m|/√k` control the rest. So the ζ-part is `≥ H(N)M(1)/2`.
   - The `Λ`- and `v`-parts cost `≤ h(N)((1+2|β|)log N + O(1))`.
   - Since `H(N)/h(N) ≥ ∏_{L≤p≤y}(1 + p^{−½}/2) ≥ exp(c√y/log y)/K_L` against `log N ≤ log A_J + y log 4`, this is a contradiction.
5. **`M(1) = 0`.** Then `β = 1` and `λ = Λ + w` with `w = (1⋆m) + v`. The partial sums of `w` are `−Σ_{j≤n} m(j){n/j} − nΣ_{j>n}m(j)/j + O(Σ|v|)`. Their weights `|·|/(n√n)` are summable by Fubini, using only `Σ|m(j)|j^{−½} < ∞`. The corpus two-pole rigidity then gives `w = 0` on `n ≥ 2`.

## Why it matters
- It completes the classification of regular pole carriers. With MUST-801–810 (log-derivative carriers `Λ⋆a`, with Möbius parts) and MUST-815/816 (constant `M`), a Weil-positive producer cannot carry its pole multiplicatively in `ζ`. The pole has to sit in a logarithmic derivative, and then it is `Λ`.
- Mechanism: the residue normalization `β + M(1) = 1` drives both halves. A positive share is detected by a hybrid resonator that evaluates the Euler product at `s = 1` on small primes and at `s = ½` on large ones. A negative share is detected at Hardy zeros.

## Scope and limits
- RH-blind: an exclusion (uniqueness) theorem. It produces no element of `W`.
- `M` absolutely convergent on the line is used twice: for continuity of `ζM` up to the line (step 3), and for the Fubini bounds (step 5). Natural boundaries of `M` at the line are not covered.
- Novelty audit: the corpus had MUST-815 (`M = β` constant) and MUST-816 (`βΛ + γ`), and the Toeplitz bound itself. No corpus or literature result treats non-constant multiplicative carriers.

## Log
- 2026-10-07: card created and formalized (loop row 555).
