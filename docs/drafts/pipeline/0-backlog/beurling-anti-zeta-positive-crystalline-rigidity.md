# Anti-zetas and positive–positive crystalline rigidity (Hilberdink–Neamah [½,½,0])

- **ID:** MC-BEURLING-ANTIZETA
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** MC conjecture loop, cycles 109, 111, 115, 116, 118 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`)
- **Statement:** No discrete Beurling system has Möbius sums `M(x) = O(x^{γ})` with `γ` below its zero abscissa. In particular, no `[½,½,0]` system exists (Hilberdink–Neamah, IJNT 16 (2020) 1005–1011, open conjecture).

## Goal
The goal is a structural theorem on discrete Beurling systems. It is ζ-blind and does not bear on RH.
- Hilberdink–Neamah prove that at least two of the exponents α (primes), β (integers), γ (Möbius) equal `Θ ≥ ½`.
- ℕ (under RH) is `[½,0,½]`.
- Broucke–Vindas (arXiv 2102.08478) constructed `[0,½,½]` systems.
- The conjecture says the Möbius exponent cannot be the one below `Θ`.

## Reduction (paper, loop cycles 111–118)
1. `[·,·,γ<½]` ⇔ `1/ζ_P` is analytic and polynomially bounded on `Re s > γ` ⇔ `ζ_P` has no zeros there (a "super-RH" zeta).
2. Atomic floor. For integer-supported systems, or for positive atoms with a Gaussian window, the log-derivative needs singularities with `Re ≥ ½−ε` in every window `|Im s − T| ≤ T^{½+δ}`. These must therefore be **poles** of `ζ_P`: the system is an *anti-zeta*.
3. Mirror law. The explicit formula with positive prime atoms is exactly symmetric under zeros ↔ poles. Every positivity statement about the centred prime measure is even (`|·|²`-type) in the singularity coefficients, so it cannot see the difference (cycle 116).
4. Where the symmetry breaks. For ℕ, the ordinate measure and the prime measure form a **positive–negative** crystalline pair; Landau–Gonek gives negative coherence at prime powers. An anti-zeta would form a **positive–positive** pair.
   - Lev–Olevskii: positive–positive pairs with uniformly discrete supports are Poisson combs.
   - Such a rigidity would put the log-primes in arithmetic progression, which contradicts `ψ_P ~ x`.

## Open core
Prove a Lev–Olevskii-type rigidity for positive atomic measures on `(0,∞)` of density `~e^u/u` (not tempered) whose centred transform has only positive-coefficient singularities in `0 < Re s < 1`.
- Obstacles:
  - The supports are not uniformly discrete.
  - Without a functional equation, Landau–Gonek coherence for anti-systems has error `x^c T log T`.
  - The natural anti-zeta `s/(c(s−1)²ζ(s))` has signed prime measure `2dli − dΠ_ℙ`.
  - Any positive discretization adds mismatch noise of size `t^{½−σ}` of both signs (cycle 115).

## Approach
First the integer-supported case: integer positions give the log-separation needed for the windowed floor. Then try to derive positive coherence from the one-sided growth of `1/ζ_P`, and a rigidity statement from a Gram argument on log-prime ratios.

## Log
- 2026-09-29 — created in 0-backlog from MC loop cycles 109–118 (literature audit and reduction).
- 2026-09-29 — Calibration examples (paper):
  - **`F_q[t]` is a `[1,1,0]` anti-zeta.** Its Beurling zeta `1/(1−q^{1−s})` has no zeros and has poles at `1 + 2πik/log q`, on the abscissa line. The Möbius sums are bounded (`Σ_{deg f≤n} μ(f) = 1−q`), while the prime and integer counts oscillate at full size because the norms are lacunary. So `γ = 0` is realizable when the poles sit on `Re s = 1`, and the conjecture concerns poles on the ½-line.
  - **`ζ_{F_Q[t]}(2s)`** (generators of norm `Q^{2deg P}`, integer multiplicities) is a zero-free Beurling factor with poles on `Re s = ½`, and its Möbius factor `1 − Q^{1−2s}` has only two terms.
  - An anti-zeta then needs a base system with a simple pole at 1, a regular Möbius function and regular primes. By Hilberdink–Neamah such a base must itself have two exponents equal to `Θ ≥ ½`. Products with the `F_Q[t]` factor therefore reproduce the problem instead of solving it, and both `[0,½,½]` (Broucke–Vindas) and `[½,½,½]` bases leave `γ = ½`.
- 2026-09-30 — (MC cycle 152) **Prime-generated systems settled.** For generators `ℙ∖E` with `Σ_{p∈E}1/p < ∞`, `γ ≥ ½` always (Lean `RHTower.CoprimeMobius.not_isBigO_coprimeMobius_of_summable`). The same holds with added integers `C` when `Σ_{c∈C}c^{−½} < ∞`. The remaining integer-supported case, `½`-divergent additions, needs positive coherence of the added integers with the zeta zeros at every height. The explicit formula `Σ_γ w(γ/T)n^{iγ} = −(T/√n)Δ_T(n) + O(log T)` turns this into prime deficits at scale `n/T` with `n > T²`: pair correlation at `α ≥ 2` in sup norm. Card `3-formalized/coprime-mobius-sums-zero-free-region.md`.
