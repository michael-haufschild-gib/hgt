# Deninger folder: stage 2 → stage 3 sweep

- **ID:** `deninger-stage3-sweep`
- **Stage:** 1-in-progress
- **Type:** WORK CARD (formalization sweep)
- **Target:** every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger`
  formalized unconditionally in Lean and moved to `3-formalized/new_scientific_knowledge/deninger`.

## Rules in force

- Lean proofs unconditional: no `sorry`, no `axiom`, no unproved analytic premise, no added
  hypothesis that is not part of the *statement* of the object.
- Verify every mathlib name in a `/tmp` scratch file before use.
- Build in the foreground, one process; `lake env lean <file>` while iterating, `lake build` for
  the audit; wire new modules into `RHTower.lean` (shared file — other sessions edit it too, so
  re-check for duplicate import lines after appending).
- Axiom audit must show exactly `propext, Classical.choice, Quot.sound`.

## Done

| Card | Modules |
|---|---|
| `deninger-cross-prime-closed-relation-saturation` | `RHTower/DeningerCalderonWittCrossPrimeClosedRelationNoGo` (extended with consequences 2 and 4) |
| `deninger-prime-log-height-kothe-calderon-source` | `RHTower/DeningerPrimeLogHeight`, `DeningerKotheComplete`, `DeningerPrimeLogHeightKothe`, `…Convolution`, `…Green`, `…Forms`, `…Mellin`, `…Power`, `…Cartan` (all new) |

## Reusable infrastructure now available

- `DeningerLattice = Nat.Primes →₀ ℤ`, `deningerHeight`, `deningerFreq`, with
  `deningerHeight_add_le`, `deningerHeight_nsmul`, `deningerHeight_inv_le_abs_freq`,
  `abs_deningerFreq_le_log_height`, `deningerHeight_summable_inv_sq`.
- `deningerKothe_exists_limit` (sequential completeness of any Köthe space),
  `deningerKothe_exists_finite_approx` (density of the finitely supported vectors),
  `DeningerKotheTendsto.coord`.
- `deningerHeightMul` : multiplier calculus with the exact seminorm loss.
- `deningerHeightConv` : convolution with submultiplicative seminorms, commutative, associative,
  unital.

## Remaining cards and what each needs

1. `deninger-balanced-word-height-bar-strict-contraction` — entire word-height **tensor** algebra
   on `Σ r, Fin r → DeningerLattice` with weights `H(w)^k (k+1)^{|w|}`; bar faces, extra
   degeneracy, character sectors, split strict exactness.
2. `deninger-linearized-milnor-first-sullivan-strict-primitive` — same word algebra plus the
   alternating projector, `Λ̂²E`, the `(2, r-2)` Hopf coproduct component and `μ∘Δ = C(r,2)·id`.
3. `deninger-euler-depleted-meyer-periodization-extension` — `S_exp(ℝ)`, translation `τ_L`,
   `Δ_p = 1 - τ_L`, strict nuclear extension, zero-periodization sector.
4. `deninger-cofinal-prime-periodization-tomography-instability` — cofinal tomography, nonclosed
   range, compact-orbit weight-zero no-go.
5. `deninger-half-density-floquet-euler-boundary-dichotomy` — half-density Floquet trace, all-prime
   Hilbert energy, Neumann inverse, leakage scalar `1 - p^{-1/2}`.
6. `deninger-cofinal-floquet-secondary-poisson-graph` — full-circle half-density lift, radical =
   reflected Calderón graph.
7. `deninger-critical-floquet-von-mangoldt-renormalization-wall` — diagonal subtraction, von
   Mangoldt autocorrelation, sign wall.
8. `deninger-mobius-fourier-commutator-poisson-kernel` — `𝔖_μ`, `ker 𝔖_μ = Z(H_∩)`, Fourier
   covariance, causal von Mangoldt anomaly. Needs the corpus's unconditional Mertens rate
   `exists_norm_sum_moebius_kappa_two_rate` (`RHTower/Sieve/MoebiusSharpKappaTwo.lean`) only
   through `∫_1^∞ |M(T)|/T² dT < ∞`.
9. `deninger-euler-gamma-mobius-connection-transgression` — all-prime Euler connection, strict
   PNT endpoint, Green–Stokes law.
10. `deninger-source-poisson-chain-lift-obstruction` — needs (8) above; then the TFAE is
    formal.
11. `deninger-algebraic-cyclotomic-milnor-amplitude` — headline `(1)` `K_q^M(F)⊗ℝ = 0` for
    `F/ℚ` algebraic, `q ≥ 2`. This is Bass–Tate + Garland/Borel; **the only genuinely
    research-scale gate in the folder.**
12. `deninger-derived-rank-quotient-universal-property` — `E_∞`/∞-category statements.
13. `deninger-pro-log-stein-kummer-residue-square` — log de Rham/coherent sheaves.
14. `deninger-selective-positive-cell-h0-preservation` — Milnor–Witt sheaves.
15. `deninger-strict-pro-log-collar-trace-kernel` — coherent sheaves and log de Rham complexes.

## Gates

- [x] 2 of 17 cards promoted
- [ ] entire word-height algebra built (unlocks cards 1 and 2)
- [ ] `S_exp(ℝ)` layer built (unlocks cards 3--7)
- [ ] Möbius–Fourier commutator built (unlocks cards 8--10)
- [ ] remaining five cards

## Log

- 2026-08-10 — Swept the folder, promoted `deninger-cross-prime-closed-relation-saturation` and
  `deninger-prime-log-height-kothe-calderon-source`, and built the reusable Köthe completeness,
  density, multiplier and convolution layers listed above.
