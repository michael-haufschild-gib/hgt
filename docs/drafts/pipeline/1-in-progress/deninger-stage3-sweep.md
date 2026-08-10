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
| `deninger-balanced-word-height-bar-strict-contraction` | `RHTower/DeningerWordHeight`, `DeningerBarWord`, `DeningerBarInsert`, `DeningerBarSlice`, `DeningerBarDifferential`, `DeningerBarUnit`, `DeningerBarContraction`, `DeningerBarSector`, `DeningerBarFace`, `DeningerBarInsertComm`, `DeningerBarFibre`, `DeningerBarSquareZero`, `DeningerBarAlgebra`, `DeningerBarPower` (all new) |

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

2. `deninger-linearized-milnor-first-sullivan-strict-primitive` — **in progress**.
   Done: clause 5, the set-indexed linearization — `RHTower/DeningerSetIndexedLinearization`
   (`deningerFreeEval`, `deningerLinearityRelations`, `deningerLinearizationEquiv`: the free
   module on the underlying set modulo the three linearity defects **is** the module).
   Done: clause 1's topological core — `RHTower/DeningerWordAlternating`
   (`deningerPermuteAt`, `deningerPermEquiv`, `deningerAlt`, `deningerBarSeminormR_alt_le`,
   `deningerPermuteAt_char`): permuting letters preserves length, product-of-letter-heights and
   total character, so the blockwise antisymmetrizer has seminorm at most one and `A₀` is its
   range — a closed complemented subspace of a complete nuclear space.
   Done: `(15)`--`(16)`, the normalized two-coproduct identity — `RHTower/DeningerExteriorPairSum`
   (`deningerPairPerm`, `deningerIotaMulti_pairPerm`, `deningerExteriorPairSum`,
   `deningerPairIndex_card`): summing the signed two-letter splittings of a wedge monomial over
   all ordered pairs gives `binom(r,2)` times the monomial.  No explicit shuffle sign is used —
   the permutation carries its own sign and it appears twice.

   Remaining, with the route already worked out — do not rediscover it:
   - The corpus already owns the algebraic first layer: `RHTower/DeningerRelativeSullivanMilnorResolution`
     has `deningerMilnorIdeal`, `deningerMilnorEpsilon(_ker)`, `deningerSullivanInclusion`,
     `deningerSullivanFirstDifferential`, `deningerSullivanFirstLayer`, and it already uses
     `V × ⋀[k]^2 V` as the linearized attachment.  Build on it; do not rebuild `A₁`.
   - `(11)`, `d h = id`: the terms of `h` are the `deningerExteriorPairSum` terms with the
     leading `ι(v i) * ι(v j)` replaced by the new generator `σ(v i ∧ v j)`; applying the
     first-layer differential returns exactly the `deningerExteriorPairSum` summands, so `(16)`
     gives `binom(r,2)` times the monomial and the normalisation `binom(r,2)⁻¹` closes it.
     What is still needed for this step is the **odd derivation** extending
     `deningerSullivanFirstDifferential` from the new generators to all of `A₁` — mathlib has no
     odd derivation on an exterior algebra, so build it (or state `d h = id` through the
     Leibniz rule on the specific two-block products, which is all the proof uses).
   - clause 4 reuses `deningerBarCharMul` verbatim (character multipliers already commute with
     everything built on the word source).
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

- [x] 3 of 17 cards promoted
- [x] entire word-height algebra built
- [x] `b² = 0` for the bar differential
- [ ] `S_exp(ℝ)` layer built (unlocks cards 3--7)
- [ ] Möbius–Fourier commutator built (unlocks cards 8--10)
- [ ] remaining five cards

## Log

- 2026-08-10 — Promoted `deninger-balanced-word-height-bar-strict-contraction`.  The alphabet
  `{1} ⊔ (Γ∖{0})` is `Γ` with the zero character as the unit; the fibre of the `j`-th face is then
  the pair of unit insertions at `j` and `j+1`.  `b² = 0` follows from the simplicial pairing
  `(j,j') ↦ (j'-1,j)` on double fibres, matched by `deningerInsertUnit_comm`.
- 2026-08-10 — Swept the folder, promoted `deninger-cross-prime-closed-relation-saturation` and
  `deninger-prime-log-height-kothe-calderon-source`, and built the reusable Köthe completeness,
  density, multiplier and convolution layers listed above.
