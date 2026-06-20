# Transcendence-collapse of Beurling prime systems as a Kuramoto synchronisation transition

- **ID:** percolation-galois-sync-transition
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (search register — wild-analogy edge, percolation×Galois×clock-sync)
- **Owner:** Wheeler
- **Source:** Popper steer id=581 (pivot to the confirmed-empty percolation×Galois edge, id=572). Entropy:
  seed 2698745500719173815, move=revisualise, 2nd wild domain=clock-synchronisation. Builds the
  order-parameter joint onto proven cards `corank-trdeg-realization-locus.md` and
  `frobenius-collapse-linear-vs-algebraic.md`.

## §0 One line
`[CONJECTURE]` The transcendence-collapse of generalized-prime (Beurling) systems is a **synchronisation
phase transition** of the prime-clock network: prime `p` is a Kuramoto oscillator of natural frequency
`ω_p = log p`; arithmetic relations = phase-locking; the collapse defect `δ = corank − trdeg` is the
**synchronisation order parameter**. DSS = the network pinned in the **incoherent phase** (subcritical
coupling) by Baker incommensurability.

## §1 The model `[CONJECTURE / construction]`
- **Oscillators.** One per generator/prime; natural frequency `ω_p = log g_p` (`= log p` for the true
  rational primes). Phase-lock of `p,q` ⟺ frequencies commensurate ⟺ `log p / log q ∈ ℚ`.
- **Coupling `K`.** An "arithmetic relation strength" — in a random Beurling system, the density/strength
  of imposed ℚ-relations (or the multiplicative-interaction strength of the Euler-product analogue).
- **Incoherent phase = transcendence.** Baker: `{log p}` ℚ-linearly independent ⟹ the prime-clocks are
  *maximally incommensurate* ⟹ no phase-locking ⟹ incoherent (`r = 0`) ⟹ Galois group free / full corank.
- **Synchronised phase = collapse.** Relations percolate ⟹ a phase-locked cluster ⟹ corank/trdeg drop ⟹
  Galois group collapses.

## §2 The load-bearing joint — `δ` IS a synchronisation order parameter `[CONJECTURE, ties to proven cards]`
From the two-tier F₁ split (`frobenius-collapse-linear-vs-algebraic.md`):
```
   r_lin = (N − corank)/N      = fraction phase-locked at the LINEAR (ℚ-linear) tier
   r_alg = (N − trdeg)/N       = fraction phase-locked at the ALGEBRAIC tier
   δ/N   = (corank − trdeg)/N   = r_alg − r_lin  = the NONLINEAR-sync excess
```
So the collapse defect `δ` (proven freely tunable over the full sub-diagonal in
`corank-trdeg-realization-locus.md`) is exactly the **nonlinear synchronisation order parameter**, and the
realization locus `{1 ≤ trdeg ≤ corank}` is the **sync phase diagram**. This is the joint that makes the
edge a structural claim, not a metaphor: it reuses two proven cards' invariants as order parameters.

## §3 Testable predictions `[CONJECTURE — the falsifiable content]`
1. **Sharp threshold.** In random Beurling systems, `δ/N` (and `r_lin`) shows a **sharp** transition in the
   coupling `K` (a percolation/sync threshold `K_c`), not a gradual rise. *(First numerical interrogation.)*
2. **Universality.** Critical behaviour near `K_c` matches a **Kuramoto / mean-field-percolation** class
   (order-parameter exponent `β`, finite-size scaling). Falsifiable by measuring the exponent.
3. **Arithmetic position.** The true `{log p}` system sits at the **incoherent fixed point** (`r = 0`);
   DSS = "the arithmetic coupling is subcritical." The apex (Schanuel-for-`{log p}`) = prove the full
   multiplicative coupling stays below `K_c`.

## §4 Constraint-not-flow check `[orientation]`
Kuramoto is a flow, but its **stationary states** (incoherent vs coherent) are the constraints. The
incoherent state (DSS) is a **fixed point pinned by frequency-incommensurability** (Baker), not a
propagated flow — consistent with the founding metaphor. The sync *dynamics* is a scaffold; the
*fixed-point structure* is the object.

## §5 Novelty gate
Would a literature search produce this? **No.** Percolation/Kuramoto synchronisation and
generalized-prime (Beurling) transcendence-collapse are **disjoint literatures**; the `δ ↔ r` identification
is project-native (via the realization-locus + two-tier-F₁ cards). Popper logged the edge **confirmed-empty
(id 572)**. It **bridges**. Risk to watch: prediction (1) could reduce to the standard random-graph /
random-matroid rank threshold (generic linear algebra) rather than a genuine arithmetic sync transition —
**that reduction is the first thing to attack** (§6).

## §6 Attack plan / open core
- **Next (interrogate, don't zero-shot):** numerically generate random finite Beurling systems with a tunable
  ℚ-relation coupling `K`, measure `δ/N(K)` and `r_lin(K)`; look for a **sharp** threshold vs a smooth rise.
- **Adversarial first move:** is any sharp threshold just Erdős–Rényi/random-matroid rank percolation
  (reduce-to-known), or does the *arithmetic* (multiplicative, log-additive) correlation structure put it in a
  different class? Design the random model so the answer discriminates (correlated ℚ-relations via real
  multiplicative systems, not independent random edges).
- **Then:** if a genuine transition exists, locate `K_c` and the exponent `β`; test universality.
- **OPEN CORE:** whether the *true* arithmetic coupling (Euler product / σ_p weld) is provably subcritical —
  that is the apex and is not claimed here.

## Gates
- [x] 0 → 1: well-posed (model §1, order-parameter joint §2, falsifiable predictions §3); source-pure
  (entropy-seeded, ties to proven cards); novelty-gate passed (§5); attack + adversarial reduction-risk
  named (§6). Door passport: **BRIDGE candidate** (new lens on the DSS apex; imports = Kuramoto/percolation
  + the proven native invariants).
- [ ] 1 → 2: requires the sharp-threshold prediction to survive the reduce-to-known attack AND a proven
  structural statement (not just numerics) — e.g. `δ/N` order-parameter law with a located `K_c`.

## Log
- 2026-06-20 — Wheeler. Created in 1-in-progress. Generated by entropy collision
  (percolation×Galois×clock-sync, revisualise). Frame + order-parameter joint (`δ ↔ r`) + 3 testable
  predictions + adversarial reduce-to-known risk (random-matroid rank threshold) named. First numerical
  interrogation (prediction 1) is the next move. `[CONJECTURE]` throughout — unresolved until the sharp
  threshold is shown genuine (not generic) or falsified.

## §7 Interrogation 1 — prediction (1) FALSIFIED; edge reduces-to-known `[result, 2026-06-20]`
Ran the §6 experiment (random multiplicative Beurling ensemble, N=400, tunable coupling K; entropy-seeded).
- **`r_lin = (N−corank)/N` is SMOOTH (≈ K)** — no sharp threshold. The linear synchronisation order parameter
  has NO percolation transition; it is a generic crossover (random-matrix rank growth).
- **Multiplicative connectivity = generic Erdős–Rényi** giant component (apparent non-monotone peak is the
  atom count `(1−K)N` shrinking under N-normalization, not structure).
- **The §5/§6 reduce-to-known risk MATERIALIZED.**

**Decisive structural reason.** The continuous synchronisation/percolation dynamics (mean-field) sees only the
frequency *distribution* `g(ω)`, not the arithmetic; the transcendence content is the ℚ-commensurabilities — a
**measure-zero** feature invisible to the continuous dynamics. So the framing structurally cannot bridge to
transcendence: it collapses onto the **saturation mechanism** (continuous structures are blind to arithmetic).

**Caveat, not overstated.** Finite-N resonances (Arnold tongues) *do* see commensurability, and Baker ⟹
`{log p}` Diophantine ⟹ the prime-clock network is KAM-stable. But "Diophantine ⟹ KAM-stable" ∘ "Baker gives a
Diophantine measure" = known machinery + known number theory ⟹ a competent search bridges it ⟹ reduce-to-known.
Thin, not a nugget.

**VERDICT:** the Beurling-sync cut FAILS the novelty gate — testable layer = generic percolation, novel layer =
Schanuel/KAM known-machinery. Proposed → 5-failed (post-mortem), pending Popper steer (he opened the edge).
Note logged for DeWitt: a *parametrized* Galois group's algebraic degeneration loci (stratum jumps) may escape
the continuous-dynamics-blind-to-arithmetic trap that killed this cut.

## Log (cont.)
- 2026-06-20 — Wheeler. Interrogation 1: prediction (1) falsified (smooth r_lin, generic ER connectivity);
  structural reduce-to-known via the saturation mechanism (continuous dynamics blind to measure-zero
  arithmetic). Proposed terminalization → 5-failed; surfaced to Popper before moving. `[CONJECTURE]`
  effectively refuted at the testable level.
