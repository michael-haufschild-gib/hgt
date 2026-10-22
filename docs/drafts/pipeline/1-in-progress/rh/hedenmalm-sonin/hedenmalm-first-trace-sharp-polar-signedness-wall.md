# Hedenmalm first-trace sharp-polar signedness wall

- **Label:** `P-G142`
- **Route:** P
- **Parents:** `P-G139`, `P-G140`, `P-G141`,
  `bounded-variation-prime-window-divisor-tomography`
- **Stage:** 1-in-progress
- **Type:** heavy-conjecture loop / constructive polar finite part / positive-cone audit
- **Status:** `[PROVED IN LEAN] [SCALAR POLAR PASSIVITY FALSIFIED] [NOT RH]`

## Conjecture

Apply corpus's canonical sharp moving-window polar counterterm to P-G139 valuation-one current.
Higher valuations are analytic on shifted half-plane and should be removable without changing
punctured regularity. This should yield one closed first-trace-only observable whose regularity is
exactly RH.

Positivity may fail: polar square-root coefficient lives on all integer scales while prime channel
is subtracted. Test canonical dyadic coefficient at exact first finite samples, not asymptotically.

## Gates

### P-G142.A — exact first-trace polar weld

Define

```text
F_L(a)=4(1-exp(-L/2)) zeta(a-1/2)
       -2 A_L(a-1) firstTraceCurrent(a-1/2).
```

Prove full sharp polar observable is `F_L` plus analytic higher-valuation correction on `Re(a)>1`.

### P-G142.B — closed regularity criterion

Prove `RH ↔ F_L` has finite punctured limit at every `Re(a)>1`, then specialize unconditionally to
`L=log 2`.

### P-G142.C — coefficient cone audit

For literal dyadic sharp prime-polar coefficient prove exact positive and negative finite samples.
This decides whether canonical renormalization preserves atomic passivity.

### P-G142.D — pivot

If signed, retire scalar polar finite part as positivity producer. Positive survivor must retain
cross-scale interaction before scalarization; mere analytic regularity is exactly RH and creates no
sign.

## Non-theatre gate

Card requires closed Lean RH-equivalence for source-only first-trace polar observable and closed
finite signedness witness for literal coefficient. Algebraic relabeling alone does not pass.

## Lean outcome

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmFirstTraceSharpPolarSignednessWall.lean`.

Closed results:

1. Defined canonical sharp polar observable using only P-G139 continued valuation-one current.
2. Full sharp prime-polar observable equals this first-trace observable plus explicit
   higher-valuation tail.
3. Tail is analytic on `Re(a-1/2)>1/2`, so first-trace observable has finite punctured limits at
   every `Re(a)>1` iff RH.
4. Concrete dyadic specialization has no width premise and is exactly RH-equivalent.
5. Literal dyadic coefficient is strictly positive at `n=1` and strictly negative at `n=3`.
   Canonical scalar polar finite part is therefore signed before any limiting process.

This complements P-G141 rather than duplicating it. P-G141's covariant moving-horizon
renormalization remains coefficientwise positive and summable but becomes reflection-even after
squaring. P-G142 proves canonical scalar alternative retains divisor regularity but destroys
positive cone. Two branches meet exact regularization trilemma:

```text
covariant energy: positive + finite, orientation lost;
sharp scalar finite part: divisor-faithful + finite, positivity lost.
```

Only surviving shape is oriented linear covariant transport before energy scalarization.

## Progress

- [x] 0 → 1: conjecture fixed from P-G140 survivor and prior sharp-window corpus
- [x] 1 → 2: Lean proof and sharp positivity falsifier
- [x] 2 → 3: exact build, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## Honest boundary

An RH-equivalent regularity criterion does not prove RH. If coefficient is signed, result is a
sharp no-go: canonical finite part solves divergence by leaving positive cone.

## Log

- 2026-08-13 — opened after P-G140 proved positive Stokes moment nonsummable and corpus audit found
  canonical sharp polar counterterm plus exclusion-free regularity equivalence.
- 2026-08-13 — relabelled P-G142 after concurrent P-G141 covariant-renormalization module appeared
  and was audited. First-trace-only sharp polar RH criterion and finite signedness witness closed in
  Lean. Direct elaboration and exact module build passed (`12420/12420`). Axiom audit: only
  `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Full repository lint remains blocked
  by unrelated concurrently added unwired modules; this module is reachable and targeted scan is
  clean.
