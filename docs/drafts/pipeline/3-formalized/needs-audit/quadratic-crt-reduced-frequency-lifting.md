# Quadratic CRT reduced-frequency lifting

- **ID:** `quadratic-crt-reduced-frequency-lifting`
- **Stage:** 3-formalized
- **Type:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [FINITE HARMONIC-INCIDENCE THEOREM]`
- **Statement:** For coprime positive moduli `q,d` and arbitrary integers `a,h`, the reducible
  quadratic root sum satisfies `S_(qd,h)(ad)=nu_h(d)S_(q,h)(a)`.

## Proof

CRT identifies `R_(qd,h)` with `R_(q,h) x R_(d,h)`.  At frequency `ad`, the standard character
`exp(2 pi i ad r/(qd))` is `exp(2 pi i a r_q/q)` and is therefore constant on the `d`-root
coordinate.  Summing that constant over the second coordinate multiplies the `q`-root response by
`#R_(d,h)=nu_h(d)`.  No relation between `a` and `q`, or between `h` and either modulus, is used.

## Hostile audit

- `d=1` gives the identity map and root count one.
- primes shared with `h` merely reduce the complementary root count.
- `a=0` gives root-count multiplicativity.
- nonprimitive `a/q` is allowed, so the theorem is stronger than the primitive-frequency form
  from which it was conjectured.
- the theorem is an exact finite identity, not an estimate and not an RH conclusion.

## Gates

- [x] 0 -> 1: exact claim and edge attacks fixed
- [x] 1 -> 2: CRT character proof dependency-closed
- [x] 2 -> 3: Lean theorem `quadraticCongruenceRootSum_mul_alias` in
  `ReducedFrequencyMobiusAliasCollapse.lean`; narrow build passes and `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`
- [ ] scientific-priority audit
