# The unavoidable additive fork above the two-element multiplicative core

- **ID:** field-one-additive-fork
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[BRIDGE] [PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Depends on:** `field-one-multiplicative-core`
- **Statement:** Let `R` be a nontrivial semiring whose every element is
  either `0` or `1`. Exactly one of the following holds:
  1. `1+1=0`, and every element satisfies `x+x=0`;
  2. `1+1=1`, and addition is idempotent: `x+x=x`.

## Goal

Classify every total additive enhancement on the two-element multiplicative
core. This tests whether addition can be added to `{0,1}` without making a
doctrinal choice.

## Complete paper proof

Apply the two-element hypothesis to `1+1`. It gives

`1+1=0` or `1+1=1`.

These alternatives are disjoint: if both held, transitivity would give
`0=1`, contradicting nontriviality.

Suppose first that `1+1=0`. For arbitrary `x`, the two-element hypothesis
gives `x=0` or `x=1`. In the first case `x+x=0+0=0`; in the second,
`x+x=1+1=0`. Thus every element is its own additive inverse. This is the
characteristic-two branch represented on the two-element carrier by
`F₂`.

Suppose instead that `1+1=1`. Again split `x=0` or `x=1`. The zero case gives
`x+x=0=x`; the one case gives `x+x=1=x`. Thus addition is idempotent. This is
the Boolean branch.

Therefore every total semiring addition on the two-element multiplicative
core chooses exactly one of two incompatible branches. ∎

## Hostile audit

1. **Canonical addition on `F₁` — `FALSE`.** Multiplication and the carrier do
   not select between characteristic-two and idempotent addition.
2. **`F₁` as `F₂` — `FALSE`.** The characteristic-two branch is an additive
   enhancement with `1+1=0`; it is not the addition-free initial pointed
   monoid.
3. **`F₁` as the Boolean semiring — `FALSE`.** The Boolean branch is useful
   for tropical/idempotent geometry but chooses `1+1=1`.
4. **Third total addition — `FALSE`.** The value of `1+1` exhausts the
   two-element carrier, and the two branches force all sums.
5. **Partial/relational addition excluded — `FALSE`.** Blueprints, bands,
   hyperrings, and pastures evade this theorem by weakening total single-valued
   addition. That is the positive escape route.

**Verdict:** `REDISCOVERED` / `BRIDGE`. Elementary, but it supplies the exact
no-go boundary needed by the method-neutral construction.

## Gates

- [x] 0 → 1: claim typed and separated from partial/relational addition.
- [x] 1 → 2: dependency-closed proof and hostile audit complete.
- [x] 2 → 3: exact Lean theorem package and axiom audit complete.
- [ ] 3 → 4: publication-ready extraction.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FieldOneMultiplicativeCore`
- **Theorems:** `twoElement_additiveFork`,
  `twoElement_additiveFork_disjoint`
- **Audit:** direct `lake env lean` and final targeted `lake build` passed;
  `#print axioms` reports only standard Lean principles.

## No-go closure

- **Exact killing theorem:** no total semiring addition on `{0,1}` is
  doctrine-neutral.
- **Strongest positive survivor:** all total additions are classified by one
  bit, while partial/relational addition remains available as a third design
  axis rather than a third total operation.
- **Status:** survivor is `[PAPER-PROVED] [LEAN-FORMALIZED]`.

## Log

- 2026-07-26 — conjectured as an additive no-go; hostile audit exposed the
  positive two-branch classification; paper proof closed.
- 2026-07-26 — formalized unconditionally; targeted build, axiom audit, and
  project lint passed; integrated into the doctrine atlas.
