# Spherical stalk base change is not arithmetic localization

- **ID:** `field-one-spherical-localization-base-change-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO / POSITIVE SURVIVOR
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-relative-picard-hodge-passivity`
- **Statement:** ordinary integral base change of a spherical monoid stalk cannot be the
  arithmetic localization \(\mathbb Z[1/p]\).

## Goal

At a prime \(p\), Connes--Consani's absolute spherical stalk is
\[
  \mathbb F_1[T^{\mathbb Z[1/p]_+}].
\]
Ordinary base change from \(\mathbb F_1\) to \(\mathbb Z\) produces the additive monoid algebra
\[
  \mathbb Z[\mathbb Z[1/p]_+],
\]
not \(\mathbb Z[1/p]\).  Prove an invariant which prevents conflating them.

## Theorem

`[PAPER-PROVED]` Let \(M\) be any additive monoid and let \(p\geq2\).  Write
\(\iota_M:\mathbb Z\to\mathbb Z[M]\) for the coefficient map.  Then
\[
  \iota_M(p)
\]
is not a unit in \(\mathbb Z[M]\).

By contrast, the image of \(p\) is a unit in the localization \(\mathbb Z[1/p]\).  Therefore there
is no \(\mathbb Z\)-algebra isomorphism
\[
  \mathbb Z[M]\simeq_{\mathbb Z}\mathbb Z[1/p].
\]
In particular this applies to \(M=\mathbb Z[1/p]_+\).

## Proof

The augmentation
\[
  \varepsilon:\mathbb Z[M]\longrightarrow\mathbb Z,\qquad
  \sum_{m\in M}a_mT^m\longmapsto\sum_{m\in M}a_m
\]
is a unital ring homomorphism and satisfies
\(\varepsilon(\iota_M(n))=n\) for every \(n\in\mathbb Z\).

If \(\iota_M(p)\) were a unit, its image \(p\) under \(\varepsilon\) would be a unit in
\(\mathbb Z\).  The only units of \(\mathbb Z\) are \(\pm1\), contradicting \(p\geq2\).  Hence
\(\iota_M(p)\) is not a unit.

In \(\mathbb Z[1/p]\), \(p\) is inverted by definition.  A \(\mathbb Z\)-algebra isomorphism
preserves the image of every scalar and preserves/refects units.  It would therefore send the
nonunit \(\iota_M(p)\) to the unit \(p\), impossible.

## No-go closure

- **Exact killing theorem:** ordinary scalar extension of
  \(\mathbb F_1[T^M]\) retains integer \(p\) as a nonunit, while arithmetic localization inverts
  it.
- **Strongest positive survivor:** any comparison from absolute spherical stalk to arithmetic
  localization must use an evaluation, localization, completion, or point functor in addition to
  scalar extension.
- **Constructed survivor:** augmentation followed by localization gives a canonical comparison
  \[
    \mathbb Z[M]\longrightarrow\mathbb Z[1/p].
  \]
  Every monomial \(T^m\) maps to \(1\), and this map is noninjective whenever \(M\) contains two
  distinct elements.
- **New insight:** this canonical comparison is maximally lossy on monomials. A
  Frobenius-faithful comparison must retain exponent data on a separate branch rather than factor
  solely through augmentation.
- **Status:** dependency-closed paper proof and unconditional Lean formalization complete.

## Gates

- [x] 0 → 1: exact well-typed claim and source application
- [x] 1 → 2: dependency-closed proof above
- [x] 2 → 3: Lean theorem and axiom audit
- [ ] 3 → 4: publication-ready integration

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FieldOneSphericalLocalizationNoGo`
- **Definitions:** `integralMonoidAugmentation`, `augmentedAwayComparison`
- **Theorems:** `integralScalar_nonunit_in_addMonoidAlgebra`,
  `integralScalar_isUnit_in_away`, `augmentedAwayComparison_of`,
  `augmentedAwayComparison_identifies_monomials`,
  `augmentedAwayComparison_not_injective`, `addMonoidAlgebra_not_algEquiv_away`
- **Audit:** direct `lake env lean` passed. Exact proof replica under `#print axioms` reports
  only standard Lean principles `propext`, `Classical.choice`, and `Quot.sound`. Final targeted
  module build remains reserved for final audit.

## Log

- 2026-07-26 — Extracted from hostile audit of RP0.  No computation and no RH premise used.
- 2026-07-26 — Formalized for every additive monoid and every natural \(p\ge2\); direct leaf
  check and scratch axiom audit passed. Positive survivor returned to RP0.
