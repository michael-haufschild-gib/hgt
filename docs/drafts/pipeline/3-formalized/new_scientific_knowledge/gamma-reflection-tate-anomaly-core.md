# Gamma reflection Tate-anomaly core

- **ID:** `gamma-reflection-tate-anomaly-core`
- **Stage:** 3-formalized
- **Type:** FORMALIZATION
- **Scientific status:** `[FORMALIZATION]` of a `[NOVELTY UNVERIFIED]` paper theorem
- **Paper theorem:** `gamma-dihedral-orbifold-bulk-mirror-anomaly`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ReflectionTateAnomaly`

## Formalized theorem

For an involutive equivalence `r` on any linearly ordered label set, let the signed reflection act
on finite integer charge vectors by `C(q)=-r(q)`. The module defines:

```text
TateCocycle(q)       : r(q)=q,
TateBoundary(g)      : g+r(g),
Cohomologous(p,q)    : p-q=TateBoundary(g) for some g.     (1)
```

It constructs an explicit finite primitive and proves the complete criterion

```text
q is a boundary
iff every fixed-label coefficient q(i) is even,            (2)
```

and its two-object form

```text
p and q are cohomologous
iff p(i)-q(i) is even at every fixed label.                (3)
```

Thus parity at the fixed set is the complete degree-one invariant. The local phase is certified by

```text
fixed unit       -> not a boundary;
twice fixed unit -> a boundary;
free equal pair  -> a boundary.                            (4)
```

At paper level, `(2)--(3)` identify the cohomology canonically with the finitely supported
`Z/2`-valued functions on the fixed-label set, equivalently its compactly supported
zero-homology. The Lean theorem supplies the complete representative-level equivalence test without
introducing an abstract quotient type.

## Deliberate paper boundary

The paper applies `(2)--(4)` to the Gamma charge lattice. Its affine reflection on `C/(H Z)` has
exactly two fixed labels, giving `(Z/2)^2`. The Lean module does not build the analytic quotient
type `C/(H Z)` or an abstract group-cohomology quotient; instead it proves the stronger explicit
equivalence test for every finitely supported representative.

## Physical/topological meaning

Ordinary conjugation-fixed charges avoid the mirror set and occur in opposite-charge pairs. The
degree-one twist cohomology does the complementary thing: free pairs contract, while parity
survives only at fixed labels. This is a literal fixed-locus localization theorem for finite
charge, without a physical dynamics claim.

## RH impact audit

At unit scale and center `1`, the paper fixed labels are the integer and half-integer Gamma shifts.
The formal core supplies the parity classifier but does not identify it with an `L`-function root
number, epsilon factor, zero parity, or RH criterion.

## Verification

The missing module was built once with
`+GaloisForLFunctions.HTGeometry.ReflectionTateAnomaly`, followed by direct source elaboration. A
separate scratch axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. No
umbrella, theorem-area, full, or self-concurrent build was run.

## Gates

- [x] explicit finite primitive
- [x] boundary iff fixed parity is zero
- [x] cohomology equivalence iff fixed parities agree
- [x] order-two fixed-label generator
- [x] free-pair contraction
- [ ] analytic two-fixed-label quotient in Lean
