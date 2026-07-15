# Gamma reflection charge-conjugation core

- **ID:** `gamma-reflection-charge-conjugation-core`
- **Stage:** 3-formalized
- **Type:** FORMALIZATION
- **Scientific status:** `[FORMALIZATION]` of a `[NOVELTY UNVERIFIED]` paper theorem
- **Paper theorem:** `gamma-reflection-charge-conjugation-doubling`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ReflectedOrbitCharge`
- **Cohomological successor:** `gamma-reflection-tate-anomaly-core`

## Formalized surface

For every involution `r` of a label set and every additive commutative coefficient group, the
module defines reflected charge, charge conjugation, oriented positive/negative charge, and
reflection-neutral pair creation. It proves:

```text
(qPlus,qMinus)
  =(orientedCharge(qPlus,qMinus),0)+(r(qMinus),qMinus),     (1)
```

and the complete equivalence

```text
orientedCharge(pPlus,pMinus)=orientedCharge(qPlus,qMinus)
iff
(pPlus-qPlus,pMinus-qMinus)=(r(g),g) for some finite g.    (2)
```

Thus oriented charge is not only invariant under reflected neutral-pair creation; it is the exact
quotient invariant.

For integral coefficients it also proves:

```text
chargeConjugate(q)=q and q!=0
  => exists i, r(i)!=i and q(r(i))=-q(i)!=0
  => 2 <= |support(q)|.                                   (3)
```

Every free two-cycle has the explicit conjugation-symmetric witness

```text
a e_i-a e_(r(i)).                                         (4)
```

## Deliberate analytic boundary

The paper theorem applies `(1)--(4)` to Gamma shift-orbit charges. Euler reflection converts each
negative-slope Gamma factor into the inverse positive-slope factor on the reflected orbit times a
DA affine-sine gauge. The Lean module formalizes the new quotient and doubling topology; it does
not postulate analytic Gamma reduction as an axiom.

## Physical/topological meaning

The theorem is a literal finitely supported charge lattice with a conjugation involution. Local
recurrence gauges are already quotiented by the orbit exact sequence; reflected neutral pairs form
the next gauge relation. A symmetric nonvacuum sector is necessarily doubled and the bound is
sharp. No quantum dynamics or statistics is asserted.

## RH impact audit

The core supplies a check on reflection-symmetric archimedean models: a one-orbit nonzero charge
cannot be self-dual. Completed `L`-functions include a non-Gamma Euler factor, so the core alone
does not constrain their zero divisor or prove any RH statement.

## Verification

The previously missing exact-module object was built with
`+GaloisForLFunctions.HTGeometry.ReflectedOrbitCharge`; the first attempt exposed proof gaps and the
corrected leaf build passed. The touched source then passed direct elaboration. A separate scratch
axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`. No umbrella, theorem-area,
full, or self-concurrent build was run.

## Gates

- [x] charge conjugation is involutive
- [x] exact oriented normal form
- [x] same-charge iff reflected neutral-pair difference
- [x] fixed-label charge vanishing over `Z`
- [x] sharp support-doubling theorem
- [ ] analytic Gamma quotient in Lean
