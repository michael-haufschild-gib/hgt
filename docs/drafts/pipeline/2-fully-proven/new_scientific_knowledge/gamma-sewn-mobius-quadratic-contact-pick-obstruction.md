# Gamma-sewn Möbius quadratic-contact Pick obstruction

- **ID:** `gamma-sewn-mobius-quadratic-contact-pick-obstruction`
- **Stage:** 2-fully-proven
- **Type:** CCM SOURCE NO-GO / POSITIVE SUCCESSOR
- **Scientific status:** `[UNCONDITIONAL PAPER PROOF] [SOURCE-SPECIFIC NOVELTY CANDIDATE]`
  `[CLASSICAL UNIVERSAL PARENT] [NOT RH]`
- **Live card:** `../../1-in-progress/gamma-sewn-mobius-quadratic-contact-pick-obstruction.md`
- **Formal certificate:** `../../3-formalized/new_scientific_knowledge/gamma-sewn-mobius-quadratic-contact-pick-obstruction.md`

## Theorem

For functions `c,q` approaching `1` along an arbitrary filter, assume

```text
(1-c^2)/(1-q^2) -> 0.
```

Against fixed `c_0 != 1`, `q_0 != 1`, the normalized two-point Pick determinant

```text
[(1-c_0^2)/(1-q_0^2)] [(1-c^2)/(1-q^2)]
  - [(1-c_0 c)/(1-q_0 q)]^2
```

converges to the strictly negative square

```text
-[(1-c_0)/(1-q_0)]^2.
```

It is therefore eventually negative.

For every prime `p`, the actual Gamma-sewn Möbius multiplier has exact quadratic loss at the
lossless zero-aperture boundary, so its normalized diagonal defect tends to zero. Hence, against
every fixed aperture `x_0>0`, every sufficiently small positive aperture `x` gives a negative
two-point determinant. Exact source algebra proves that the determinant of the actual fixed-prime
Möbius aperture Gram loss equals this normalized determinant times a strictly positive factor.
The actual scalar-sewn source loss is therefore indefinite.

## Proof

First diagonal product tends to zero. Cross quotient tends to
`(1-c_0)/(1-q_0)`, which is nonzero. This proves universal limit and eventual negativity.
For source instance, exact quadratic-contact identity factors diagonal defect as

```text
(1-q) g (1+c)/(1+q),
```

which tends to zero because `q,c->1` and `g` is continuous. Substitution into universal theorem
and exact Szego-metric factorization complete proof.

## Scope and positive survivor

This rules out fixed-prime scalar Gamma sewing as provider of complete CCM aperture passivity.
It does not rule out non-diagonal mixing. Any surviving completion must mix prime, valuation-depth,
or Gamma-boundary channels before scalar trace, thereby retaining a nonzero first-order boundary
channel.

Universal theorem is classical in mechanism (Julia--Caratheodory). Current novelty candidate is
exact CCM source instantiation and its Gram-determinant connector; no priority claim is made.
