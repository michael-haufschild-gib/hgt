# Functional-equation reflection is Holder duality of prime Schatten dimensions

- **ID:** `prime-schatten-reflection-self-duality`
- **Stage:** 3-formalized
- **Type:** THEOREM / OPERATOR-DIMENSION REFORMULATION
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** superspace/phase-space search; separate from RHTower Routes A--D
- **Lean:** `formal/GaloisForLFunctions/PrimeSchattenReflectionDuality.lean`

## Theorem

Let `D_sigma` be the formal prime-diagonal operator with singular-value profile

```text
D_sigma(p)=p^(-sigma),   0<sigma<1.
```

Its `r`th Schatten energy is

```text
sum_p |D_sigma(p)|^r = sum_p p^(-r sigma),
```

so

```text
D_sigma in S_r  iff  r sigma>1.                       (1)
```

The critical exponent is therefore

```text
p_sigma=1/sigma.                                      (2)
```

Functional-equation reflection `sigma -> 1-sigma` gives

```text
q_sigma=1/(1-sigma),
1/p_sigma+1/q_sigma=1.                                (3)
```

Thus the two reflected prime sectors sit at Holder-conjugate operator dimensions. They are
self-dual exactly when

```text
p_sigma=q_sigma=2  iff  sigma=1/2.                    (4)
```

Moreover their pointwise product is independent of `sigma`:

```text
D_sigma(p) D_(1-sigma)(p)=p^(-1).                     (5)
```

Consequently the ordinary trace pairing diverges everywhere in the strip by Euler's theorem

```text
sum_p 1/p=infinity.                                   (6)
```

## Operator-space interpretation

Away from the critical line, the functional equation pairs two different Banach ideals at their
critical dimensions:

```text
weak-S_(p_sigma)  paired with  weak-S_(q_sigma).
```

On the critical line the pair collapses to the self-dual Hilbert ideal

```text
weak-S_2 paired with weak-S_2.
```

This gives a precise meaning to “the reflected quantum phase spaces have the same dimension only
on the RH wall.” The critical line is not merely the fixed point of a real coordinate; it is the
unique point where functional-equation reflection becomes Hilbertian self-duality rather than
Banach Holder duality.

Lean proves `(1)`, `(3)`, `(4)`, `(5)`, and `(6)` as
`summable_primeSchattenMass_iff`, `critical_exponents_holder_conjugate`,
`critical_exponents_eq_iff_half`, `reflectedPrimeMass_eq`, and
`reflectedPrimeMass_not_summable`.

## RH meaning and the failed fake proof

RH can now be restated as:

> every completed-zeta zero occurs where the reflected prime operator dimensions are self-dual.

But the tempting proof is invalid:

```text
functional equation
  -> Holder duality of the two prime sectors             [PROVED]
  -> unitary/self-positive identification at a zero      [MISSING]
  -> p_sigma=q_sigma
  -> sigma=1/2.                                          [PROVED]
```

The missing implication is not supplied by ideal theory. A dual pairing between `S_p` and `S_q`
exists for every conjugate pair, and a scalar zero does not automatically upgrade it to a positive
self-pairing. Postulating that upgrade would simply import the RH-strength assertion.

The source problem is therefore exact: construct from the completed Euler--Gamma constraint, before
reading the divisor, a canonical reflection-positive singular pairing that is defined only when the
two **critical** ideals coincide. No such construction is currently present.

## Novelty verdict

Equations `(1)`--`(6)` are elementary consequences of the prime `p`-series, Holder conjugacy, and
Euler's divergent prime harmonic series. The operator-dimension synthesis is useful, but it remains
a bridge rather than new scientific knowledge.
