# Cofinal Gamma Bockstein all-order Schatten wall

- **Stage:** 3-formalized
- **Type:** exact classification / positive survivor
- **Formal module:** `GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinSchattenWall.lean`

## Theorem

For an ordinary prime `p`, define

```text
F_t(p)=p^t p/(p+1)^2,
Delta_t(p)=F_(-t)(p)-F_t(p).
```

For every `t in R` and `q>0`,

```text
sum_p |Delta_t(p)|^q < infinity
  <-> t=0 or q(1-|t|)>1.                         (1)
```

Therefore, without a strip hypothesis,

```text
Delta_t in intersection_(q>1) ell^q(P) <-> t=0. (2)
```

## Proof

Reflection and monotonicity reduce the magnitude to `u=|t|`:

```text
|Delta_t(p)|=F_u(p)(1-p^(-2u)).
```

When `t!=0`, `u>0`.  For every ordinary prime `p>=2`,

```text
(1/4)(1-2^(-2u)) p^(u-1)
  <= |Delta_t(p)|
  <= p^(u-1).
```

The lower coefficient is positive.  Raising to `q>0` compares the series above and below with
positive constant multiples of `sum_p p^(-q(1-u))`.  The prime-power convergence criterion gives
exactly `q(1-u)>1`, proving (1).  If `0<u<1`, order `q=(1-u)^(-1)>1` is on the divergent boundary;
if `u>=1`, order `q=2` diverges.  Thus all orders above one occur only at `t=0`, proving (2).

## Frontier consequence

The all-order ideal is a complete reader for the cofinal Gamma grade, not a producer.  Any source
construction which independently lands the explicit physical Bockstein in every `ell^q`, `q>1`,
annihilates it and forces neutral grade.  Conversely, no ambient strip-wide all-order landing can
exist: (2) would force every strip parameter to have grade zero.

## Lean audit surface

- `primeGammaCofinalBocksteinMagnitude_bounds`
- `summable_primeGammaCofinalBocksteinSchattenMass_iff`
- `all_order_summable_primeGammaCofinalBocksteinSchattenMass_iff`

Proofs are unconditional and contain no `sorry`, `admit`, local axiom, opaque declaration, or
unsafe declaration.
