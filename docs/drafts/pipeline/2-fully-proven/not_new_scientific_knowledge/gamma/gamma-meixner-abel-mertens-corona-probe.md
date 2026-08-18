# Gamma--Meixner Abel kernels detect the actual Mertens corona class

- **ID:** `gamma-meixner-abel-mertens-corona-probe`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / HT SOURCE-TOPOLOGY BRIDGE
- **Scientific status:** `[PROVED HERE] [NOT FORMALIZED] [BRIDGE]
  [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parents:**
  - `../new_scientific_knowledge/weighted-euler-tangent-global-graph-decoupling.md`
  - `archimedean-meixner-root-seam-scale.md`
- **Statement:** The Gamma--Meixner shape kernels form a uniformly bounded Abel family on the
  logarithmic Marcinkiewicz prime field.  They vanish asymptotically on the complete
  finite-gauge/vanishing-tail layer and take limiting value one on the actual Euler unit field.
  Thus positive Gamma shape approaches the precise Mertens corona class left by the HT joint-graph
  no-go; it is a source-boundary probe, not a flow on zeta or Xi.

## Source boundary

Let

```text
||b||_M
 =sup_(X>=2) 1/log X * sum_(p<=X) (log p)/p |b_p|,        (1)
```

let `M_log` be the corresponding prime-field space, and let `M_0` be the closure of finite-support
fields.  The actual Euler unit field

```text
one_p=1                                                     (2)
```

lies in `M_log` but not in `M_0`; its quotient class `[one]` in
`Q_log=M_log/M_0` is the exact continuous coefficient datum surviving finite Euler gauges.

For `theta>0`, put

```text
w_theta(p)=cosh(2log p)^(-theta/2)                         (3)
```

and define the normalized Gamma-shape Abel functional

```text
L_theta(b)
 =theta * sum_p (log p)/p * w_theta(p) * b_p.             (4)
```

## Exact prime asymptotic

The shape kernel has the exact factorization

```text
w_theta(p)
 =2^(theta/2) p^(-theta) (1+p^(-4))^(-theta/2).           (5)
```

For `0<theta<=1`, this is bounded above by `sqrt(2)p^(-theta)`.  Moreover,

```text
sup_p |w_theta(p)/p^(-theta)-1|=O(theta)                  (6)
```

as `theta` tends to zero, because the logarithm of the ratio in `(5)` is uniformly `O(theta)`.

## Uniform boundedness on the source field

For `b in M_log`, write

```text
A_b(X)=sum_(p<=X)(log p)/p |b_p| <= ||b||_M log X.         (7)
```

Partial summation with `X=exp(t)` gives, uniformly for `0<theta<=1`,

```text
theta * sum_p (log p)/p p^(-theta)|b_p|
 <=C ||b||_M.                                             (8)
```

Indeed, after the finite lower endpoint, the right side is bounded by a constant multiple of

```text
theta^2 integral_0^infinity exp(-theta t)t dt=1.           (9)
```

Equations `(5)` and `(8)` prove

```text
sup_(0<theta<=1)||L_theta||_(M_log^*)<infinity.            (10)
```

## Corona extraction theorem

For every finite-support field `c`, equation `(4)` gives `L_theta(c)->0`.  Uniform boundedness
`(10)` and density therefore imply

```text
L_theta(b)->0                 for every b in M_0.          (11)
```

On the actual unit field, the prime number theorem, equivalently the pole of `-zeta'/zeta` at
one with the uniformly convergent prime-power tail removed, gives

```text
theta * sum_p (log p)p^(-1-theta) ->1.                   (12)
```

The uniform comparison `(6)` then yields

```text
L_theta(one)->1.                                         (13)
```

Consequently, for every `b in M_0`,

```text
L_theta(one+b)->1.                                       (14)
```

Every weak-star cluster point of `(L_theta)` annihilates `M_0` and evaluates `[one]` as one.  The
Gamma--Meixner Abel family therefore gives a canonical approximate dual probe of the actual
Mertens corona coset `one+M_0`.

The family need not converge on all of `Q_log`; no such claim is required.  It also does not
converge to `one` in the `M_log` norm.  In fact, for every fixed positive `theta`, `w_theta` lies in
the vanishing-tail layer, while `one-w_theta` retains nonzero corona norm.  The boundary passage is
genuinely singular.

## Positive meaning of the joint-graph no-go

The weighted Euler joint-graph theorem rules out every continuous RH selector on the entire
vanishing-tail coefficient layer jointly with the regular strip germ.  Its positive residue was
the quotient class `[one]`.  Equations `(10)`--`(14)` now supply an explicit analytic probe of
that residue:

```text
positive Gamma shape  -> continuous vanishing-tail observation;
theta down to zero    -> the actual nonsummable Mertens corona class.        (15)
```

This explains why a viable Gamma-shape RH trace must be a singular boundary incidence coupling
`[one]` to the completed divisor.  A theorem at one fixed positive shape can be changed freely by
the dense finite Euler graph and cannot orient RH by continuity alone.

## Relation to the Xi positive shape trace

The Xi seam trace

```text
G_Xi(theta)=sum_p A_p w_theta(p)                          (16)
```

uses the same Abel family but applies it to a quadratic FE--Schwarz anomaly.  Its exact convergence
boundary is the maximal horizontal Xi displacement.  Thus `(16)` is naturally interpreted as a
second-order corona susceptibility.  This interpretation does not prove its extension to every
positive shape: the missing theorem is precisely a source-defined quadratic pairing between the
Mertens corona class and the reflected divisor anomaly.

## Parent-theory boundary

Abel--Cesaro transfer, partial summation, the prime number theorem, and weak-star cluster points of
bounded dual families are classical.  The project-specific content is the exact collision of the
Gamma--Meixner kernel with the already isolated Mertens source quotient.  That collision is a
useful bridge but does not clear the novelty gate.

## Gates

- [x] exact factorization of the Gamma--Meixner prime kernel
- [x] uniform dual bound on `M_log`
- [x] vanishing on `M_0`
- [x] unit limit on the actual Euler source
- [x] singular, non-norm-convergent boundary identified
- [x] interpretation as the positive residue of the joint-graph no-go
- [ ] formalize only if a later source-incidence theorem consumes this Abel family
