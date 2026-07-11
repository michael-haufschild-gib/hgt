# The floor discrepancy and Möbius tail form one complementary shift incidence

- **ID:** `coupled-floor-mobius-complementary-shift-incidence-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Source:** `shifted-euler-error-floor-mobius-tail-coupling.md`;
  `mobius-channel-critical-mass-escape-law.md`
- **Statement:** After logarithmic change of variables, the floor-discrepancy and Möbius-tail
  pieces of the shifted Euler error are the lower and upper halves of one projection incidence.
  At the unique normalization which gives both halves the same arithmetic coefficient, the upper
  input is the constant boundary mode and is not in `L2`.  Thus the archimedean completion in a
  successful Hilbert--Pólya construction must act as a boundary renormalization of this exact
  complementary incidence.

## 1. Shift projections

Let

```text
H=L2(R_(>=0),dt),
(V_a f)(t)=1_(t>=a)f(t-a),
P_a=V_a V_a^*.                                           (1)
```

Then `P_a` is the orthogonal projection onto functions supported on `[a,infinity)`, so

```text
(P_a f)(t)=1_(t>=a)f(t),
((I-P_a)f)(t)=1_(t<a)f(t).                               (2)
```

For an integer `d>=1`, write

```text
P_d=P_(log d).                                            (3)
```

The two projections in `(2)` are exactly the incidence tests

```text
P_d: d<=e^t,
I-P_d: d>e^t.                                             (4)
```

## 2. Exact regularized incidence theorem

Fix `omega>0` and `delta>0`.  Put

```text
q_delta(t)=e^(-delta t),

k_(omega,delta)(t)
 =e^(-(1+omega+delta)t)R_omega(e^t),                     (5)
```

where

```text
R_omega(Y)
 =sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega).               (6)
```

Both vectors in `(5)` belong to `H`.  Then the normalized coupled error

```text
F_(omega,delta)(t)
 =e^(-(1+omega+delta)t)E_omega(e^t)                      (7)
```

has the exact `H` identity

```text
F_(omega,delta)
 =sum_(d>=1)mu(d)d^(-1-2omega)
   (
     d^(-delta)V_(log d)k_(omega,delta)
     -(1/(1+omega))(I-P_d)q_delta
   ).                                                     (8)
```

Both series in `(8)` converge absolutely in `H`.

### Proof

The floor part of the coupled error is

```text
sum_(d<=e^t)mu(d)d^(-omega)R_omega(e^t/d).               (9)
```

For `a=log d`, direct substitution in `(5)` gives

```text
mu(d)d^(-1-2omega-delta)V_a k_(omega,delta)
 =1_(d<=e^t)e^(-(1+omega+delta)t)
   mu(d)d^(-omega)R_omega(e^t/d).                        (10)
```

For the tail part, `(2)` and `(5)` give

```text
sum_(d>=1)mu(d)d^(-1-2omega)((I-P_d)q_delta)(t)
 =e^(-delta t)sum_(d>e^t)mu(d)d^(-1-2omega).             (11)
```

Multiplying the tail term

```text
-e^((1+omega)t)/(1+omega)
 sum_(d>e^t)mu(d)d^(-1-2omega)                           (12)
```

by the normalizing factor in `(7)` yields `-(1/(1+omega))` times `(11)`.  Equations
`(10)`--`(12)` prove `(8)`.

The standard bound

```text
R_omega(e^t)=O_omega(e^(omega t)+1)                      (13)
```

shows that `k_(omega,delta)` is in `H`; clearly `q_delta` is in `H`.  The coefficient sums are
bounded by

```text
sum_d d^(-1-2omega-delta),
sum_d d^(-1-2omega),                                     (14)
```

so the two vector series converge absolutely.

## 3. The common-coefficient boundary incidence

Let `delta` decrease formally to zero.  Equation `(8)` becomes the pointwise locally
finite/absolutely convergent identity

```text
e^(-(1+omega)t)E_omega(e^t)
 =sum_(d>=1)mu(d)d^(-1-2omega)
   (
     V_(log d)k_(omega,0)
     -(1/(1+omega))(I-P_d)1
   ),                                                     (15)
```

where

```text
k_(omega,0)(t)=e^(-(1+omega)t)R_omega(e^t).              (16)
```

At this normalization, and only at this normalization within the exponential family `(7)`, both
branches have the identical arithmetic coefficient

```text
mu(d)d^(-1-2omega).                                      (17)
```

The lower branch is selected by `P_d` through the right shift; the upper branch is selected by
`I-P_d`.  Thus the two summands of the original floor--tail formula are not merely correlated
scalar errors.  They are the complementary halves of one source incidence indexed by `d`.

The common upper input in `(15)` is the constant function `1`, which lies on the boundary of `H`
but not in `H`.  This failure is exact:

```text
||q_delta||_H^2=1/(2delta)->infinity.                     (18)
```

Therefore the common-coefficient incidence is a boundary form, not a bounded `H` operator obtained
by setting `delta=0` in `(8)`.

## 4. Relation to the normalized Möbius channel

The common coefficient `(17)` is, up to its sign and the scalar
`r_omega=1/zeta(1+2omega)`, the square of the normalized Möbius channel amplitude

```text
sqrt(r_omega) mu(d)d^(-1/2-omega).                       (19)
```

Consequently `(15)` is naturally a covariance form on the direct-sum Möbius channel, rather than
a coherent scalar multiplier.  The exact exponential boundary-layer law for the squared channel
weights shows where this covariance must remain active as `omega` decreases to zero.

This supplies the missing structural placement:

```text
normalized Mobius analysis
  -> complementary floor/tail incidence
  -> archimedean boundary renormalization
  -> causal/anti-causal continuation seam.               (20)
```

## 5. Positive boundary-renormalization obligation

The Gamma factor annihilates the Euler main moment at `s=1+omega`.  In the incidence coordinate,
this means that the successful archimedean operator cannot be a bounded multiplier acting after
the two branches have been separated.  It must renormalize the common boundary mode in `(15)`
while preserving the `P_d`/`I-P_d` pairing.

At the critical tangent, the target pointed output of that renormalization is already fixed:

```text
1 at the common incidence boundary
  -> ell_pole(t)=2e^(-t/2),
||ell_pole||_2^2=4.                                      (21)
```

The RH-bearing theorem is therefore a source-defined boundary map on the incidence form `(15)`
whose renormalized covariance is nonexpansive and whose two continuations differ by `ell_E`.
This statement is positive: every successful construction must possess that map.  A separate
estimate of the floor discrepancy and Möbius tail cannot construct it because the complementary
projection pairing would already have been discarded.

## 6. Scope and classification

- `[PROVED]` The regularized `H` identity `(8)`.
- `[PROVED]` The common-coefficient complementary boundary identity `(15)`.
- `[PROVED]` The unique exponential normalization at which the coefficients agree.
- `[PROVED]` The boundary-mode norm divergence `(18)`.
- `[NOT PROVED]` The Gamma kernel renormalizes `(15)` to `(21)` as a contraction.
- `[NOT PROVED]` The resulting continuation seam has energy at most four.

The proof is an exact change of variables and Hilbert-space encoding of an elementary Möbius
divisor switch.  It is a route bridge, not claimed as new scientific knowledge.

## 7. Lean decision

The RHTower tree does not yet formalize the shifted summatory error, the logarithmic right shifts,
or the complementary projection series.  Formalizing the projection identity without the
arithmetic series would be wrapper bloat.  No Lean file is added before the full incidence `(8)`
can be represented.

## Gates

- [x] logarithmic lower/upper projections identified
- [x] regularized `L2` incidence proved
- [x] common-coefficient boundary form proved
- [x] exact non-`L2` boundary mode isolated
- [x] Möbius covariance placement identified
- [ ] archimedean boundary renormalization theorem
- [ ] nonexpansive continuation seam
- [ ] four-unit energy bound
- [ ] RH
