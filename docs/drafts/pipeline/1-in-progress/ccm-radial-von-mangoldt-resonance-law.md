# CCM radial von Mangoldt resonance law

- **ID:** `ccm-radial-von-mangoldt-resonance-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** global radial-prolate defect measure plus the exact Poisson summation vector
- **Statement:** The exact constrained CCM lower tail has a von Mangoldt-weighted dilation response governed by the divisibility resonances `k=qj`, with an explicit arcsine constant.

## Exact object

Let `g_lambda`, `Phi_lambda=Fourier(g_lambda)`, and `d_1(lambda)` be the constrained CCM source,
its Fourier transform, and the first admissible prolate deficit. For `x>=1`, Poisson summation gives
the exact lower exterior vector

```text
B_lambda(x)
 =sqrt(lambda*x) sum_(k>=1) Phi_lambda(k*lambda*x)
  -g_lambda(0)/(2*sqrt(lambda*x)).                                (1)
```

For an integer dilation `q>=2`, define

```text
C_(lambda,q)
 =integral_1^infinity B_lambda(x)B_lambda(q*x) dx/x.              (2)
```

This is the `log q` autocorrelation entering the prime part of the exterior Weil form.

## Conjecture

`[CONJECTURE]` For every fixed integer `q>=2`,

```text
C_(lambda,q)/d_1(lambda) -> D_q,                                  (3)

D_q=8/(11*pi*sqrt(q))
    *sum_(j>=1) arcsin(1/(q*j))/j.                                (4)
```

Moreover there is an absolute summable majorant

```text
|C_(lambda,q)|/d_1(lambda) <= C*q^(-3/2)                          (5)
```

for all sufficiently large `lambda`, uniformly in `q>=2`. Consequently the exact all-prime
response has the limit

```text
R_exact(lambda)/d_1(lambda) -> K_rad,

K_rad=8/(11*pi)
  *sum_(q>=2) Lambda(q)/q
    *sum_(j>=1) arcsin(1/(q*j))/j.                                (6)
```

The signed prime contribution to the exterior Weil form is `-2*K_rad*d_1+o(d_1)`.

## Why this is not RH in disguise

The conjecture contains no zeta zero, no positivity assertion, no spectral floor, and no
determinant limit. It is an asymptotic correlation law for one explicit prolate source and the
von Mangoldt coefficient sequence. It can be false without deciding RH, and its constant is
independently testable from the exact finite-aperture source.

If proved, it feeds the chain

```text
radial von Mangoldt resonance law
  + archimedean radial symbol
  + true even-gap lower bound
  -> source Rayleigh-excess ratio
  -> projective ground-vector convergence
  -> locally uniform Hermitian determinant convergence
  -> RH.
```

## Derivation of the candidate constant

The proved global radial defect measure is

```text
lambda |Phi_lambda(lambda*y)|^2/d_1(lambda) dy
 =>8/(11*pi) dy/[y*sqrt(y^2-1)]                                   (7)
```

on `1<y<infinity`.

Expand the product in `(2)`. The `k`-th phase in `B_lambda(x)` and the `j`-th phase in
`B_lambda(q*x)` are identical precisely when

```text
k=q*j.                                                           (8)
```

The diagonal contribution is therefore

```text
lambda*sqrt(q)
 sum_(j>=1) integral_1^infinity
   |Phi_lambda(q*j*lambda*x)|^2 dx

=lambda/sqrt(q)
 sum_(j>=1) 1/j
   integral_(q*j)^infinity |Phi_lambda(lambda*y)|^2dy.            (9)
```

Using `(7)` in `(9)` gives

```text
8/(11*pi*sqrt(q))
 sum_(j>=1) 1/j
  integral_(q*j)^infinity dy/[y*sqrt(y^2-1)].                    (10)
```

The elementary identity

```text
integral_a^infinity dy/[y*sqrt(y^2-1)]=arcsin(1/a),  a>=1,       (11)
```

turns `(10)` into `(4)`.

Since `arcsin t<=pi*t/2` on `[0,1]`,

```text
D_q<=4/(11*q^(3/2))*sum_(j>=1)1/j^2,                             (12)
```

which explains the required majorant and makes `(6)` absolutely convergent.

The old first-endpoint-layer constant is the first small-argument approximation to `(6)`:

```text
arcsin(1/(q*j))>1/(q*j)

=> K_rad
 >(8/(11*pi))*(pi^2/6)*sum_(q>=2)Lambda(q)/q^2
 =(4*pi/33)*(-zeta'(2)/zeta(2)).                                 (13)
```

Thus full radial resummation predicts a strictly larger positive prime response than the isolated
sawtooth component, while preserving its sign and `d_1` scale.

## Open proof gates

### 1. Nonresonant fixed pairs

For `k!=q*j`, the phase difference is

```text
sqrt((k*x)^2-1)-sqrt((q*j*x)^2-1).                               (14)
```

It is not identically zero. Its derivative has at most one stationary point; stationary phase
therefore makes each fixed nonresonant pair `o(d_1)`. This pointwise statement is not enough to
sum over `k,j`.

### 2. Uniform double-sum control

Prove a two-parameter radial Bessel bound which is summable after Abel truncation and survives
removal of that truncation. The far radial asymptotic is harmonic, so absolute termwise summation is
not expected; one needs Dirichlet cancellation organized by the monotone phase.

### 3. Central Poisson cancellation

The term `g_lambda(0)/(2*sqrt(lambda*x))` cannot be separated in `L2` from the infinite radial sum
at the `d_1` scale. Prove the cancellation before taking quadratic limits, for example by Abel
regularizing the entire bracket in `(1)`. A proof which evaluates the central term or the radial
sum separately is invalid.

### 4. Uniform prime majorant

After the bracket is controlled, prove `(5)` directly. Fixed-`q` convergence does not justify the
von Mangoldt interchange.

### 5. Exact first-row estimate from the radial ODE

The remaining fixed-pair theorem in
`constrained-prolate-radial-leakage-divisibility-spectrum.md` reduces the simultaneous
off-diagonal problem to the first row. The leading Bessel model predicts the uniform estimate

```text
|G_lambda(1,k)|/d_1(lambda)
 <=C/[sqrt(c)*k^2],   c=2*pi*lambda^2, k>=2.                       (15)
```

For `k=o(c)`, the stationary point is

```text
x_k^2=1+1/k^2.
```

At that point the two normalized radial amplitudes have product `O(1/(c*sqrt(k)))`, while the
second derivative of the phase difference has size `k^3`. Stationary phase therefore gives
`O(c^(-3/2)k^(-2))` before the endpoint normalization, which is `(15)` after the factor of order
`c*d_1`. When `k` is of order `c`, the stationary point enters the Bessel endpoint layer of width
`c^(-2)`; the endpoint-layer estimate gives the same `c^(-5/2)` value at `k~c`. Thus no larger
coalescing contribution is predicted.

There is a single coordinate which proves both regimes for the limiting Bessel model. Its Gram
integral is

```text
I_(k,c)=1/sqrt(k) integral_1^infinity
  J_0(c*sqrt(x^2-1))
  J_0(c*sqrt(k^2*x^2-1)) dx/x.                                  (16)
```

Set

```text
t=k*sqrt(x^2-1),   alpha=c/k.
```

Then exactly

```text
I_(k,c)=k^(-5/2) integral_0^infinity
  t/(1+t^2/k^2)
  J_0(alpha*t)
  J_0(c*sqrt(k^2-1+t^2))dt.                                     (17)
```

The difference phase has its unique critical point at `t=1`, independently of `k`. If
`alpha->infinity`, the first Bessel envelope contributes `alpha^(-1/2)` and stationary phase at
`t=1` contributes a second `alpha^(-1/2)`. The second Bessel envelope contributes
`(c*k)^(-1/2)`. Including the outside factor `k^(-5/2)` gives

```text
I_(k,c)=O(c^(-3/2)*k^(-2)).                                      (18)
```

If `alpha=O(1)`, retain `J_0(alpha*t)` without a large-argument expansion. The second phase varies
on an order-one `t` scale and its envelope still supplies `(c*k)^(-1/2)`; direct Bessel-envelope
integration gives the same bound `(18)`. Thus `(18)` is uniform through `k` of order `c` and proves
`(15)` for the exact `sigma=0` radial model.

To transfer this from the leading Bessel model to the exact radial function without summing a
nonoscillatory big-`O` envelope, use the differential equation. If

```text
Q_k(x)=Ps_4^0(k*x,c^2),
p_k(x)=k^(-2)-x^2,
```

then every dilate satisfies

```text
(p_k Q_k')'+(kappa-c^2*k^2*x^2)Q_k=0.                            (19)
```

Multiplying the `k=1` equation by `Q_k`, the `k` equation by `Q_1`, subtracting, and integrating
gives the exact Lagrange identity

```text
c^2(k^2-1) integral x^2 Q_1 Q_k dx
 =(1-k^(-2)) integral Q_1' Q_k' dx
  -[p_1 Q_1'Q_k-p_k Q_k'Q_1]_boundary.                           (20)
```

Equation `(20)` exposes the large divisor `c^2(k^2-1)` at the exact-solution level. Split
`integral Q_1Q_k` into the endpoint layer, where `x^2=1+O(k^(-2))`, and its complement, where one
ordinary nonstationary integration by parts is uniform. The required proof is to combine `(20)`
with the endpoint Bessel bounds and the exact radial energy identities to obtain `(15)`.

If `(15)` holds, then

```text
sum_(k>=2) log(k)|G_lambda(1,k)|
 =O(d_1(lambda)/sqrt(c))=O(d_1(lambda)/lambda),                   (21)
```

which is already at the Rayleigh-transfer rate. Together with the `j,k>=2` estimate, the complete
raw radial prime response is then the proved diagonal constant plus `O(d_1/lambda)`.

### 6. Finite-aperture cutoff removes the infinite-error obstruction

For the actual restricted-Weil vector supported on the logarithmic aperture `[-log lambda,
log lambda]`, a prime shift `log q` has no overlap once

```text
q>lambda^2.                                                       (22)
```

Thus the finite operator consumed by the Hermitian determinant route requires the radial Gram row
only through `q<=lambda^2`, equivalently `q=O(c)`. This is exactly the range covered by the endpoint
transition analysis above.

This observation weakens the Dunster-remainder gate. A pointwise uniform relative error
`O(c^(-1))` whose absolute first-row contribution is bounded by `C*d_1/(c*q)` accumulates only

```text
d_1/c *sum_(q<=c) log(q)/q
 =O(d_1*log(c)^2/c)=o(d_1/lambda).                                (23)
```

No oscillatory representation of the error is needed for this finite-aperture estimate. The
apparent divergence arises only after separating the infinite exterior representative into prime
and central pieces. The exact quotient identity should instead be used as follows:

```text
finite aperture form: evaluate the finitely supported prime shifts directly;
exterior representative: use only for the completed closed-form identity,
                         without termwise infinite prime separation.                (24)
```

Accordingly, the determinant route needs a finite-cutoff version of `(3)`--`(5)`, uniform for
`q<=lambda^2`, rather than an independently summable all-prime decomposition of `(1)`.

## Attacks and failure conditions

1. A second phase resonance not explained by `(8)` would add another term to `(4)`.
2. A boundary stationary family with nonvanishing total mass would invalidate the pure diagonal
   rule.
3. Failure of the uniform `q^(-3/2)` bound would leave the all-prime constant undefined even if
   every fixed dilation converges.
4. A surviving central low-frequency defect could alter `(4)`; it must be computed, not assumed
   absent.
5. Even a proof of `(6)` does not prove RH. The archimedean radial energy and true even-gap
   comparison remain independent gates.
6. Failure of the exact ODE estimate `(15)` would leave a first-row term at gap scale; its limit
   would have to be added to `(4)` instead of being discarded.

## Gates

- [x] 0 → 1 in-progress: explicit source, candidate constant, resonance mechanism, and falsifiers stated
- [ ] 1 → 2 fully-proven: close the four proof gates above and audit the constant against parent theory
- [ ] 2 → 3 formalized: requires formal PSWF and semiclassical infrastructure; no wrapper Lean theorem
- [ ] 3 → 4 publication-ready: only if novelty and significance survive after the full Rayleigh consequence is known

## Log

- 2026-07-11 — generated top down from the exact Hermitian determinant implication and the global
  radial defect measure; divisibility resonance `k=qj` isolated as the first nontrivial all-prime
  carrier beyond the endpoint sawtooth scalar.
