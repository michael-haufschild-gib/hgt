# CCM Poisson-tail control must use source-structured arithmetic cancellation

- **ID:** `ccm-poisson-tail-l2-unboundedness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE] [NECESSITY THEOREM]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent theories:** Mellin diagonalization of dilations; Dirichlet-polynomial multipliers;
  Connes--Consani's summation map `E`
- **Statement:** A cofinal CCM tail estimate must use structure beyond the scalar prolate deficit.
  The ambient arithmetic dilation sum has `N`-term norm at least of order `sqrt(N)`, so the required
  boundedness must arise on the radial-prolate sequence through oscillation, endpoint jets, a
  zeta-weighted graph norm, or an exact summation identity.

## Route object

For `a>0` and a positive integer `N`, define

```text
(S_(a,N)q)(v)=v^(1/2) sum_(1<=n<=N) q(nv),   v>=a.
```

View it as an operator

```text
S_(a,N):L2([a,infinity),dv) -> L2([a,infinity),dv/v).
```

This is the finite arithmetic-summation operator occurring in the CCM lower-tail mechanism. If
`q` is the positive-frequency part of the Fourier leakage of a source `f`, then Poisson inversion
expresses the lower tail of `E(f)` through the limit of these dilation sums applied to `q`.

## Theorem

`[PROVED HERE]` For every `a>0` and `N>=2`,

```text
||S_(a,N)|| >= 2^(-1/2) sum_(n=1)^N n^(-1/2)
             >= sqrt(2)*(sqrt(N)-1).                    (1)
```

Consequently,

```text
sup_N ||S_(a,N)||=infinity.                              (2)
```

In particular, the infinite arithmetic sum has no bounded extension from the source `L2(dv)`
leakage space to the target `L2(dv/v)` tail space.

## Proof

The logarithmic change of variables gives a unitary map

```text
U:L2([a,infinity),dv) -> L2([log a,infinity),dt),
(Uq)(t)=e^(t/2)q(e^t).
```

For `F=Uq`, direct substitution gives

```text
(S_(a,N)q)(e^t)
 =sum_(n=1)^N n^(-1/2)F(t+log n).                       (3)
```

The target measure `dv/v` becomes `dt`.

Put `T=log a`, `L=2 log N`, and take

```text
F(t)=L^(-1/2) 1_[T,T+L](t).
```

Then `||F||_2=1`. For

```text
t in [T,T+L-log N],
```

one has `t+log n in [T,T+L]` for every `1<=n<=N`. Equation (3) is therefore constant on this
interval with value

```text
L^(-1/2) sum_(n=1)^N n^(-1/2).
```

The interval has length `L-log N=L/2`, so

```text
||S_(a,N)q||_(L2(dv/v))
 >=2^(-1/2) sum_(n=1)^N n^(-1/2).
```

Finally,

```text
sum_(n=1)^N n^(-1/2) >= integral_1^N x^(-1/2)dx=2(sqrt(N)-1),
```

which proves (1)--(2).

## Mellin interpretation

After the same logarithmic unitary, the finite sum is a translation polynomial

```text
sum_(n<=N)n^(-1/2) tau_(log n).
```

On the full line its Fourier multiplier is the Dirichlet polynomial

```text
sum_(n<=N)n^(-1/2-it).
```

The growth in (1) is its coherent value at frequency zero. Thus the positive CCM estimate must
cancel the critical-line zeta multiplier's coherent mode in the one-sided tail geometry.

## Positive requirement for the CCM transfer

For a time-limited unit vector `f`, the prolate angle controls only

```text
||(1-P_lambda)Fourier(f)||_2^2.
```

The theorem shows that the successful estimate must be source-restricted, with cancellation beyond
an ambient operator bound of the form

```text
||1_[lambda,infinity) E((1-P_lambda)Fourier(f))||_(L2(dv/v))
 <=C_lambda ||(1-P_lambda)Fourier(f)||_2               (4)
```


The scalar concentration eigenvalue must be supplemented by cancellation data describing the
actual radial-prolate leakage vector.

For finite CCM determinants whose zeros are
real in the spectral variable, the prime-clock energy defect is exactly zero. Their unresolved
terminal gate is therefore locally uniform, zero-preserving convergence to `Xi`, not an additional
horizontal-energy estimate. The actual leakage vector is a special radial-prolate tail with strong
oscillatory and endpoint structure. A viable proof must use that structure to obtain the weighted or
projective control required by the Mellin determinants—through endpoint jets, weighted variation, a
Mellin Hardy space, an exact radial-prolate summation identity, or a different direct normal-family
argument. Such information is absent from the scalar concentration eigenvalue.

`ccm-endpoint-oscillation-poisson-tail-bound.md` supplies the first source-specific exception. For
an even compact `C2` source, the leading exterior Fourier term generates the bounded sawtooth
series `sum sin(n theta)/n`, not the coherent packet used in `(1)`. The arithmetic lower tail is
therefore controlled by endpoint jets. For the normalized CCM zero-integral two-mode source, its
Poisson zero-mode correction is moreover asymptotic to an explicit constant times the concentration
deficit. The generic theorem here remains valid, but its bad vectors are now proved not to model the
leading endpoint tail of the CCM source.

## Novelty verdict

The theorem is an exact and useful topology classifier, but its mechanism is standard
Mellin/dilation theory. It is therefore `[BRIDGE]`, not new scientific knowledge. The positive
unresolved mathematical object is the arithmetic tail map restricted to the two-dimensional
low-mode radial-prolate family.
