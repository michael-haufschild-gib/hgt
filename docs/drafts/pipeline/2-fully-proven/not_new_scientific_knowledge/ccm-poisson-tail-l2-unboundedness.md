# The CCM Poisson-tail map is not controlled by prolate leakage in `L2`

- **ID:** `ccm-poisson-tail-l2-unboundedness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE] [CLOSED GENERIC TRANSFER]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent theories:** Mellin diagonalization of dilations; Dirichlet-polynomial multipliers;
  Connes--Consani's summation map `E`
- **Statement:** The arithmetic dilation sum that carries the Fourier leakage of a prolate source
  into the lower Poisson tail has unbounded operator norm on the natural `L2` leakage space. Its
  `N`-term norm grows at least like `sqrt(N)`. Therefore the scalar prolate deficit
  `||(1-P_lambda) Fourier(f)||_2` cannot, by itself, control the Weil-side tail or residual.

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

The growth in (1) is its coherent value at frequency zero. Thus the obstruction is the standard
unbounded critical-line zeta multiplier, written in the one-sided tail geometry needed by CCM.

## Consequence for the CCM transfer

For a time-limited unit vector `f`, the prolate angle controls only

```text
||(1-P_lambda)Fourier(f)||_2^2.
```

The theorem proves that no estimate of the form

```text
||1_[lambda,infinity) E((1-P_lambda)Fourier(f))||_(L2(dv/v))
 <=C_lambda ||(1-P_lambda)Fourier(f)||_2               (4)
```

can hold on the ambient leakage space with a constant obtained from the prolate angle alone. Hence
the exponentially small eigenvalue `1-chi_4(lambda)^2` and the surrogate spectral gap do not imply
a Weil residual estimate by abstract perturbation theory.

This closes the generic `L2` transfer, not the CCM route. For finite CCM determinants whose zeros are
real in the spectral variable, the prime-clock energy defect is exactly zero. Their unresolved
terminal gate is therefore locally uniform, zero-preserving convergence to `Xi`, not an additional
horizontal-energy estimate. The actual leakage vector is a special radial-prolate tail with strong
oscillatory and endpoint structure. A viable proof must use that structure to obtain the weighted or
projective control required by the Mellin determinants—through endpoint jets, weighted variation, a
Mellin Hardy space, an exact radial-prolate summation identity, or a different direct normal-family
argument. Such information is absent from the scalar concentration eigenvalue.

## Novelty verdict

The theorem is an exact and useful route gate, but its mechanism is standard Mellin/dilation theory.
It is therefore `[BRIDGE]`, not new scientific knowledge. The new unresolved mathematical object is
the restriction of the arithmetic tail map to the two-dimensional low-mode radial-prolate family.
