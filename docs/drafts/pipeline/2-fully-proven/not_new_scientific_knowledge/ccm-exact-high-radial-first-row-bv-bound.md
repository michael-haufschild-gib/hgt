# The exact high radial first row is summable by bounded variation

- **ID:** `ccm-exact-high-radial-first-row-bv-bound`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's pole-uniform Bessel and exterior Liouville--Green expansions,
  exact interaction-picture transport, and nonstationary integration by parts
- **Statement:** For the actual constrained prolate source and every
  `k>=lambda^2=c/(2*pi)`, the exact radial Gram entry satisfies
  `|G_lambda(1,k)|<=C*d_1(lambda)/k^2`. Consequently the truncated-divisor weighted high first row
  is `o(d_1)`.

## Setup

Put

```text
U_(lambda,r)(x)=sqrt(lambda*x)q_lambda(lambda*r*x),

G_lambda(1,k)
 =integral_1^infinity U_(lambda,1)(x)U_(lambda,k)(x)dx/x,

c=2*pi*lambda^2.                                                (1)
```

The constrained `m=4` exterior mode carries the `sqrt(d_1)` scale. The `m=0` mode and its cross
term are smaller and obey the same estimates after their deficit factor is inserted.

## Exterior phase for the high factor

For `k>=lambda^2` and `x>=1`, one has `k*x>=lambda^2>2` for large `lambda`. Dunster's Section 2
Liouville--Green expansion therefore gives the exact phase-preserving representation

```text
U_(lambda,k)(x)
 =sqrt(d_1)/k sum_(epsilon in {+1,-1})
   exp(i*epsilon*c*xi_c(k*x))a_(epsilon,c,k)(x),                 (2)
```

where

```text
|a_(epsilon,c,k)(x)|<=C*x^(-1/2),
|d/dx a_(epsilon,c,k)(x)|<=C*x^(-3/2).                           (3)
```

The differentiated bounds include the exact remainder by
`radial-pswf-interaction-picture-transport.md`: the Liouville-transformed equation gives exact
amplitude derivatives proportional to `psi/c`, and Dunster's exterior potential is uniformly
short-range. This avoids the unjustified step of treating an additive Olver remainder as a
relative oscillatory remainder. The phase satisfies

```text
Phi_(epsilon,k)'(x)
 =epsilon*c*k*sqrt((k^2*x^2-sigma_4(c)^2)/(k^2*x^2-1)),

|Phi_(epsilon,k)'(x)|>=c_0*c*k,                                 (4)
```

and

```text
|d/dx[1/Phi_(epsilon,k)'(x)]|<=C/(c*k*x^2).                     (5)
```

## Bounded-variation lemma for the pole factor

For either amplitude in `(2)`, define

```text
V_(epsilon,c,k)(x)
 =U_(lambda,1)(x)a_(epsilon,c,k)(x)/x.                           (6)
```

`[PROVED HERE]` Dunster's Section 3 pole-uniform Bessel formula and its differentiated Olver bound
give

```text
|V_(epsilon,c,k)(1)|
 +integral_1^infinity |V_(epsilon,c,k)'(x)|dx
 <=C*sqrt(d_1)*c.                                               (7)
```

To verify `(7)`, write the normalized first factor as

```text
U_(lambda,1)(x)/sqrt(d_1)
 =A_c(x){J_0(c*xi_c(x))+c^(-1)E_c(x)},                           (8)
```

where `A_c(x)=O(x^(-1/2))`, `A_c'(x)=O(x^(-3/2))`, and the error and its derivative obey the
corresponding Bessel-envelope bounds in the analytic endpoint coordinate `eta=xi_c^2`.

On the endpoint interval `c^2*(x-1)<=1`, the analytic coordinate gives total variation `O(1)`.
On its complement, use the Bessel symbol estimates

```text
|J_0(u)|<=C*u^(-1/2),
|J_0'(u)|<=C*u^(-1/2),                                         (9)
```

and `xi_c'(x)=O(x/sqrt(x^2-1))`. After multiplication by the factor
`a_(epsilon,c,k)(x)/x=O(x^(-3/2))`, the phase derivative term is bounded by an integrable envelope
whose integral is `O(c)`. The differentiated Olver error has an extra `c^(-1)` and is smaller.
The far boundary is zero. This proves `(7)`.

## High-index integration by parts

Insert `(2)` into `(1).` For each sign, integration by parts gives

```text
integral_1^infinity V_(epsilon,c,k)(x)
  exp(i*Phi_(epsilon,k)(x))dx

 =-[V_(epsilon,c,k)(1)exp(i*Phi_(epsilon,k)(1))]
     /(i*Phi_(epsilon,k)'(1))
   -integral_1^infinity exp(i*Phi_(epsilon,k)(x))
      d/dx[V_(epsilon,c,k)(x)/(i*Phi_(epsilon,k)'(x))]dx.        (10)
```

Equations `(4)`--`(7)` bound `(10)` by

```text
C*sqrt(d_1)/k.                                                  (11)
```

The outside factor `sqrt(d_1)/k` in `(2)` therefore proves

```text
|G_lambda(1,k)|<=C*d_1/k^2,
k>=lambda^2.                                                    (12)
```

## Truncated-divisor tail

Let

```text
a_lambda(k)=sum_(q|k; q<=lambda^2)Lambda(q).
```

The divisor identity gives `0<=a_lambda(k)<=log k`. Hence `(12)` implies

```text
sum_(k>lambda^2)a_lambda(k)|G_lambda(1,k)|
 <=C*d_1 sum_(k>lambda^2)log(k)/k^2
 =O(d_1*log(lambda)/lambda^2)
 =o(d_1).                                                       (13)
```

Together with `ccm-exact-finite-aperture-first-row-vanishing.md`, equation `(13)` closes the full
truncated-divisor weighted first row.

## Route consequence

The exact prime-shift cutoff and infinite radial multiplier are now both respected:

```text
low radial row k<=lambda^2: pole-uniform stationary estimate,
high radial row k>lambda^2: exterior phase + BV estimate.        (14)
```

Thus the high radial divisor tail identified in
`ccm-prime-shift-radial-index-separation-law.md` vanishes at the leakage scale.

## Novelty and significance verdict

The theorem is a source-specific but standard nonstationary-phase argument using Dunster's
published expansions. It repairs the CCM route but does not clear the parent-theory novelty gate;
it is classified as a bridge.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699, Sections 2
  and 3.
- F. W. J. Olver, *Asymptotics and Special Functions*, the Liouville--Green and Bessel error
  theorems used by Dunster.
- `radial-pswf-interaction-picture-transport.md`, exact ODE transport and Lean formalization.

## Lean decision

The formal tree has no Bessel-envelope bounded-variation or nonstationary integration interface.
No Lean file is added.

## Gates

- [x] high radial factor placed in the exterior oscillatory regime
- [x] pole-factor weighted BV bound proved
- [x] exact `k^(-2)` high first-row estimate proved
- [x] truncated-divisor weighted high tail summed
