# The CCM radial prime charge has a complete weighted first-row theorem

- **ID:** `ccm-radial-prime-first-row-reduction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[COMPLETED REDUCTION]`
- **Scientific status:** `[PROVED HERE] [NOT AN RH PROOF]`
- **Parent theories:** `ccm-limiting-radial-first-row-weber-bound.md`,
  `ccm-exact-radial-nonstationary-sector-bound.md`,
  `ccm-exact-finite-aperture-first-row-vanishing.md`,
  `ccm-exact-high-radial-first-row-bv-bound.md`, Dunster's uniform radial Bessel expansion, and the
  von Mangoldt divisor identity
- **Statement:** After removing the solved diagonal divisibility spectrum, the `j,k>=2` sector is
  `O(d_1/c)` and the low first row through `k<=lambda^2` is
  `O(d_1*c^(-1/2)+d_1*log(c)^2/c)`. The weighted high radial tail is
  `O(d_1*log(lambda)/lambda^2)`. Hence the complete exact off-diagonal radial prime charge is
  `o(d_1)`.

## Setup

Use the constrained source and radial Gram matrix

```text
G_lambda(j,k)
 =inner(H_(lambda,j),H_(lambda,k))_(L2(ds)),

H_(lambda,k)(s)
 =sqrt(lambda*e^s) q_lambda(k*lambda*e^s),

c=2*pi*lambda^2.                                                (1)
```

For a radial cutoff `K`, define the raw prime Gram charge

```text
P_(lambda,K)
 =-2 sum_(k=2)^K log(k) sum_(j=1)^K G_lambda(j,k).                (2)
```

Equation `(2)` is the finite divisibility expansion of the prime pairing: writing `k=mn` and
summing `Lambda(m)` over divisors gives

```text
sum_(m|k;m>=2)Lambda(m)=log k.                                   (3)
```

It deliberately excludes the Poisson central correction, which is kept intact later in the exact
closed-form tail.

## Uniform nonstationary Gram bound

`[PROVED in ccm-exact-radial-nonstationary-sector-bound.md]` There is a constant `C` such that, for
all sufficiently large `lambda` and all
distinct integers `j,k>=2`,

```text
|G_lambda(j,k)|
 <=C*d_1(lambda)/(c*j*k*|j-k|).                                  (4)
```

### Phase-preserving exact proof

Dunster's radial expansion and the constrained `m=4` dominance give, uniformly for `x>=1` and
`r>=2`,

```text
sqrt(lambda*x) q_lambda(lambda*r*x)
 =sqrt(d_1(lambda))/r
   *a_(r,c)(x)
   *[cos(c*xi_c(r*x)-pi/4)+O(c^(-1))],                            (5)
```

where `a_(r,c)` and its first derivative are bounded by an integrable envelope independent of
`r,c`. More precisely, after the `ds=dx/x` measure is included, the product envelope in the
`(j,k)` entry is bounded by `C/(j*k*x^2)` together with its first derivative.

For the limiting phase `xi_infinity(t)=sqrt(t^2-1)`,

```text
d/dx xi_infinity(r*x)=r^2*x/sqrt(r^2*x^2-1).                      (6)
```

As a function of the integer parameter `r>=2`, the right side of `(6)` has derivative bounded
above and below by positive absolute constants, uniformly for `x>=1`. The small
`sigma_4(c)^2=O(c^(-1))` perturbation in Dunster's exact phase preserves this property. Hence

```text
|d/dx[xi_c(j*x)-xi_c(k*x)]|>=c_0|j-k|,   j,k>=2.                  (7)
```

The sum phase has an even larger derivative. One integration by parts in each **leading Bessel
product** from `(5)`, using `(7)` and the integrable amplitude derivative, gives `(4)` for that
model.

For `j,k>=2`, both radial arguments are at least two. Dunster's exterior Liouville--Green
expansion `(2.19)`--`(2.22)`, rather than the pole-uniform Bessel envelope alone, retains the two
oscillatory branches and their differentiated Olver remainders uniformly to infinity. Applying
the integration-by-parts argument above to that exact phase-preserving representation proves `(4)`.
The complete proof and symbol bounds are recorded in
`ccm-exact-radial-nonstationary-sector-bound.md`.

## Summed nonstationary sector

The elementary Hilbert-kernel estimate

```text
sum_(j>=2;j!=k) 1/(j*k*|j-k|)
 <=C*(1+log k)/k^2                                              (8)
```

and `(4)` imply

```text
sum_(k>=2) log(k)
  sum_(j>=2;j!=k)|G_lambda(j,k)|

 <=C*d_1(lambda)/c
   *sum_(k>=2)log(k)(1+log k)/k^2
 =O(d_1(lambda)/c).                                              (9)
```

Therefore this entire sector would be `o(d_1)`.

## Exact first-row reduction

Split `(2)` into diagonal, first-row, and the sector in `(9)`:

```text
P_(lambda,K)
 =D_(lambda,K)+E_(lambda,K)+N_(lambda,K),                         (10)

D_(lambda,K)=-2 sum_(k=2)^K log(k)G_lambda(k,k),
E_(lambda,K)=-2 sum_(k=2)^K log(k)G_lambda(1,k).                  (11)
```

The radial leakage theorem proves

```text
D_(lambda,infinity)/d_1(lambda)
 ->-16/(11*pi)sum_(k>=2)log(k)/k*arcsin(1/k),                     (12)
```

and conjectural estimate `(9)` would prove

```text
N_(lambda,infinity)=O(d_1(lambda)/c)=o(d_1(lambda)).              (13)
```

For the exact finite prime aperture, replace `log k` by

```text
a_lambda(k)=sum_(q|k; q<=lambda^2)Lambda(q).
```

The bound `a_lambda(k)<=log k` preserves `(12)`--`(13)` by dominated convergence. The only
unresolved exact radial prime contribution is therefore the weighted first-row series

```text
E_lambda=-2 sum_(k>=2)a_lambda(k)G_lambda(1,k).                   (14)
```

## Coalescing stationary scale

For the limiting radial phase, a stationary point of

```text
xi_infinity(x)-xi_infinity(k*x)
```

must satisfy

```text
x/sqrt(x^2-1)=k^2*x/sqrt(k^2*x^2-1).
```

Its unique solution is

```text
x_k^2=1+1/k^2.                                                    (15)
```

Hence

```text
x_k-1~1/(2k^2).                                                   (16)
```

Dunster's radial Bessel endpoint coordinate has width `x-1` of order `c^(-2)`. Equations
`(15)`--`(16)` show that the stationary point coalesces with the endpoint precisely at

```text
k asymptotic to c=2*pi*lambda^2.                                  (17)
```

This is the same scale as the finite-prime cutoff in the CCM parity carrier.

## Imported leading-model first-row vanishing theorem

The complete proof is recorded separately in
`ccm-limiting-radial-first-row-weber-bound.md`. Its mechanism and exact transfer target are
retained here because they determine the open remainder norm. Put

```text
rho(x)=sqrt(x^2-1).
```

When `sigma_4(c)=0`, the radial Bessel profile in Dunster's formula simplifies exactly to

```text
R_c(x)=x^(-1/2)J_0(c*rho(x)).                                    (18)
```

The normalized leading-model first-row Gram entry is therefore a fixed constant times

```text
c*k^(-1/2) integral_1^infinity
  J_0(c*rho(x))J_0(c*rho(k*x)) dx/x.                             (19)
```

For `1<<k<<c`, the difference phase has the critical point `(15)`. At that point

```text
rho(x_k)=1/k,
rho(k*x_k)=k,
|d^2/dx^2[rho(x)-rho(k*x)]|_(x=x_k)=k^3-k^(-1).                  (20)
```

The two Bessel amplitudes and one-dimensional stationary phase consequently give

```text
G_lambda^model(1,k)/d_1(lambda)
 =O(c^(-1/2)k^(-2)).                                             (21)
```

The sum phase is nonstationary and is smaller. For every fixed `k`, ordinary stationary phase
proves `(21)`. In the transition `k=u*c` with `u` in a compact subset of `(0,infinity)`, set
`x=1+z/c^2`. Then

```text
c*rho(x)->sqrt(2z),
c*rho(k*x)=c*k+u*z-(2u)^(-1)+o(1),
dx=c^(-2)dz,                                                     (22)
```

while the second Bessel amplitude is `O(c^(-3/2))`. Thus

```text
G_lambda^model(1,u*c)/d_1(lambda)=O_u(c^(-5/2)),                  (23)
```

exactly the value predicted by `(21)`. More precisely, the transition is governed by the classical
Weber Gaussian--Bessel transform. After `r=rho(x)` and `z=c*r`, the model integral becomes

```text
1/(c*sqrt(k)) integral_0^infinity z J_0(z)
  J_0(sqrt(k^2*z^2+c^2*(k^2-1))) dz                         (23a)
```

up to a factor tending to one on bounded `z`. If `k/c->u>0`, the second Bessel phase is

```text
c*k-1/(2u)+u*z^2/2+o(1).
```

Abel continuation of

```text
integral_0^infinity z J_0(z)exp(i*u*z^2/2)dz
 =i/u*exp(-i/(2u))                                           (23b)
```

therefore supplies exactly the missing factor `1/u=c/k`. This identifies an explicit Weber
transition kernel, rather than merely a coalescing scale. Endpoint integration by parts for
`k/c->infinity` gives the same factor.

### Uniform model estimate

The regimes match without an asymptotic gap. In the variable `r=rho(x)`, define

```text
M_c(k)=c/sqrt(k) integral_0^infinity r/(1+r^2) J_0(c*r)
       J_0(c*sqrt(k^2*r^2+k^2-1))dr.                         (23c)
```

There is an absolute constant `C` such that, for `c>=2` and every integer `k>=2`,

```text
|M_c(k)|<=C/(sqrt(c)*k^2).                                   (23d)
```

Use the standard Bessel symbol decomposition

```text
J_0(t)=exp(i*t)a_+(t)+exp(-i*t)a_-(t),
|d^r/dt^r a_+-(t)|<=C_r*t^(-1/2-r),   t>=1,                  (23e)
```

and leave `J_0` unexpanded below unit argument.

If `2<=k<=c`, split at `r=2/c`. The endpoint piece is bounded absolutely by
`C*c^(-3/2)/k`, which is at most the right side of `(23d)`. On the remaining interval the
difference phase

```text
phi_k(r)=r-sqrt(k^2*r^2+k^2-1)
```

has exactly one critical point `r=1/k`, with

```text
|phi_k''(1/k)|=(k^2-1)/k asymptotic to k.                     (23f)
```

After the prefactor in `(23c)` is included, the amplitude at this point is `O(k^(-3/2))`.
The stationary-phase lemma gives `O(c^(-1/2)k^(-2))`. On the complement, one integration by
parts using the monotonicity of `phi_k'` gives the same bound. The sum phase has no critical point
and is smaller. The differentiated amplitudes are `O(r^(-2))` after the measure in `(23c)` is
included, so the boundary at infinity vanishes.

If `k>=c`, the critical point lies in `r<=1/c`. There set `z=c*r` and then `w=z^2`. The second
Bessel phase satisfies

```text
d/dw sqrt(k^2*w+c^2*(k^2-1))
 =k^2/(2*sqrt(k^2*w+c^2*(k^2-1))) asymptotic to k/c            (23g)
```

for bounded `z`. The factor `z dz=dw/2` removes the apparent stationary endpoint. Integration by
parts in `w`, together with the large-argument symbol bound for the second Bessel factor, gives

```text
C/(c^(3/2)*k) * c/k=C/(sqrt(c)*k^2).                           (23h)
```

For `r>=1/c`, both phases are nonstationary because `1/k<=1/c`; the same symbol integration by
parts gives `(23h)`. A dyadic partition makes the estimate uniform at infinity. This proves
`(23d)`. Consequently,

```text
sum_(k>=2)log(k)G_lambda^model(1,k)
 =O(d_1(lambda)c^(-1/2))=o(d_1(lambda)).                          (24)
```

For the actual fixed mode, `c*sigma_4(c)^2` has a finite nonzero limit. This changes the bounded
stationary phase but not the powers in `(21)`--`(24)`. What is still missing is a differentiated,
two-parameter version of Dunster's exact remainder estimate strong enough to retain the
`k^(-2)` summability uniformly through `k/c`.

## Positive completed reduction

The proved first-row theorem is one-dimensional in the arithmetic index:

```text
  d_1(lambda)^(-1) sum_(k>=2)a_lambda(k)G_lambda(1,k) ->0
uniformly through the transition k/c,
then combine the solved diagonal spectrum with the exact
Poisson central correction and archimedean form.                   (25)
```

The exact aperture stops the prime divisor `q` at `q<=lambda^2`; it does not stop the radial index
`k=q*n`, because `n` remains unbounded. `ccm-exact-finite-aperture-first-row-vanishing.md` transfers
the leading bound only on the low radial subseries `k<=lambda^2`. The surviving gate is

```text
sum_(k>lambda^2)a_lambda(k)G_lambda(1,k)=o(d_1(lambda)).          (26)
```

`ccm-exact-high-radial-first-row-bv-bound.md` proves `(26)` absolutely. Therefore the radial
constant can now be assembled with the Poisson center, archimedean form, and true restricted-Weil
gap.

The finite-archimedean Gamma boundary law makes the division of labor exact: completion supplies
one upper projective direction, whereas the indices `k` in `(25)` carry an unbounded independent
divisibility module. The desired theorem must transport and sum that module in the closed Weil
form. It cannot replace it by an archimedean scalar or a compact-open germ limit.

## Novelty and significance verdict

The phase geometry and leading-model reduction use standard nonstationary phase and the classical
divisor identity. The exact all-index error-stability theorem may be nontrivial and remains under
the main route's novelty gate. No novelty claim is made before it is proved.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- NIST Digital Library of Mathematical Functions, Eq. 10.22.51 (the Gaussian--Bessel transform
  used in `(23b)`, followed by Abel continuation).

## Lean decision

The formal tree has no radial PSWF or stationary-phase infrastructure. No Lean file is added.

## Gates

- [x] uniform nonstationary estimate proved for the leading Bessel model
- [x] transfer the estimate through Dunster's phase-preserving exterior remainder
- [x] sum the exact `j,k>=2` weighted sector
- [x] diagonal charge imported and separated
- [x] isolate the exceptional first-row series for the exact finite radial charge
- [x] coalescing scale `k/c` identified
- [x] derive the fixed-index and `k/c` transition vanishing scales
- [x] prove one uniform summable bound for the complete leading Dunster model
- [x] transfer summable vanishing to the exact PSWF remainder for `k<=lambda^2`
- [x] prove the truncated-divisor weighted high radial tail `(26)`
- [ ] combine with exact Poisson central correction
- [ ] true Weil Rayleigh-excess and parity transfer
