# Cofinal prime separation forces ground-state oscillation

- **ID:** `ccm-prime-log-crowding-separating-margin-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the fundamental theorem for a differentiable operator orbit, the Rayleigh
  quotient, and the prime number theorem
- **Statement:** The least Gram eigenvalue separating finitely many prime-log shift channels is at
  most the squared nearest-neighbour log-prime spacing times the translation-generator energy of
  the carrier vector. Hence any cofinal CCM construction retaining a quantitative incidence
  margin must pay for prime-log crowding through growing oscillation.

## 1. A general channel-crowding inequality

Let `H` be a complex Hilbert space and let

```text
A:I->B(H)                                                   (1)
```

be strongly continuously differentiable on an interval `I`. Fix a unit vector `xi` for which

```text
M_A(xi;I)=sup_(t in I)||A'(t)xi||<infinity.                 (2)
```

For distinct nodes `h_1,...,h_k in I`, let

```text
G_A(xi;h)=(<A(h_i)xi,A(h_j)xi>)_(1<=i,j<=k),
sigma_A(xi;h)=lambda_min(G_A(xi;h)).                        (3)
```

`[PROVED]` If

```text
delta(h)=min_(i!=j)|h_i-h_j|,                              (4)
```

then

```text
sigma_A(xi;h)<=delta(h)^2 M_A(xi;I)^2/2.                   (5)
```

### Proof

Choose `i!=j` realizing `(4)` and take the unit coefficient vector with entries
`2^(-1/2)` and `-2^(-1/2)` in those positions and zero elsewhere. Its Gram Rayleigh quotient is

```text
1/2 ||A(h_i)xi-A(h_j)xi||^2.                              (6)
```

The strong fundamental theorem of calculus gives

```text
||A(h_i)xi-A(h_j)xi||
 <=integral_(h_i)^(h_j)||A'(t)xi||dt
 <=delta(h) M_A(xi;I).                                    (7)
```

The least eigenvalue is at most every unit Rayleigh quotient, so `(6)`--`(7)` prove `(5)`.

Equivalently, every positive separating margin obeys the exact resource lower bound

```text
M_A(xi;I)>=sqrt(2 sigma_A(xi;h))/delta(h).                 (8)
```

## 2. Translation-generator form

Let `U_t=exp(tD)` be a strongly continuous unitary translation group with skew-adjoint generator
`D`. For `xi in Dom(D)`,

```text
d/dt U_t xi=U_t Dxi,
M_U(xi;I)=||Dxi||.                                        (9)
```

Thus the Gram matrix of the translated channels satisfies

```text
sigma_U(xi;h)<=delta(h)^2||Dxi||^2/2,                     (10)

||Dxi||>=sqrt(2 sigma_U(xi;h))/delta(h).                 (11)
```

For the symmetric orbit

```text
B(t)=U_t+U_(-t),                                          (12)
```

one has

```text
||B'(t)xi||<=2||Dxi||,                                    (13)
```

and therefore

```text
sigma_B(xi;h)<=2 delta(h)^2||Dxi||^2.                     (14)
```

The compressed aperture shifts satisfy the same estimate on the zero-extension graph domain:
if `P_A` is the aperture projection and `xi` has zero extension in `Dom(D)`, then

```text
T_(A,t)xi=P_A U_t P_A xi                                  (15)
```

up to the fixed smooth scalar weight of the CCM representation. Contractivity of `P_A` gives
`(10)` with `D` replaced by the corresponding weighted translation generator `D+c`. The symmetric
prime-correlation channel inherits `(14)` with the same harmless fixed weight correction.

## 3. Prime-log crowding

For `P>=3`, put

```text
H_P={log p:p<=P},
delta_P=min{log(q/p):p<q<=P are consecutive primes}.       (16)
```

Ordering the `pi(P)` points of `H_P` inside `[log 2,log P]` gives the exact pigeonhole bound

```text
delta_P<=log(P/2)/(pi(P)-1).                               (17)
```

In particular, the prime number theorem gives

```text
delta_P=O((log P)^2/P)->0.                                (18)
```

Applying `(10)` to the prime-log channels gives

```text
sigma_P
 <=delta_P^2||D xi_P||^2/2.                              (19)
```

Hence a cofinal family with

```text
inf_P sigma_P>0                                           (20)
```

must satisfy, along the same cutoffs,

```text
||D xi_P||>=c/delta_P,                                    (21)
```

and in particular cannot remain bounded in the translation-generator graph norm. Using only
`(17)`, the exact statement is

```text
||D xi_P||
 >=sqrt(2 sigma_P) (pi(P)-1)/log(P/2).                    (22)
```

The PNT asymptotic turns a fixed positive margin into the scale

```text
||D xi_P|| >= c P/(log P)^2.                              (23)
```

No unproved prime-gap estimate is used.

### Degree-one Euler rays: the top-shell reduction

For a degree-one Euler parameter, the source operator is a finite ray sum over `m log p`, not a
single shift. The single-channel estimate `(19)` therefore does not apply indiscriminately to the
whole ray family. It does apply exactly on the top prime shell.

Set the aperture ceiling to `N_A=e^A`. If

```text
e^(A/2)<p<=e^A,                                            (23a)
```

then `m log p>A` for every `m>=2`. The degree-one ray operator from
`ccm-generic-ground-separating-incidence-law.md` reduces to

```text
W_(A,p)=alpha_p B_(A,log p),       alpha_p!=0.             (23b)
```

Rescaling each source coordinate by `alpha_p` is invertible and preserves incidence rank. For the
normalized ray channels `alpha_p^(-1)W_(A,p)`, equations `(19)`--`(22)` apply verbatim.

The number of primes in `(23a)` is

```text
pi(e^A)-pi(e^(A/2)) asymptotic to e^A/A.                   (23c)
```

Their logarithms lie in an interval of length `A/2`, so their nearest-neighbour spacing satisfies

```text
delta_A^top
 <=(A/2)/(pi(e^A)-pi(e^(A/2))-1)
 =O(A^2 e^(-A)).                                          (23d)
```

Thus a fixed positive normalized margin on the actual degree-one Euler-ray carrier forces

```text
||D xi_A||>=c e^A/A^2.                                    (23e)
```

The critical weights cannot be ignored for an unnormalized stability statement; they determine
the coordinate norm. Equation `(23e)` concerns the canonically rescaled source directions in
which every retained prime has unit first-order incidence.

## 4. Mixed scalar/state form

In `ccm-euler-observability-relative-index-allocation-law.md`, a scalar jet may already see a
subspace of the prime directions. Let `W_P` be the scalar-blind coefficient subspace. If
`W_P` contains a difference `e_p-e_q` of two prime-coordinate directions, the same two-vector
proof gives

```text
sigma_(P,W)
 <=|log p-log q|^2 M_A(xi_P)^2/2.                         (24)
```

More general scalar-blind subspaces require their own smallest Rayleigh quotient; no fictitious
node spacing is assigned to an arbitrary linear combination. The exact conclusion is that scalar
differential aperture removes a close-pair crowding obligation only when its observed quotient
separates that pair. Every unresolved close pair transferred into the relative state still
requires the corresponding oscillation scale.

## 5. Positive CCM requirement

`ccm-generic-ground-separating-incidence-law.md` proves qualitative injectivity outside a closed
nowhere-dense Gram seam. Equation `(8)` gives the missing quantitative law:

```text
cofinal prime-incidence margin
  -> inverse-spacing translation-generator energy
  -> escape from bounded graph-norm compactness.           (25)
```

This is the positive form of channel crowding. A successful CCM carrier is forced to become more
oscillatory as new prime logs enter; a bounded-oscillation ground family cannot carry a uniform
first-order prime marking. If the margin is allowed to decay, `(8)` gives the exact tradeoff that
must still be combined with the reduced-resolvent gap and the growing Mellin evaluation norm.

Accordingly there are two admissible cofinal mechanisms:

```text
inverse-spacing generator growth preserving a norm-stable incidence margin,
or
a renormalized/nonuniform incidence topology that retains directions whose Gram margin vanishes.
                                                               (25a)
```

The theorem does not assert that every divisor-preserving determinant limit needs a uniform lower
bound. It asserts the exact oscillation price whenever norm-stable inversion or transport of the
prime-incidence Jacobian is used.

The law does not reject the CCM route. The prolate/Sonin mechanism already supplies growing
time--frequency complexity and is the natural place where the required oscillation can reside.
The remaining theorem is to prove that the true source-selected ground state pays `(8)` at a rate
strong enough for divisor-preserving convergence or complete Weil positivity.

## 6. Orbit-sensitive boundary

Large generator norm and positive separating margin still do not select the critical line.
Symmetric polynomial orbit insertion preserves differential aperture and may leave the prime
channel Gram data unchanged if the divisor is attached externally. The determinant/kernel
transport must therefore remain pointed and orbit-sensitive in addition to satisfying `(8)`.

## 7. Scientific classification and Lean decision

The channel estimate is one Rayleigh quotient plus the fundamental theorem of calculus; prime-log
crowding uses pigeonhole and the prime number theorem. It is a route bridge and not new scientific
knowledge.

The Lean tree does not contain the strongly differentiable compressed translation orbit, the true
finite-Weil ground family, or the cofinal Gram margin. Formalizing only `(5)` would be a wrapper
around the missing analytic specialization, so no Lean file is added.

## Gates

- [x] general channel-crowding inequality proved
- [x] translation and symmetric-translation bounds proved
- [x] prime-log spacing bound proved without a prime-gap hypothesis
- [x] degree-one Euler-ray crowding reduced exactly to the top prime shell
- [x] exact incidence-margin/oscillation tradeoff proved
- [x] scalar-blind quotient form stated
- [x] positive cofinal carrier requirement isolated
- [ ] prove a lower bound for the true CCM separating margin
- [ ] prove the true ground state has the required generator growth
- [ ] combine the margin with the reduced-resolvent gap and Mellin evaluation norm
- [ ] prove orbit-sensitive cofinal inertia transport
- [ ] RH
