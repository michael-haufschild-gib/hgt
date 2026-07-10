# Hardy leakage rank and the norm singularity of off-line-zero entry

- **ID:** euler-hardy-leakage-offline-zero-rank
- **Stage:** 2-fully-proven/needs-audit
- **Type:** THEOREM (paper) -- complete proof; external novelty audit open
- **Source:** Suzuki's shifted xi quotient; Hardy factorization; Kronecker--Nehari theory
- **Statement:** `[PROVED HERE; CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]` The rank of the anti-causal
  Hardy compression of the shifted xi Euler quotient is exactly the multiplicity of the zeta zeros
  beyond the corresponding transverse line, including infinite rank. At an isolated outermost
  off-line layer, this operator has a full norm jump when the layer crosses the sampling line.

## Goal

Identify a global infinite-Euler-data constraint that does more than record a local collision. The
constraint must use neither a zero height cutoff nor a jet at a zero. It should say what has to fail
in the global prime-side operator when an off-line zero enters the critical line.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea, literature parents identified
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem, build green, axiom check pass
- [ ] 3 -> 4 publication-ready: standalone paper and external novelty review

## Setup

For `omega>0`, let

```text
Theta_omega(z)=xi(1/2-omega-iz)/xi(1/2+omega-iz).
```

Its boundary values on the real axis have modulus one almost everywhere. Let `H^2_+` be the Hardy
space of the upper half-plane, let `P_-` be the orthogonal projection of `L^2(R)` onto the lower
Hardy space, and define the Hardy leakage operator

```text
L_omega = P_- M_(Theta_omega) | H^2_+ .                    (L)
```

Under the Mellin--Fourier transform used by Suzuki, `(L)` is unitarily equivalent to

```text
1_(0,1) widehat(Theta_omega) 1_(1,infinity),               (M)
```

the part of the multiplicative convolution by the inverse Mellin transform of `Theta_omega` that
sends input supported above one to output below one. Thus `L_omega` is the exact anti-causal or
wrong-support leakage of the global shifted Euler quotient.

Call `omega` nonexceptional if the numerator and denominator have no common nonreal zero; at an
exceptional shift cancel their common inner divisor before counting.

## Theorem A: exact leakage rank

For every `omega>0`, after common-divisor cancellation,

```text
rank(L_omega)
= sum_(xi(rho)=0, Re rho>1/2+omega) multiplicity(rho),      (R)
```

where both sides may be infinite.

Equivalently, the full transverse off-line divisor filtration is the rank filtration of one family
of global support-leakage operators. In particular, RH is equivalent to `L_omega=0` for every
`omega>0`, while `(R)` retains the cardinal information discarded by this Boolean criterion.

## Paper proof of theorem A

`[PROVED HERE; NOVELTY UNVERIFIED]`

The centered xi function is Cartwright, so the unimodular bounded-type quotient admits a coprime
inner quotient factorization in the upper half-plane,

```text
Theta_omega = A_omega/B_omega .                            (1)
```

There is no denominator singular exponential because the quotient has zero mean type. The zeros of
`B_omega` are exactly the uncancelled poles of `Theta_omega`, hence exactly the zeros
`rho=beta+i gamma` with `beta>1/2+omega`, under the correspondence

```text
rho -> -gamma+i(beta-1/2-omega).                           (2)
```

On the real boundary, `(1)` is `A_omega conjugate(B_omega)`. If `f=B_omega g` with `g in H^2_+`,
then `Theta_omega f=A_omega g` lies in `H^2_+`, so `B_omega H^2_+` is contained in the kernel of
`L_omega`.

Conversely, if `L_omega f=0`, then `Theta_omega f=g` for some `g in H^2_+`, and therefore

```text
A_omega f=B_omega g.                                      (3)
```

Coprimeness of the inner factors implies that `B_omega` divides the inner factor of `f`.
Consequently

```text
kernel(L_omega)=B_omega H^2_+.                             (4)
```

The quotient `H^2_+/B_omega H^2_+` is the model space `K_(B_omega)`. Its dimension is the degree of
the Blaschke product `B_omega`, with infinite dimension for an infinite denominator divisor. Since
the operator induced by `L_omega` on this quotient is injective, `(4)` gives

```text
rank(L_omega)=dim K_(B_omega)=degree(B_omega).              (5)
```

For an infinite Blaschke denominator, the same divisibility argument is literal: equation `(3)`
says that the inner factor of `A_omega f` contains every zero of `B_omega` with its multiplicity.
Because `A_omega` and `B_omega` are coprime, the inner factor of `f` contains the whole Blaschke
product `B_omega`. Thus `(4)` holds without a finiteness hypothesis, and the model space is
infinite-dimensional exactly when the pole divisor is infinite. Equations `(2)` and `(5)` prove
`(R)`, including the value infinity.

## Theorem B: full norm singularity at an isolated outermost layer

Assume that a zero quartet has right-hand member

```text
rho=1/2+a+i gamma,   a>0,
```

of multiplicity `m`, and that no other pole of `Theta_omega` crosses the real boundary near
`z=-gamma` when `omega` crosses `a`. Suppose also that for `omega>a` there is no remaining
denominator inner factor; equivalently this is the outermost and last off-line layer for the leakage
operator under consideration. Then

```text
lim_(omega increases to a) ||L_omega|| = 1,
L_omega=0 for omega>a sufficiently close to a.              (J)
```

Thus the layer cannot cross under operator-norm continuity of the global Euler leakage. A line
entry in a deformation, for which `a(t)` tends to zero, drives this unit norm jump to the corner
`(t,omega)=(t_entry,0)`.

More quantitatively, along `omega=lambda*a` with fixed `0<lambda<1`, the local denominator and
numerator Blaschke zeros are

```text
b=-gamma+i(1-lambda)a,
c=-gamma+i(1+lambda)a,
```

and the half-plane Blaschke factor at `c` satisfies

```text
|b_c(b)|=lambda.                                           (6)
```

For multiplicity `m`, the local factor contributes `lambda^m`. Therefore any isolated entry with
tame residual inner divisor obeys

```text
liminf_(t -> t_entry) ||L_(t,lambda*a(t))|| >= lambda^m.    (7)
```

Taking `lambda` arbitrarily close to one gives a sharp unit-size two-parameter corner obstruction.

## Paper proof of theorem B

`[PROVED HERE; NOVELTY UNVERIFIED]`

Write `Theta=A/B` in coprime inner form. Nehari's theorem and multiplication by the inner function
`B` give, for every zero `b` of `B`,

```text
||L_omega||
= distance_(L-infinity)(A conjugate(B), H-infinity)
= inf_(q in H-infinity) ||A-Bq||_infinity
>= |A(b)|.                                                 (8)
```

As an isolated denominator zero approaches the boundary, the associated numerator and denominator
local factors have the geometry in `(6)`. If `omega` tends to `a` from below, their ratio tends to
one and all residual inner factors have unimodular nontangential limit at `-gamma`. Hence
`|A(b)|` tends to one. Since multiplication by a unimodular symbol and orthogonal projection give
`||L_omega||<=1`, equation `(8)` proves the first part of `(J)`. On the pole-free side `Theta` is
inner, so its multiplication preserves `H^2_+` and `L_omega=0`.

Along an entering family with `omega=lambda*a(t)`, equation `(6)` instead gives the lower bound
`lambda^m`; the residual-factor hypothesis makes its remaining modulus tend to one. This proves
`(7)`. The upper bound one follows directly from `|Theta|=1` almost everywhere and the fact that
`P_-` is an orthogonal projection, so the norm limits are sharp.

## Euler-data realization

For `Im z>1/2+omega`, both shifted xi arguments lie in `Re s>1`, and

```text
Theta_omega(z)
= pi^omega
  * s_minus(s_minus-1)/(s_plus(s_plus-1))
  * Gamma(s_minus/2)/Gamma(s_plus/2)
  * product_p (1-p^(-s_plus))/(1-p^(-s_minus)).             (E)
```

Suzuki's inverse Mellin construction recovers the convolution in `(M)` from this high-line
function. Consequently the rank and norm constraints above are constraints on the complete
infinite Euler data together with the explicit archimedean factor; they do not evaluate xi in the
critical strip and do not use jets at a zero.

The entry barrier can be stated purely on the source side:

```text
If the anti-causal compression of the shifted Euler convolution is jointly norm-continuous down
to omega=0, an isolated off-line zero cannot enter the critical line.
```

An entry can evade this only through a global failure of that continuity, or through a simultaneous
nonlocal degeneration of the residual inner divisor that destroys the isolation/tameness premise.

## General self-dual completed Euler products

The argument uses only a centered Cartwright completion, a self-dual functional equation,
unimodular boundary values, and an absolutely convergent Euler product in `Re s>1`. It therefore
extends to self-dual completed `L`-functions after including the root number in `Theta` and clearing
known symmetric poles.

## Novelty and significance audit

- Suzuki (2012) introduced this exact `Theta_omega`, its model-space kernel, its inverse Mellin
  convolution, and the Boolean statement that innerness is equivalent to absence of wrong-support
  leakage; this is Theorem 2 in *A canonical system of differential equations arising from the
  Riemann zeta-function*, arXiv `1204.1827`.
- The factorization `Theta=A/B`, the model-space identity `dim K_B=degree(B)`, Kronecker finite-rank
  theory, and Nehari's distance theorem are classical. A standard source is V. Peller,
  *Hankel Operators and Their Applications*, Springer (2003), DOI
  `10.1007/978-0-387-21681-2`. These operator-theoretic parents are not claimed novelty.
- The searched Suzuki source contains no negative-square count, no rank formula for the wrong-side
  compression, and no operator-norm threshold or entry theorem.
- A citation-chain audit of Suzuki's paper found the later canonical-system and Selberg-class
  extensions (including arXiv `1606.05726`) but no rank cardinalization. A separate audit of
  Suzuki's *Integral operators arising from the Riemann zeta function* (arXiv `1907.07302`) found
  Fredholm-determinant and log-derivative operators, not `(R)` or `(J)`.
- The searched literature has not produced the exact cardinal identity `(R)` for zeta, its
  infinite-rank version, or the sharp norm singularity `(J)` attached to a transverse zero layer.
- Candidate novelty is therefore the arithmetic synthesis: the off-line divisor is exactly the
  rank of a prime-determined anti-causal leakage operator, and crossing a transverse layer is a
  norm-singular event in the global Euler operator.
- Significance is stronger than a new RH equivalent: `(R)` counts all off-line zeros, and `(J)`
  identifies a precise global regularity condition that actually forbids entry.

## Open core

1. State the residual-divisor regularity needed for `(7)` in an invariant form and decide whether
   an isolated analytic `L`-family supplies it automatically.
2. Extend `(J)` from the last off-line layer to the appropriate approximation-number jump when
   other denominator zeros remain.
3. Audit later citations of Suzuki and the Hardy/Hankel zeta literature for an equivalent rank
   statement.

## Log

- 2026-07-10 -- rank identity and norm-singularity mechanism isolated; paper proof and novelty
  audit started.
- 2026-07-10 -- kernel/divisibility proof completed for finite and infinite pole divisors; sharp
  outermost-layer norm jump proved by Nehari distance and the local Blaschke geometry.
