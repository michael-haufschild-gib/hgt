# Hardy leakage rank and unit-channel singularity of off-line-zero entry

- **ID:** euler-hardy-leakage-offline-zero-rank
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) -- scientifically non-new bridge
- **Source:** Suzuki's shifted xi quotient; Hardy factorization; Kronecker--Nehari theory
- **Statement:** `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The rank of the anti-causal
  Hardy compression of the shifted xi Euler quotient is exactly the multiplicity of the zeta zeros
  beyond the corresponding transverse line, including infinite rank. At any isolated finite
  off-line layer, the crossing multiplicity splits off as asymptotically orthogonal unit-strength
  leakage channels; for an outermost layer this is a full norm jump.

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

## Theorem C: unit-channel peeling at an arbitrary isolated layer

The outermost assumption in theorem B is unnecessary if the disappearing layer is separated from
the persistent denominator divisor. Let `a>0` be an isolated horizontal displacement, let `B_1`
be the finite Blaschke product of degree `m` made from the denominator zeros belonging to that
layer for `omega<a`, and factor

```text
B_omega=B_(0,omega) B_(1,omega).                           (9)
```

The persistent factor `B_0` may have finite or infinite degree. The model-space product identity
gives the orthogonal decomposition

```text
K_(B_omega)=K_(B_0) direct_sum B_0 K_(B_1).                (10)
```

Call the second summand the crossing channel `C_omega`. If `Q_omega` is its orthogonal projection,
then, as `omega` increases to `a`,

```text
||Q_omega L_omega* L_omega Q_omega-Q_omega|| -> 0,         (11)

||(1-Q_omega)L_omega*L_omega Q_omega|| -> 0.               (12)
```

Thus the `m` singular values of the leakage restricted to the crossing channel all tend to one,
and its image becomes asymptotically orthogonal to the leakage generated by every persistent
off-line zero. Immediately after the crossing, `B_1` is absent from the denominator and the model
space has lost precisely this `m`-dimensional channel.

When the persistent denominator has finite degree, `(11)`--`(12)` imply the spectral peeling law

```text
spectrum_nonzero(L_(a-)^* L_(a-))
 -> spectrum_nonzero(L_(a+)^* L_(a+)) union {1 repeated m times},             (13)
```

with convergence of the finite multisets after the naturally persistent block is identified. In
particular, the squared Hilbert--Schmidt leakage has the exact jump

```text
lim_(omega increases to a)||L_omega||_(S_2)^2
-lim_(omega decreases to a)||L_omega||_(S_2)^2 = m.        (14)
```

### Paper proof of theorem C

`[PROVED HERE; NOVELTY UNVERIFIED]`

Take `g=B_0 f` with `f in K_(B_1)`. On the boundary the persistent denominator cancels:

```text
L_omega g=P_- A_omega conjugate(B_1) f,
T_omega g=P_+ A_omega conjugate(B_1) f,                    (15)
```

where `T_omega=P_+ M_(Theta_omega)|H^2_+` is the complementary Toeplitz compression. The zeros of
`B_1` approach their isolated real boundary points as `omega` increases to `a`, while the residual
inner numerator is analytic and unimodular there.

The following elementary boundary-scaling lemma applies. If a finite Blaschke product `D_delta` of
degree `m` has all its zeros approach isolated boundary points at scale `delta`, and inner functions
`C_delta` are analytic there with unimodular limits after the matching local factors are removed,
then

```text
||T_(C_delta conjugate(D_delta)) | K_(D_delta)|| -> 0.      (16)
```

For one boundary point, conjugate by the unitary translation and dilation
`z=x_0+delta*zeta`. The model spaces become one fixed finite-dimensional model space, the residual
multiplier converges uniformly there to its unimodular boundary constant, and
`T_(conjugate(D))` vanishes identically on `K_D`. Multiple separated boundary points give an
asymptotically orthogonal direct sum; repeated zeros remain in the same fixed finite-dimensional
scaled model space. This proves `(16)`.

Apply `(16)` to `(15)`. Uniformly for unit `g in C_omega`, `||T_omega g||` tends to zero. Since the
boundary multiplier is unimodular,

```text
L_omega*L_omega+T_omega*T_omega=1,                         (17)
```

and `(11)` follows. If `h in K_(B_0)`, then `h` is orthogonal to `g`; using `(17)`,

```text
|inner(L_omega h,L_omega g)|
=|inner(T_omega h,T_omega g)|
<=||T_omega g||.                                           (18)
```

The convergence is uniform for unit `h` and `g`, proving `(12)` even when `B_0` has infinite
degree. For finite `B_0`, the persistent finite block converges across the layer because the local
all-pass factor tends strongly to one on that fixed model space. Equations `(11)` and `(12)` then
give `(13)`, and taking the finite trace gives `(14)`.

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

For a finite off-line divisor, `euler-leakage-residue-mode-expansion.md` makes this transport
explicit: moving the inverse Mellin contour from the Euler line to the Hardy boundary expresses the
wrong-support kernel as a finite residue sum, one exponential-polynomial block per off-line zero.

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

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The arithmetic specialization is useful, but the parent-theory
gate fails. Once the xi names are erased, theorem A is the standard kernel/rank description of a
Hankel operator with coprime inner quotient symbol, theorem B is Nehari plus a boundary Blaschke
factor, and theorem C is the standard model-space product decomposition with boundary scaling.
These are direct consequences of classical Hardy--Hankel theory applied to Suzuki's already known
shifted quotient. They remain source-transport infrastructure, not a scientific discovery.

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
  Fredholm-determinant and log-derivative operators, not `(R)` or `(J)`. The later *Chains of
  reproducing kernel Hilbert spaces generated by unimodular functions* (arXiv `2012.11121`) also
  contains no rank, residue-mode, or unit-channel version of these statements.
- The searched literature has not produced the exact cardinal identity `(R)` for zeta, its
  infinite-rank version, or the sharp norm singularity `(J)` attached to a transverse zero layer.
- The surviving research residue is not the rank or channel theorem itself. It is the open demand
  for an intrinsic arithmetic condition on the Euler source that forces the leakage-continuity
  premise without already implying equality of the completed functions.

## Open core

1. State the residual-divisor regularity needed for `(7)` in an invariant form and decide whether
   an isolated analytic `L`-family supplies it automatically.
2. Audit later citations of Suzuki and the Hardy/Hankel zeta literature for an equivalent rank
   statement.
3. Find a prime-coefficient hypothesis that implies the required operator-norm continuity; this
   would turn the conditional entry barrier into an arithmetic exclusion theorem.

## Log

- 2026-07-10 -- rank identity and norm-singularity mechanism isolated; paper proof and novelty
  audit started.
- 2026-07-10 -- kernel/divisibility proof completed for finite and infinite pole divisors; sharp
  outermost-layer norm jump proved by Nehari distance and the local Blaschke geometry.
- 2026-07-10 -- generalized the outermost jump to an arbitrary isolated finite layer: the crossing
  multiplicity becomes an asymptotically orthogonal unitary leakage block, with an exact
  Hilbert--Schmidt jump when the persistent background is finite.

## Formalization progress (2026-08-24)

`[LEAN-PROVED] [CORPUS]` The finite coprime inner-quotient rank core is now exact in
`HTGeometry.FiniteBlaschkeLeakageRank`:

- `finiteBlaschkeLeakageCore` is the canonical initial-space realization
  `P_(K_B) M_A : H² -> K_B` of anti-causal leakage;
- `norm_sq_finiteBlaschkeLeakageCore` identifies its squared norm with the exact Schur leakage
  energy `||f||²-||M_B^* M_A f||²`;
- `finiteBlaschkeLeakageCore_surjective_of_coprime` proves that coprime numerator and denominator
  make this channel onto the entire denominator model space; and
- `finrank_range_finiteBlaschkeLeakageCore_of_coprime` proves exact rank `deg B`, including
  multiplicities.

The supporting leaves `HTGeometry.FiniteBlaschkeGeneralizedSchurInertia` and
`HTGeometry.FiniteBlaschkeAdjointDefect` supply exact model-space degree, adjoint energy loss,
Hardy coprimality, and the corresponding generalized-Schur negative-index theorem. All three
leaves pass `lake env lean`; targeted leaf builds pass. New theorem axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

This is not yet the complete card and does not justify Stage 3. Remaining exact obligations are:

1. infinite Blaschke denominator/model-space dimension and the infinite-rank branch;
2. the completed-Xi shifted quotient's coprime inner factorization and divisor-multiplicity
   transport into that finite/infinite operator theorem;
3. Theorem B's outermost-layer norm singularity in the actual family; and
4. Theorem C's arbitrary-layer unit-channel peeling, persistent-block orthogonality, spectral
   multiset limit, and Hilbert--Schmidt trace jump.
