# Neutral Gamma ratios activate an all-degree polynomial jet boundary

- **ID:** `neutral-gamma-ratio-polynomial-jet-boundary-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [BRIDGE]`
- **Statement:** For every `theta>0`, every upper translation sequence of the neutral HT Gamma ratio
  `G_theta(s)=Gamma(s+i theta)/Gamma(s)` has a subsequence whose phase error and inverse height blow
  up to one nonzero affine coordinate. Vanishing order becomes the power of that coordinate. Hence
  individual boundaries realize jets of every degree, while every finite polynomial coefficient
  tuple has a constant functional-projective boundary.

## 1. The object and its frozen phase

Fix `theta>0` and put

```text
G_theta(s)=Gamma(s+i theta)/Gamma(s),
A_theta=exp(-pi theta/2),
T_n=exp(2 pi n/theta).                                     (1)
```

The ratio is neutral: its common-scale orbit charges are `+1` on `i theta+Z` and `-1` on `Z`, so
their total is zero. The two orbits are distinct.

The chosen heights freeze the logarithmic phase because, with the upper-sector branch of `log`,

```text
(i T_n)^(i theta)
 =exp(i theta log T_n-pi theta/2)
 =A_theta.                                                  (2)
```

Define the nonconstant affine jet

```text
L_theta(s)=theta s+theta(i theta-1)/2.                     (3)
```

## 2. First-jet theorem

`[PROVED HERE]` Locally uniformly for `s` on every compact subset of `C`,

```text
(T_n/A_theta)(G_theta(s+i T_n)-A_theta)
  ->L_theta(s).                                             (4)
```

### Proof

The classical Gamma-ratio expansion, uniformly in every closed sector avoiding the negative real
axis, is

```text
Gamma(z+a)/Gamma(z+b)
 =z^(a-b)(1+(a-b)(a+b-1)/(2z)+O(z^(-2))).                 (5)
```

Apply `(5)` with `a=i theta`, `b=0`, and `z=s+iT_n`. Its first coefficient is

```text
c_1=i theta(i theta-1)/2.                                  (6)
```

Uniformly on compact `s`-sets,

```text
(s+iT_n)^(i theta)
 =A_theta(1+theta s/T_n+O(T_n^(-2))),                      (7)

c_1/(s+iT_n)
 =theta(i theta-1)/(2T_n)+O(T_n^(-2)).                     (8)
```

Multiplying `(7)` by the bracket in `(5)` gives

```text
G_theta(s+iT_n)
 =A_theta(1+L_theta(s)/T_n+O(T_n^(-2))).                  (9)
```

The remainder is locally uniform, so `(4)` follows.

## 3. Vanishing order becomes jet degree

`[PROVED HERE]` Let `Q in C[X]` be nonzero and suppose its zero at `A_theta` has multiplicity
`m>=0`. Then

```text
(T_n/A_theta)^m Q(G_theta(s+iT_n))
 ->Q^(m)(A_theta)/m! * L_theta(s)^m                        (10)
```

locally uniformly. For `m=0`, the right side is `Q(A_theta)`.

### Proof

Factor

```text
Q(X)=(X-A_theta)^m U(X),  U(A_theta)!=0.                   (11)
```

Equation `(4)` gives

```text
(T_n/A_theta)^m(G_theta(s+iT_n)-A_theta)^m
 ->L_theta(s)^m.                                           (12)
```

Equation `(9)` gives `U(G_theta(s+iT_n))->U(A_theta)` locally uniformly. Since
`U(A_theta)=Q^(m)(A_theta)/m!`, multiplying proves `(10)`.

## 4. Universal phase--height blow-up

`[PROVED HERE]` Let `S_n->+infinity` be arbitrary. After passing to a subsequence,

```text
a_n=(i S_n)^(i theta) ->A,  |A|=A_theta.                  (10a)
```

Put

```text
d_n=|a_n-A|+1/S_n.                                        (10b)
```

After one further subsequence there are `lambda in C` and `mu in R_(>=0)` with

```text
(a_n-A)/d_n ->lambda,
(1/S_n)/d_n ->mu,
|lambda|+mu=1,                                             (10c)
```

and

```text
(G_theta(s+iS_n)-A)/d_n
 ->H(s)=lambda+mu A L_theta(s).                            (10d)
```

The affine function `H` is not identically zero. If `Q in C[X]` has a zero of multiplicity `m` at
`A`, then

```text
d_n^(-m) Q(G_theta(s+iS_n))
 ->Q^(m)(A)/m! * H(s)^m.                                  (10e)
```

All convergence is locally uniform.

### Proof

Compactness of the circle `|a|=A_theta` gives `(10a)`. The same ratio expansion used in `(9)` gives

```text
G_theta(s+iS_n)
 =a_n(1+L_theta(s)/S_n+O(S_n^(-2))).                      (10f)
```

Divide

```text
G_theta(s+iS_n)-A
 =(a_n-A)+a_n L_theta(s)/S_n+O(S_n^(-2))                  (10g)
```

by `d_n`. The pairs in `(10c)` lie in a compact set and satisfy the displayed norm identity, so a
subsequence converges. Also `S_n^(-2)/d_n<=S_n^(-1)->0`. This proves `(10d)`. If `mu=0`, then
`|lambda|=1`; if `mu>0`, the coefficient `mu A theta` of `s` is nonzero. Hence `H` is nonzero.
Taylor factorization of `Q` at `A`, exactly as in `(11)`--`(12)`, proves `(10e)`.

The frozen sequence `(1)` has `a_n=A_theta`, `d_n=1/T_n`, `lambda=0`, and `mu=1`; thus `(4)` and
`(10)` are the normalized special case of this universal law.

## 5. Finite tuples have a constant projective boundary

`[PROVED HERE]` Let `(Q_1,...,Q_r)` be a finite nonzero tuple in `C[X]`. For every `S_n->infinity`,
after the subsequence in Section 4, let

```text
m=min_j ord_A(Q_j).                                        (10h)
```

Then

```text
d_n^(-m)(Q_1(G_theta(s+iS_n)),...,Q_r(G_theta(s+iS_n)))
 ->H(s)^m(c_1,...,c_r),                                    (10i)
```

where

```text
c_j=Q_j^(m)(A)/m!  if ord_A(Q_j)=m,
c_j=0              otherwise,                              (10j)
```

and the constant vector `c` is nonzero. Dividing the limit tuple by its common nonzero function
`H^m` gives the constant projective point `[c_1:...:c_r]`.

### Proof

Apply `(10e)` to each component. Components with larger vanishing order acquire an additional
factor `d_n` and vanish; at least one component has order `m`, so the constant vector is nonzero.

The distinction is exact:

```text
elementwise scalar boundary -> polynomial jets of all degrees,
finite-tuple functional-projective boundary -> one constant point.          (10k)
```

## 6. Recurrent consequence for rational Gamma-coordinate coefficients

`[PROVED HERE]` Let `f` be holomorphic and vertically Bohr uniformly almost periodic on a vertical
strip. Suppose `f` satisfies a nonzero ADE whose finite coefficients lie in `C(G_theta)`. Then `f`
satisfies a nontrivial autonomous ADE and has finite rational Bohr-frequency rank. The same
finite-rank conclusion holds for every continuous translation-equivariant observable of its
nonzero divisor.

### Proof

Clear the common denominators of the ADE coefficients, obtaining a finite nonzero polynomial tuple
`(Q_j(G_theta))`. Choose positive simultaneous return times `S_n->infinity` for `f` and all
derivatives occurring in the equation. Apply Section 5. Translation, scalar normalization, and
local uniform convergence give a limiting relation

```text
H(s)^m P_c(f(s),f'(s),...,f^(N)(s))=0.                    (10l)
```

Since `H` is not identically zero and `c` is nonzero, the identity theorem gives the nontrivial
autonomous ADE `P_c(f,...)=0`. The autonomous implicit-ADE frequency theorem gives finite Bohr rank
and its divisor-observable consequence.

This theorem is deliberately for coefficients rational in the Gamma coordinate itself. Extending
it to the full differential field `C(s)<G_theta>` requires simultaneous control of rational
`s`-weights and the logarithmic-derivative field; that is the remaining general signed-Gamma core.

## 7. Hypertranscendence

`[PROVED HERE; BRIDGE]` The function `G_theta` is hypertranscendental over `C(s)`.

Indeed, put `Psi=G_theta'/G_theta` and `Tau=Psi'`. Gamma recurrence gives

```text
Tau(s+1)-Tau(s)=1/s^2-1/(s+i theta)^2.                     (13)
```

The two order-two poles lie in distinct integer-shift orbits and have nonzero discrete residues.
Thus the right side `r(s)` of `(13)` is not a rational shift difference. With
`rho(F)(s)=F(s+1)` and `q=rho(r)/r`, the formal expansion satisfies the homogeneous rational shift
equation

```text
(rho-q)(rho-1)hat(Tau)=0.                                  (13a)
```

The Adamczewski--Dreyfus--Hardouin formal shift dichotomy says that `hat(Tau)` is rational or HT.
The rational alternative would give a rational solution of `(13)`, contrary to the discrete
residues. Hence `hat(Tau)` is HT. Therefore its formal primitive `hat(Psi)` is HT as well. An
analytic ADE would pass to the full sectorial expansion, so analytic `Psi` is HT. Since a DA
`G_theta` would have DA logarithmic derivative, `G_theta` is HT.

This HT proof is the one-ratio specialization of
`../needs-audit/signed-archimedean-gamma-orbit-charge-phase-law.md` and is not claimed as new.

## 8. The positive boundary law

Taking `Q_m(X)=(X-A_theta)^m` in `(10)` gives, for every `m>=1`,

```text
(T_n/A_theta)^m Q_m(G_theta(s+iT_n))
 ->L_theta(s)^m.                                           (14)
```

Because `L_theta` is affine and nonconstant, the upper projective boundary contains polynomial
jets of arbitrarily high degree. More precisely:

> **Vanishing-order/jet-degree law.** At the frozen logarithmic phase `A_theta`, algebraic
> vanishing order in the Gamma coordinate is converted exactly into polynomial degree in the local
> translation coordinate.

This is positive carrier information. Neutral hypertranscendence does not merely leave a point or
a recurrent phase: on the log-resonant locus it necessarily exposes a noncompact polynomial-jet
carrier.

The law also separates two invariants that must not be conflated:

```text
recurrent character rank of the jets =0,
available polynomial jet degree       =unbounded.          (15)
```

Thus arbitrarily deep archimedean jets do not manufacture even one prime-log character.

## 9. Consequence for RH architectures

The positive implementation requirement is two-coordinate:

```text
archimedean jet depth  +  arithmetic character rank.       (16)
```

The ratio `G_theta` can supply unbounded finite jet depth through `(14)`, but it supplies no
prime-frequency direction. Therefore:

1. **Connes / Hilbert--Polya / de Branges.** Gamma-ratio jets may enter local determinant or
   canonical-system coefficients, while the operator must carry the prime character module as a
   separate compact phase factor.
2. **Nyman--Beurling / Weil positivity.** Increasing derivative or endpoint-jet order is not a
   substitute for growing test-space character rank; both coordinates must be controlled
   cofinally.
3. **Li-type criteria.** Arbitrarily many archimedean Taylor corrections remain rank-zero in the
   prime-frequency coordinate. The coefficient hierarchy must preserve the Euler character module
   independently.
4. **Finite-prime cutoffs.** Retaining primes through `N` still requires total compact phase
   dimension at least `pi(N)`. The all-degree jet tower `(14)` changes local differential
   complexity but contributes zero to that dimension, including across a `1/log N` boundary layer.

This is not a categorical verdict on any named criterion. It states the two resources every viable
implementation must identify and prevents polynomial jet depth from being counted as arithmetic
phase capacity.

## 10. Attacks and sharp boundaries

1. **The earlier one-point neutral claim is false.** Equation `(4)` is an explicit nonconstant
   boundary limit when `beta=0`.
2. **The rank-zero statement is not contradicted.** A polynomial has no nonzero Bohr frequency; the
   new carrier is noncompact jet depth, not recurrent character rank.
3. **The law is exact, not merely first-order evidence.** Equation `(10)` treats every polynomial
   and identifies the limit from its exact vanishing multiplicity.
4. **The degree is unbounded across the field, not for one fixed coefficient tuple.** Each fixed
   polynomial has finite degree, while the family `Q_m` realizes every `m`.
5. **`theta=0` is excluded.** Then `G_theta=1`, the orbit charges cancel in the same orbit, and the
   HT and jet mechanisms both disappear.
6. **Complex shifts are load-bearing.** The moving logarithmic phase comes from `Im(i theta)!=0`.
   Real neutral exponents do not produce this frozen-phase jet activation.
7. **Arbitrary return sequences are included.** Section 4 resolves every relative rate between
   phase convergence and inverse height; no Diophantine synchronization with the frozen sequence is
   assumed.
8. **The jet is projectively common.** Section 5 proves that a finite polynomial coefficient tuple
   carries one common affine power. It therefore leaves a constant autonomous relation after
   functional projectivization.

## 11. Parent and novelty audit

`[BRIDGE]`

- Tricomi--Erdelyi and later work give the complete asymptotic expansion of
  `Gamma(z+a)/Gamma(z+b)`; equation `(5)` is classical.
- Discrete shift residues and the Adamczewski--Dreyfus--Hardouin theorem supply the HT bridge.
- Full parent/priority audit refreshed 2026-08-23 across classical Gamma-ratio asymptotics,
  product-ratio expansions, shift hypertranscendence, meromorphic shift-equation classifications,
  almost-periodic function algebras, logarithmic phases, vertical translation limits, projective
  boundaries, and polynomial jet activation. It did not locate `(4)`, `(10a)`--`(10k)`, or `(14)`
  as a boundary-carrier theorem. This is a literature-search conclusion, not a priority claim beyond
  the searched corpus.
- The exact conversion of phase-vanishing multiplicity into polynomial jet degree is a short
  consequence of the classical ratio expansion and Taylor factorization. It is scientifically
  useful because it falsifies the former neutral boundary conjecture, but it does not pass the
  parent-theory novelty gate. The genuinely open scientific target is the uniform finite-depth
  phase--jet--Stokes classification for the full signed-Gamma differential field.

Primary adjacent sources:

- F. G. Tricomi and A. Erdel'yi, *The asymptotic expansion of a ratio of gamma functions*, Pacific
  J. Math. 1 (1951), 133--142; see also [DLMF §5.11(iii)](https://dlmf.nist.gov/5.11#iii).
- W. Bühring, [*Asymptotic expansions for ratios of products of gamma
  functions*](https://arxiv.org/abs/math/0206200), Int. J. Math. Math. Sci. 2003, 1167--1171.
- B. Adamczewski, T. Dreyfus, C. Hardouin,
  [*Hypertranscendence and linear difference equations*](https://arxiv.org/abs/1910.01874),
  J. Amer. Math. Soc. 34 (2021), 475--503, DOI `10.1090/jams/960`.
- T. Dreyfus, [*Hypertranscendence and linear difference equations, the exponential
  case*](https://arxiv.org/abs/2212.00388), J. Algebra 686 (2026), 775--792.

## 12. Lean status

Complete unconditional Lean formalization:

- module: `GaloisForLFunctions.HTGeometry.NeutralGammaRatioPolynomialJetBoundary`;
- exact quantitative global first-jet theorem, frozen phase/height sequence, and compact-open frozen
  polynomial root-multiplicity law;
- arbitrary escaping-sequence compact phase extraction, exact `|lambda|+mu=1` normalization,
  nonzero affine compact-open blow-up, and arbitrary polynomial multiplicity law;
- finite tuples with zero-coordinate support, exact minimum order, derivative coefficients,
  nonzero constant projective vector, and common affine power;
- rational neutral-Gamma coefficient class constant functional-projective boundary, recurrence to a
  nonzero autonomous ADE, finite Bohr-hull rank, and inherited rank bound for every continuous
  carrier observable;
- meromorphic carrier hypertranscendence and exact all-degree polynomial carrier law;
- umbrella import wired; targeted `lake env lean` and targeted `lake build` passed warning-free;
- new capstone axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`; no
  `sorry`, `admit`, declared `axiom`, `opaque`, or `unsafe` declaration occurs in the module.

Global `scripts/formal_tools.py lint` was also run. The new module is reachable and clean; the global
run remains red only on three unrelated concurrently owned modules missing their umbrella imports:
`ArbitraryFamilyPowerQuotientResidue`, `DifferentialAdjoinCoordinateScale`, and
`DifferentialAdjoinFiniteSupport`.

## Gates

- [x] exact first-jet limit proved
- [x] all-polynomial multiplicity law proved
- [x] arbitrary-sequence phase--height blow-up classified
- [x] finite polynomial tuples reduced to one projective point
- [x] recurrent rational-coordinate consequence proved
- [x] HT of the carrier proved
- [x] smallest and degenerate cases attacked
- [x] internal proof audit and arbitrary-sequence attack passed
- [x] full parent-literature and priority audit
- [x] complete unconditional Lean formalization
