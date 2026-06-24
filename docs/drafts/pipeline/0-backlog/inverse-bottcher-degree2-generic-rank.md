# Inverse-Böttcher Degree-Two Generic Rank Guard

- **ID:** inverse-bottcher-degree2-generic-rank
- **Stage:** 0-backlog
- **Type:** CANDIDATE / micro-guard
- **Source:** research chat 2026-06-23; Nguyen inverse-coordinate Question 6.2 audit; Xie 2022 product-value audit
- **Statement:** For generic distinct quadratic parameters `c1,c2`, the standard inverse-Böttcher coordinates `X=phi_c1(z)`, `Y=phi_c2(z)` admit no algebraic relation of total degree `<=2` over `Qbar(c1,c2)(z)`.

## Goal

Record a low-degree symbolic guard for the inverse-Böttcher `phi` lane without promoting it as new branch-level knowledge. The result is useful only if it becomes an all-degree proof strategy, an invariant for exceptional loci, or a source reduction to known dynamics machinery.

## Normalization

For `f_c(z)=z^2+c`, use the standard Böttcher coordinate near infinity

`phi_c(f_c(z)) = phi_c(z)^2`, `phi_c(z)=z+O(z^-1)`.

The Laurent recurrence gives

`phi_c(z)=z + c/(2z) + c(2-c)/(8z^3) + c^2(c-6)/(16z^5)+...`.

This corrects the erroneous coefficient `c(c-1)/8` sometimes produced in informal discussion. The Chebyshev control `c=-2` gives

`phi(z)=(z+sqrt(z^2-4))/2 = z-z^-1-z^-3-...`,

matching `c(2-c)/8=-1`.

## Degree-One Check

For a putative relation

`A z + B X + C Y = 0`,

the coefficient matrix from powers `z`, `z^-1`, `z^-3` has determinant

`c1*c2*(c1-c2)/16`.

Thus there is no nontrivial linear relation for distinct nonzero `c1,c2`.

## Degree-Two Check

For total-degree `<=2` monomials

`1,z,X,Y,z^2,zX,zY,X^2,XY,Y^2`,

the Laurent coefficient matrix has generic rank `10`.

The homogeneous quadratic block on powers `z^2,z^-2,z^-4,z^-6,z^-8,z^-10` has determinant

`c1^4*c2^4*(c1+2)*(c1-c2)^4*(c2+2)*R(c1,c2) / 2^27`,

where

`R(c1,c2)=24*c1^4 -117*c1^3*c2 +124*c1^3 +186*c1^2*c2^2 -194*c1^2*c2 -2592*c1^2 -117*c1*c2^3 -194*c1*c2^2 +6536*c1*c2 -2272*c1 +24*c2^4 +124*c2^3 -2592*c2^2 -2272*c2 +14112`.

Hence no total-degree `<=2` relation exists generically away from the monomial locus `c=0`, Chebyshev locus `c=-2`, diagonal `c1=c2`, and the additional proper algebraic exceptional locus `R=0`.

## Source Audit

Nguyen proves algebraic independence for local conjugacies `psi_f` under Medvedev-Scanlon style hypotheses and explicitly asks the inverse-coordinate `phi_f=psi_f^-1` function/value question as Question 6.2. Xie 2022, Theorem 1.10, treats products of Böttcher-coordinate values and geometric invariants; it does not appear to settle function-level relations `P(z,phi_c1(z),phi_c2(z))=0`.

## Theatre Status

Current status: **HOLD / micro-guard**, not NOVEL x SIGNIFICANT.

Promotion requires one of:

1. an all-degree generic independence proof strategy;
2. a new invariant explaining the exceptional polynomial `R(c1,c2)` and its higher-degree analogues;
3. a source reduction showing the result is already implied by Xie / Nguyen / Medvedev-Scanlon machinery.

Numeric relation search is not a next step; the `D<=2` answer is already symbolic.

## Gates

- [ ] 0 -> 1 in-progress: audit Xie/Nguyen/Medvedev-Scanlon coverage more fully and decide whether this is search.
- [ ] 1 -> 2 fully-proven: either prove all-degree generic independence, prove a principled exceptional-locus theorem, or kill by source reduction.
- [ ] 2 -> 3 formalized: optional Lean/formal power-series rank certificate if the claim becomes structurally useful.
- [ ] 3 -> 4 publication-ready: only if it becomes part of a broader inverse-Böttcher independence theorem.

## Log

- 2026-06-23 — created from symbolic Laurent-rank audit after correcting the `z^-3` coefficient. Not promoted.

## 2026-06-23 correction: `R` is not the relation locus

A later audit killed the tempting interpretation that the polynomial `R(c1,c2)` is itself a new dynamical coincidence variety.

`R` is symmetric and irreducible over `Q`, but it is only the vanishing locus of one chosen homogeneous quadratic-block minor. Its vanishing does not imply that a total-degree `<=2` relation exists.

Exact check: specialize `c1=1`. Then

`R(1,d)=24*d^4 + 7*d^3 -2600*d^2 +3953*d +9396`.

A different full `D<=2` minor, using Laurent powers

`[-2,-1,0,1,2,3,4,6,8,12]`,

has determinant

`3*d^5*(d-1)^5*(d+2)*(48*d^5 +127*d^4 -6157*d^3 +5595*d^2 +22829*d +2982)/2^31`.

The gcd of this determinant with `R(1,d)` is `1`. Therefore the full degree-two coefficient matrix remains full rank at a generic point of the slice `c1=1, R=0`. A numerical check at the real root `d≈2.998646258176248` also gives rank `10`.

Updated interpretation:

- `c=0`, `c=-2`, and `c1=c2` are genuine dynamical exceptional factors;
- `R` is certificate-failure noise for one minor, not a proven exceptional locus;
- any future exceptional-locus theorem must use all relevant minors / elimination, not one convenient determinant factor.

Status remains **HOLD / micro-guard**. The proposed promotion of `R` as a new algebraic variety is killed.

## 2026-06-23 cross-transfer fork

After killing `R` as an exceptional variety, the only scalable object left in this lane is the cross-transfer map.

Let `psi_c` denote the local conjugacy with

`psi_c(t^2)=psi_c(t)^2+c`,

and let `phi_c=psi_c^{-1}` be the Böttcher coordinate near infinity. For two parameters define

`H_12(t)=phi_c2(psi_c1(t))`.

Then

`psi_c2(H_12(t))=psi_c1(t)`

and the exact transfer equation is

`psi_c2(H_12(t^2)) = psi_c2(H_12(t)^2) + (c1-c2)`.

Equivalently,

`H_12(t^2)=phi_c2(psi_c2(H_12(t)^2)+(c1-c2))`.

This isolates why Nguyen's `psi` theorem does not directly settle the inverse-coordinate `phi` question: Nguyen controls algebraic dependence of `psi_f(u(t))` for polynomial/monomial substitutions `u`; the inverse-coordinate relation introduces the unknown cross-transfer `H_12`, with an additive parameter defect inside the `c2` Böttcher chart.

Updated fork:

1. **Rigidity route:** prove that any algebraic relation `P(z,phi_c1(z),phi_c2(z))=0` forces the associated `H_12` into a field/class where the defect equation implies `c1=c2` or the monomial/Chebyshev exceptions.
2. **Source-reduction route:** show the same rigidity is already a consequence of Nguyen/Xie/Medvedev-Scanlon or adjacent invariant-variety machinery.
3. **Invariant route:** define a source-new invariant of the defect term `c1-c2` in the `c2` chart that gives an all-degree obstruction and survives label stripping.

Anything else, including further low-degree determinant searches, remains micro-guard work and should not be promoted.
