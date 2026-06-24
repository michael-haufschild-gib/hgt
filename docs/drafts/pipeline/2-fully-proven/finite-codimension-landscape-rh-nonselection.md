# Finite-Codimension Landscape RH Nonselection

- **ID:** finite-codimension-landscape-rh-nonselection
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / landscape-proof guardrail
- **Source:** `rh-landscape-proof-gate.md`; finite-probe nonselection
- **Statement:** No constraint landscape that is finite-codimensional in the
  even-polynomial perturbation directions can select RH. If the landscape contains
  `Xi(t)=xi(1/2+i t)` and is locally thick along a finite-codimension polynomial-tail
  subspace, then it also contains even real order-one entire functions with off-line
  zero quartets.

## Setup

Let

`Xi(t)=xi(1/2+i t)=Phi(t^2)`.

Let `U` be a real vector subspace of `R[u]` of finite codimension. Think of

`Xi(t) + R(t^2)`, `R in U`,

as the local polynomial-tail slice of a proposed constraint landscape. Finite
Taylor conditions, finitely many moment/value/passport conditions, and finite
symbolic audits all cut out such finite-codimension slices.

For a fixed `N>=0`, impose seam-jet preservation by replacing `U` with

`U_N = U cap u^(N+1) R[u]`.

This is still finite-codimensional inside `u^(N+1) R[u]`, hence infinite-dimensional.

## Theorem

For every finite-codimensional real subspace `U <= R[u]` and every `N>=0`, there are
a non-real `u0` and a polynomial `R in U cap u^(N+1) R[u]` such that:

1. `R(u0)=-Phi(u0)`;
2. for either square root `tau` of `u0`,

   `F(t)=Xi(t)+R(t^2)`

   is even, real on the real axis, entire of order `1`, agrees with `Xi` through
   derivatives `0,...,2N+1` at `t=0`, belongs to the finite-codimension landscape
   slice, and has the non-real zero quartet
   `tau,-tau,conj(tau),-conj(tau)`.

Therefore a finite-codimension local landscape cannot force RH.

## Proof

Since `U_N` is infinite-dimensional, choose linearly independent polynomials
`P,Q in U_N` with `Q != 0`. Then `P/Q` is a nonconstant rational function. As in
finite linear-probe nonselection, there is a non-real `u0` with `Q(u0) != 0` and
`P(u0)/Q(u0) notin R`: otherwise the rational function `P/Q` would be real-valued
on a nonempty open subset of the upper half-plane, contradicting the open mapping
theorem.

Thus `P(u0)` and `Q(u0)` span `C` over `R`. Choose real `a,b` with

`aP(u0)+bQ(u0)=-Phi(u0)`.

Set

`R=aP+bQ`.

Then `R in U_N`, so the finite-codimension landscape constraints and the seam-jet
vanishing are preserved. Defining

`F(t)=Xi(t)+R(t^2)`

gives an even real entire function of order `1`. The order is still `1` because a
polynomial cannot cancel the non-polynomial order-one function `Xi`. Since `R` is
divisible by `u^(N+1)`, the perturbation `R(t^2)` vanishes to order `2N+2` at the
seam. Finally, with `tau^2=u0`,

`F(tau)=Phi(u0)+R(u0)=0`,

and evenness plus real symmetry gives the full quartet. Since `u0` is non-real, this
quartet is off the real `t`-axis, so `F` violates RH.

## Consequence for the RH Route

The user-level slogan "prove the landscape, not a generator" has a precise negative
edge:

> The landscape cannot be a finite-codimension constraint around `Xi` in local
> polynomial-tail directions.

Any such landscape is too thick; it contains false-nearby functions with the same
finite local/passport data and with off-line zeros. A viable RH landscape must be
infinite-codimensional/all-order in exactly the sense supplied by a genuine Euler
product, the completed explicit formula as a full distributional identity, a
geometric polarization, or an equivalent source rigidity theorem.

Thus the next proof obligation is not a finite extra condition on the rank-one Weyl
chart. It is an all-order source theorem that prevents these polynomial-tail
perturbations before zero-location language appears.

## Source Boundary

This theorem is elementary linear algebra plus one complex-analysis observation. Its
significance is methodological: it rules out a class of landscape-shaped but finite
constraint proposals. It does not preserve the Euler product; the fact that Euler
product structure is destroyed is precisely why the Euler product must be part of any
viable all-order landscape.

## Gates

- [x] 0 -> 1 in-progress: finite-codimension landscape failure isolated.
- [x] 1 -> 2 fully-proven: proof by finite-codimension polynomial-tail perturbation.
- [ ] 2 -> 3 formalized: optional linear-algebra skeleton; the open mapping step can be
  imported or replaced by an explicit polynomial choice in a stronger formal version.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal to translate finite-probe
  nonselection into the stricter landscape language: a candidate constraint class must
  be all-order/infinite-codimensional, not a finite local audit.
