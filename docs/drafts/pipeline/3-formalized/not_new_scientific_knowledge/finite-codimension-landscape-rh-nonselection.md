# Finite-Codimension Landscape RH Nonselection

- **ID:** finite-codimension-landscape-rh-nonselection
- **Stage:** 3-formalized
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
- [x] 2 -> 3 formalized: `RHTower/FiniteProbeRHNonselection.lean`; the open-mapping step is replaced by an algebraic argument.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal to translate finite-probe
  nonselection into the stricter landscape language: a candidate constraint class must
  be all-order/infinite-codimensional, not a finite local audit.

## 2026-08-16 Lean closure

`RHTower/FiniteProbeRHNonselection.lean` builds the perturbation construction on the actual
centered completed function, unconditionally.

`xiPerturbed R t = XiC t + R(t^2)` is `Xi_R`.  Its structural clauses are proved once and for all:

- `xiPerturbed_even`: `Xi_R(-t) = Xi_R(t)`, the functional-equation parity.
- `xiPerturbed_conj` and `xiPerturbed_ofReal_im`: Schwarz reality, and `Xi_R` real on the real axis.
- `xiPerturbed_differentiable`: `Xi_R` is entire.
- `xiPerturbed_order`: `Xi_R` carries the same order-one envelope
  `||Xi_R(t)|| <= exp(C (1 + ||t||) log(2 + ||t||))` that the corpus proves for `xi`
  (`XiC_order`, from `xi_growth_order_le_one`).  Moreover `xiPerturbed_sub_XiC` shows
  `Xi_R - Xi` is a polynomial function, so `Xi_R` lies in exactly the same growth class as `Xi`;
  that is the content of the cards' "entire of order 1" clause, and it is proved without any
  lower bound on the order of `xi`.
- `xiPerturbed_seamJet`: if `X^(N+1)` divides `R` then `Xi_R - Xi` equals `t^(2N+2)` times an
  entire function, i.e. it vanishes to order at least `2N+2` at the seam.  This is clause 1 of the
  seam-jet statement; the derivative reformulation `Xi_R^(j)(0) = Xi^(j)(0)` for `j <= 2N+1` is the
  standard restatement of the same divisibility.

The two algebraic inputs are proved from scratch:

- `exists_indep_pair_of_finiteCodim`: for any real subspace of finite codimension `<= m` in
  `R[X]` and any `N`, the slice `W cap X^(N+1) R[X]` contains two `R`-independent polynomials.
  The proof is a rank count on the `m+2` monomials `X^(N+1), ..., X^(N+m+2)` followed by an
  elementary extraction of a second vector outside the span of the first.
- `exists_nonreal_spanning`: two `R`-independent real polynomials take, at some non-real point,
  values spanning `C` over `R`.  **The card's open-mapping step is replaced by an algebraic
  argument**: if the values were `R`-dependent at every non-real point, then for each real shift
  `c` the polynomial `P(z - ic) Q(z + ic) - P(z + ic) Q(z - ic)` would vanish on the whole real
  axis, hence identically; evaluating it at `z = a + ic` shows `P(a) Q - Q(a) P = 0` for every
  complex `a`, and a real point where `Q` does not vanish forces `P` and `Q` proportional.

Axioms of every theorem listed: `propext`, `Classical.choice`, `Quot.sound`.

Card-specific.  `exists_offLine_perturbation_of_finiteCodim` is the card's theorem: for every real
subspace `U <= R[X]` of finite codimension and every `N`, there is `R in U` divisible by
`X^(N+1)` and a non-real `tau` with `tau^2` non-real such that `Xi_R` has the zero quartet.  This
is the stronger formal version the card asked for: the open-mapping step is not imported but
replaced by the algebraic shifted-Wronskian argument of `exists_nonreal_spanning`.
