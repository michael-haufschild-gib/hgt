# Order-two shadow-matching normal form

- **ID:** `order-two-shadow-matching-normal-form`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; nonlinear cascade observability
- **Statement:** Loss of the third output-jet rank in a first-order/order-two composition is equivalent to an explicit static matching PDE; for separable outer branches the PDE has a complete first-order reduction.

## Algebraic state

Work over a characteristic-zero differential base containing `C(z)`. Let `x,v,y` be algebraically independent state coordinates, adjoin algebraic branches

`A=A(x,y)!=0`,

`R=R(z,x,v)`,

and define

`D x=v`,

`D v=R`,

`D y=A v`.

This is the state system for an order-two inner function `x=g`, `v=g'` and a first-order outer function `y=f(g)`.

Put

`u=A_x/A`

and

`Omega=u^2-u_x-A u_y`.

## Matching PDE

`[BRIDGE] [PROVED HERE]` The three-jet observation determinant

`J=det partial(y,Dy,D^2y)/partial(x,v,y)`

vanishes if and only if

`R_x-u(vR_v-R)=v^2 Omega.`

Indeed, with

`C=A_x+A_y A`,

one has

`D^2y=Cv^2+A R`.

Expansion along the first output row gives

`J=v^2(2A_xC-A C_x)+A A_x(vR_v-R)-A^2R_x.`

The identity

`(2A_xC-A C_x)/A^2=u^2-u_x-Au_y`

then yields the displayed PDE after division by `A^2`.

Thus the entire order-compression question is encoded by a constraint on the static algebraic branches `A` and `R`; no trajectory or asymptotic flow is required.

## Complete separable normal form

Assume

`A(x,y)=alpha(x) beta(y)`

with nonzero algebraic branches `alpha,beta`. Then `u=alpha'/alpha` is independent of `y`, and the matching PDE has the general solution

`R(z,x,v)=-u(x)v^2+alpha(x)^(-1) F(z,alpha(x)v)`,

where `F` is an arbitrary algebraic branch in its two displayed arguments.

To verify this, put `w=alpha(x)v`. Direct differentiation gives

`R_x-u(vR_v-R)=v^2(u^2-u_x)`

for the displayed `R`. Conversely, the characteristic invariant of the homogeneous PDE is `w=alpha(x)v`, and integration along the `x`-characteristics gives exactly this form.

On an analytic composition, define a local algebraic primitive `Psi` by

`Psi'(y)=1/beta(y)`.

Then

`w=alpha(g)g'=(Psi(f(g)))'`

and the matched inner equation gives

`w'=F(z,w)`.

Therefore the apparently three-state composition collapses to a first-order state `w` plus its primitive `Psi(f(g))`. This is the exact nonlinear cascade-matching mechanism.

## Entire-function residue

For a global entire counterexample one must realize the normal form without lowering the inner function to first order. Equivalently, one needs:

1. a genuinely nonautonomous separable first-order entire outer `f`, with `f'=alpha(z)beta(f)`;
2. a first-order DA entire state `w`;
3. an entire order-two function `g` solving `alpha(g)g'=w`.

Writing `Phi'=alpha`, this is the global factorization constraint

`Phi(g)=integral w.`

Local solutions are automatic. Global entire solutions are the obstruction.

`[PROVED]` The direct zero-free primitive subcase cannot provide a counterexample. If `W'=w`, `w` is first-order entire DA, and `W` is zero-free entire, then `w` has finite order and so does its primitive `W`. Hadamard factorization gives `W=exp(P)` for a polynomial `P`; hence `W` itself is already first-order DA.

The first open subcase for `Phi=id` is therefore ramified. For general nonaffine `Phi`, even a zero-free `W` still requires a separate entire-factorization argument; no blanket exclusion is claimed here.

## Parent-theory verdict

The matching PDE is the algebraic form of the standard partial-matching criterion for cascade observability. Solving it in the separable case is a characteristic calculation. The global entire factorization residue is not resolved here. This card is therefore bridge infrastructure, not new scientific knowledge.

## Gates

- [x] Exact determinant identity.
- [x] Exact matching PDE.
- [x] Complete separable characteristic normal form.
- [x] Direct zero-free primitive boundary excluded.
- [x] Parent observability theory identified; bridge verdict.
- [ ] Classify the ramified entire factorization residue.
- [ ] Lean deferred: existing formal files cover differential polynomials and primitive affine actions, but not algebraic partial derivatives or observation Jacobians.

## Primary references

1. A. Isidori, A. J. Krener, C. Gori-Giorgi, and S. Monaco, *The Observability of Cascade Connected Nonlinear Systems*, IFAC Proceedings Volumes 14 (1981), 337--342.
2. Y. Wang and E. D. Sontag, *Orders of Input/Output Differential Equations and State-Space Dimensions*, SIAM J. Control Optim. 33 (1995), 1102--1126.
