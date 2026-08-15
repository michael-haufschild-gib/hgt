# Stieltjes Bulk Exterior Christoffel Monotonicity

- **ID:** stieltjes-bulk-exterior-christoffel-monotonicity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / conditional source-route lemma
- **Source:** `boundary-weyl-thresholds-have-no-formal-monotonicity.md`;
  `pole-budget-does-not-imply-uvarov-repair.md`;
  `source-selector-repair-obligation-ledger.md`;
  entropy move `monotone`
- **Statement:** For a positive moment bulk supported to the right of an exterior
  boundary interval, the Christoffel/Weyl dual energy is monotone: exterior
  evaluation becomes cheaper as the boundary point moves toward the support.
  Thus pole-to-first-trivial-zero threshold monotonicity is valid only after a
  positive Stieltjes bulk has already been source-built.

## Setup

Let `mu` be a positive Borel measure on `R` with finite moments through degree
`2d`, and suppose `supp(mu) subset [a,infinity)`. Assume the polynomials of
degree at most `d` have positive definite Gram form

`<p,q> = int p(t) q(t) dmu(t)`.

Let `K_d(x,x)` be the Christoffel-Darboux kernel diagonal for this degree-`d`
polynomial space:

`K_d(x,x)=sum_{n=0}^d P_n(x)^2`,

where `P_0,...,P_d` are any real orthonormal polynomials for `mu`.

Equivalently, for the moment Gram matrix `H_d` and vector

`v_x=(1,x,...,x^d)^T`,

`K_d(x,x)=v_x^T H_d^{-1} v_x`.

The rank-one subtraction

`H_d - t v_x v_x^T`

is positive semidefinite exactly when

`t <= lambda_d(x) := 1/K_d(x,x)`.

## Theorem

For `x<a`, the function `K_d(x,x)` is nonincreasing in `x`. If `d>=1` and the
degree-`d` orthogonal polynomial is nonconstant, then `K_d(x,x)` is strictly
decreasing on `(-infinity,a)`.

Consequently the Schur threshold

`lambda_d(x)=1/K_d(x,x)`

is nondecreasing on `(-infinity,a)`, and is strictly increasing in the
nondegenerate case.

## Proof

Use the orthonormal-polynomial representation

`K_d(x,x)=sum_{n=0}^d P_n(x)^2`.

For each `n>=1`, the zeros of `P_n` lie in the convex hull of `supp(mu)`, hence
in `[a,infinity)`. Write

`P_n(x)=c_n prod_{j=1}^n (x-r_{n,j})`

with `r_{n,j}>=a` and `c_n != 0`. For `x<a`,

`P_n'(x)/P_n(x)=sum_{j=1}^n 1/(x-r_{n,j}) < 0`.

Therefore

`P_n(x)P_n'(x)=P_n(x)^2 sum_{j=1}^n 1/(x-r_{n,j}) < 0`.

The constant polynomial `P_0` contributes derivative `0`. Hence

`d/dx K_d(x,x)
 = 2 sum_{n=0}^d P_n(x)P_n'(x)
 = 2 sum_{n=1}^d P_n(x)P_n'(x) <= 0`,

with strict inequality when `d>=1`.

The threshold statement follows because `lambda_d(x)=1/K_d(x,x)` and
`K_d(x,x)>0`.

## Boundary-Channel Corollary

Let `x_1 < x_2 < a`. Then

`K_d(x_1,x_1) >= K_d(x_2,x_2)`

and

`lambda_d(x_1) <= lambda_d(x_2)`.

Thus, in a positive Stieltjes bulk with support to the right of both boundary
points, a tolerated rank-one subtraction at the farther-left point gives a
larger or equal threshold at the nearer point.

Applied only at the level of formal boundary locations, this would compare the
pole channel `y=-4` and the first-trivial-zero channel `y_*=-4/25` whenever the
same positive bulk has support to the right of `-4/25`.

## Consequence For The RH Route

This card refines, rather than contradicts,
`boundary-weyl-thresholds-have-no-formal-monotonicity.md`.

There is no monotonicity for arbitrary positive definite bulk forms. There is a
monotonicity theorem for Stieltjes moment bulks with support on one side of the
boundary points.

Therefore a pole-to-first-trivial-zero monotone proof has exactly two burdens:

1. source-build the relevant positive moment bulk, with support to the right of
   both exterior channels;
2. prove the pole-channel threshold with the correct mass normalization.

After those two inputs, the Christoffel comparison is legitimate. Without the
first input, the monotone argument is only boundary vocabulary. In the RH route,
source-building the positive bulk is already the large Schur/Hankel content: if
the bulk is the reciprocal nontrivial-zero Stieltjes form, that positivity is
RH-strength; if the bulk is a semilocal Euler/Gamma carrier, its positivity is
exactly the missing A6/A7 repair theorem.

## Theatre Test

For any proof using exterior Christoffel monotonicity:

1. What is the positive measure `mu`?
2. Is its support on one side of the boundary interval being compared?
3. Is positivity of the Gram form proved from source data, or imported from an
   RH-equivalent Stieltjes cone?
4. Are the rank-one masses compared under the same subtraction convention?

If the positive bulk is not source-built before this comparison, the monotonicity
lemma has not crossed the repair gate.

## Source Boundary

This theorem is a conditional orthogonal-polynomial lemma. It proves no
positivity for zeta and no zero localization. Its use is to separate a valid
Christoffel monotonicity input from the missing source-built positivity theorem.

## Gates

- [x] 0 -> 1 in-progress: moment-bulk monotonicity route isolated.
- [x] 1 -> 2 fully-proven: exterior Christoffel monotonicity proved from
  orthogonal-polynomial zero placement.
- [ ] 2 -> 3 formalized: optional theorem on real-rooted orthogonal
  polynomials and kernel monotonicity.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after entropy
  again selected `monotone`. The card keeps the valid Stieltjes-bulk
  monotonicity while preventing it from being used before the source-built bulk
  positivity is proved.

## 2026-06-24 N1 signed bulks do not inherit the monotonicity

`../../3-formalized/not_new_scientific_knowledge/n1-signed-bulk-exterior-monotonicity-fails.md` gives the exact boundary case. A signed moment form with inertia `(2,1)` and support `{0,1,2}` to the right of both `-4` and `-4/25` reverses the repair-threshold order: the farther-left boundary point has the larger threshold.

Thus this card's positivity hypothesis is load-bearing. Exterior Christoffel monotonicity can be used only after a positive Stieltjes bulk has been source-built, not merely after an unrepaired `N_1` Krein scaffold has been identified.

## 2026-06-24 positive-bulk monotonicity does not pay the fixed masses

`../../3-formalized/not_new_scientific_knowledge/positive-stieltjes-pole-plus-first-atom-insufficient.md` separates monotone threshold order from mass adequacy. A positive Stieltjes bulk can have the correct exterior order, yet the zeta pole mass `4` and first-trivial-zero mass `4/25` need not produce a positive repaired form.

Therefore this monotonicity lemma is not a repair theorem. It can compare thresholds once a source-built positive bulk and the correct mass inequality are known; it does not prove that the first-trivial-zero atom pays the pole deficit.
