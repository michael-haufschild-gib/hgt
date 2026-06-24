# N1 Signed Bulk Exterior Monotonicity Fails

- **ID:** n1-signed-bulk-exterior-monotonicity-fails
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `stieltjes-bulk-exterior-christoffel-monotonicity.md`;
  `boundary-weyl-thresholds-have-no-formal-monotonicity.md`;
  `finite-rank-one-selector-no-free-lunch.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** A one-negative-square signed moment bulk does not inherit the
  exterior Christoffel monotonicity of a positive Stieltjes bulk. Even with
  support to the right of both exterior boundary points, the rank-one repair
  threshold can be larger at the farther boundary point.

## Setup

Let `V=R[y]_{<=2}` and write

`v_x=(1,x,x^2)^T`.

Consider the signed atomic moment form

`A[p] = -(1/36) p(0)^2 + (1/14) p(1)^2 + 15 p(2)^2`.

The support `{0,1,2}` lies to the right of both boundary points

`x_1=-4`, `x_2=-4/25`.

Let `H` be the `3 x 3` Gram matrix of `A` in the monomial basis. Since the
Vandermonde matrix at `0,1,2` is invertible, `H` is congruent to the diagonal
matrix

`diag(-1/36, 1/14, 15)`.

Thus `H` has inertia `(2,1)`.

For an exterior point `x`, define

`m(x)=v_x^T H^{-1} v_x`.

When `m(x)<0`, the positive rank-one repair

`H + t v_x v_x^T`

crosses to positive definite precisely when

`t > tau(x) := -1/m(x)`.

## Theorem

For the signed moment form above,

`m(-4) = -88/3`,

while

`m(-4/25) = -321266936/5859375`.

Hence

`tau(-4) = 3/88`

and

`tau(-4/25) = 5859375/321266936`.

In particular,

`tau(-4) > tau(-4/25)`.

Thus the repair threshold is larger at the farther-left boundary point `-4`
than at the nearer boundary point `-4/25`, despite the signed moment support
being to the right of both points.

## Proof

For the support points `0,1,2`, the degree-two Lagrange basis values are

`l_0(x)=((x-1)(x-2))/2`,

`l_1(x)=-x(x-2)`,

and

`l_2(x)=x(x-1)/2`.

Since `H=V W V^T` with

`W=diag(-1/36, 1/14, 15)`,

the inverse-energy identity gives

`m(x)=l_0(x)^2/(-1/36) + l_1(x)^2/(1/14) + l_2(x)^2/15`.

At `x=-4`,

`(l_0,l_1,l_2)=(15,-24,10)`,

so

`m(-4) = -36*15^2 + 14*24^2 + 10^2/15`

`= -8100 + 8064 + 20/3`

`= -88/3`.

At `x=-4/25`,

`(l_0,l_1,l_2)=(783/625,-216/625,58/625)`.

Therefore

`m(-4/25)
 = -36*(783/625)^2
   + 14*(216/625)^2
   + (58/625)^2/15`

`= -321266936/5859375`.

Both values are negative, so the rank-one repair thresholds are

`tau(-4)=3/88`

and

`tau(-4/25)=5859375/321266936`.

The inequality

`3/88 > 5859375/321266936`

follows from

`3*321266936 > 88*5859375`.

This proves the threshold-order reversal.

## Consequence For The RH Route

`stieltjes-bulk-exterior-christoffel-monotonicity.md` gives a valid monotonicity
lemma for positive moment bulks. The present theorem shows that replacing
"positive Stieltjes bulk" by "signed `N_1` bulk" breaks that lemma.

This matters because the unrepaired Krein object in the rank-one Gamma-boundary
route is precisely a one-negative-square object. Knowing that the source-built
bulk has inertia `(d,1)` does not by itself allow pole-to-first-trivial-zero
threshold transport.

A proof may still establish a monotone law for the actual completed
Euler/Gamma/FE carrier, but it must use more than the `N_1` signature. It must
prove a source-specific structural fact: for example a positive hidden bulk
decomposition, a total-positivity theorem, a variation-diminishing weld map, or
the full semilocal Schur/index theorem.

## Theatre Test

For any proof that applies exterior Christoffel monotonicity to an unrepaired
Krein bulk:

1. Is the bulk positive, or only one-negative-square?
2. If it is only `N_1`, what source theorem replaces the positive orthogonal
   polynomial zero-placement argument?
3. Does the proposed monotonicity survive the explicit signed atomic
   countermodel above?
4. If not, the proof has imported the missing positivity theorem.

## Source Boundary

This theorem is a finite signed-moment counterexample. It proves no statement
about the actual zeta carrier and no zero localization. Its role is to prevent
the `N_1` scaffold from being treated as if it were already a positive
Stieltjes bulk.

## Gates

- [x] 0 -> 1 in-progress: signed-bulk monotonicity question isolated.
- [x] 1 -> 2 fully-proven: exact signed atomic counterexample written.
- [ ] 2 -> 3 formalized: optional rational matrix/inertia calculation.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation. A small local
  search found the support `{0,1,2}` and rational weights; the proof above is
  exact and independent of the search.

## 2026-06-24 positive-bulk mass adequacy is separate

`positive-stieltjes-pole-plus-first-atom-insufficient.md` gives a complementary positive-bulk countermodel. Even before passing to a signed `N_1` bulk, the formal data of a positive Stieltjes bulk, pole mass `4`, and first-trivial-zero mass `4/25` do not force repair.

Together the two cards isolate two missing source facts: a positivity or kernel-exhaustion theorem for the bulk, and a mass/domination theorem for the actual completed carrier.
