# Unbounded one-coordinate monodromy obstructs algebraic dependence

- **ID:** unbounded-one-coordinate-monodromy-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / BRIDGE method lemma
- **Source:** abstracted from the Nguyen Q6.2 inverse-Böttcher route

## Statement

Let `K subset C` be a coefficient field. Let `F(z)` and `G(z)` be analytically
continuable germs over a common base domain, with `G` transcendental over `K(z)`.

Assume that for every `N` there is a continuation loop, based on a small simply
connected test neighborhood `V`, such that after continuation

`F -> xi_N F`, `G -> G`,

as analytic functions on `V`, where `xi_N` is a root of unity of order `> N`, and
`F` is not identically zero on `V`.

Then `F` and `G` are algebraically independent over `K(z)`.

The symmetric variant also holds: if arbitrarily high-order scalar monodromy moves
`G` while fixing `F`, and `F` is transcendental over `K(z)`, then `{F,G}` is
algebraically independent over `K(z)`.

## Proof

Suppose a nonzero relation exists:

`P(z,F(z),G(z))=0`, with `P in K[z,Y,W]`.

After clearing denominators, choose such a `P` with minimal positive degree in `Y`.
If `deg_Y P=0`, then `G` is algebraic over `K(z)`, contradicting the hypothesis.

Let `d=deg_Y P>0`. Choose a monodromy loop whose multiplier `xi` has order
`m>d`. Analytic continuation of the relation along the loop and its iterates gives,
on the same test neighborhood `V`,

`P(z,xi^k F(z),G(z))=0`, for `k=0,...,m-1`.

Since `F` is not identically zero on `V`, after shrinking away from its isolated
zeros the `m` functions `xi^k F(z)` are pairwise distinct. Thus, for each `z` in a
nonempty open subset of `V`, the degree-`d` polynomial

`Y -> P(z,Y,G(z))`

has more than `d` roots. Hence it is identically zero in `Y` on that open subset.
Writing

`P(z,Y,W)=sum_j p_j(z,W)Y^j`,

we get

`p_j(z,G(z))=0`

for every `j`. Since `G` is transcendental over `K(z)`, each `p_j` is the zero
polynomial. Therefore `P=0`, contradiction.

The symmetric variant is identical with `F` and `G` interchanged. ∎

## Role in Q6.2

For disconnected quadratic Böttcher coordinates, the component-loop period lemma
supplies loops with arbitrarily high dyadic scalar monodromy. In the both-disconnected
case, a loop around a depth-`n` cylinder of `K_c1` can be placed in a disk disjoint
from `K_c2`, so it moves `phi_c1` and fixes `phi_c2`. In the mixed case, the loop
moves the disconnected coordinate while the connected coordinate is single-valued
on its basin.

This theorem is exactly the algebraic-dependence obstruction used there. The complex
dynamics supplies the loops; this lemma supplies the finite-degree contradiction.

## Significance

This is not a deep source-new theorem by itself. It is a reusable constraint-side
gatekeeper: finite algebraic dependence is incompatible with unbounded scalar
monodromy in one coordinate while the other coordinate remains fixed.

In the project vocabulary, it isolates a basic form of "constraint, not flow":
the obstruction is not a generative differential equation but an infinite
continuation action that no finite algebraic relation can absorb.

## Lean formalization

Module: `formal/GaloisForLFunctions/HTGeometry/ScalarMonodromyAlgebraicIndependence.lean`
(namespace `GaloisForLFunctions.HTGeometry`).

Continuation along a loop is an `L`-algebra automorphism of the germ algebra, where `L = K(z)` is
the coefficient field it fixes pointwise; the germ algebra is an integral domain. The Lean layer
quantifies over exactly that data, so the analytic input is the card's own hypothesis and nothing
else.

| Paper statement | Lean declaration |
|---|---|
| iterating the loop multiplies by `xi^k` | `algEquiv_pow_apply_of_scalar` |
| iterating the loop fixes the untouched coordinate | `algEquiv_pow_apply_of_fixed` |
| unbounded scalar monodromy forces transcendence over the fixed subalgebra | `transcendental_of_unbounded_scalar_monodromy` |
| `{F,G}` algebraically independent over `K(z)` | `algebraicIndependent_pair_of_unbounded_scalar_monodromy` |

The proof is the card's degree argument in its sharp form: a relation of degree `d` in the moved
coordinate is inherited by the `m > d` pairwise distinct translates `xi^k F`, and a polynomial of
degree `d` over a domain vanishing at `m > d` distinct points is zero; injectivity of the
coefficient inclusion then kills every coefficient. The symmetric variant of the card is the same
theorem with the roles of the two germs exchanged.

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
