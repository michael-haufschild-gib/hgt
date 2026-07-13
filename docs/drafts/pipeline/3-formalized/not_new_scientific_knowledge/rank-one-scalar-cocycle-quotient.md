# Rank-one scalar cocycle quotient

- **ID:** rank-one-scalar-cocycle-quotient
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/multi-q-shafarevich-gluing-group.md` R0; Lean file `formal/GaloisForLFunctions/HTGeometry/RankOneCohomology.lean`
- **Statement:** For commuting scalar difference actions on a commutative coefficient group, rank-one scalar cocycles form an abelian group, scalar coboundaries form a subgroup, and the quotient rank-one Picard skeleton is an abelian group.

## Goal
This banks the exact group-algebra skeleton behind the rank-one cocycle/coboundary calculation in the multi-q Shafarevich gluing card. It does not formalize Picard-Vessiot rings, the category of difference modules, nonabelian `H^1`, the Shafarevich kernel, character varieties, or the C5-star regularity layer.

## Paper Proof
Let `G` be a commutative group and let `act_p : G -> G` be pairwise commuting group endomorphisms. A scalar rank-one cocycle is a family `a_p` satisfying
`a_p * act_p(a_q) = a_q * act_q(a_p)` for all `p,q`.

The constant family `1` is a cocycle. If `a` and `b` are cocycles, then
```
(a_p b_p) * act_p(a_q b_q)
  = (a_p act_p(a_q)) * (b_p act_p(b_q))
  = (a_q act_q(a_p)) * (b_q act_q(b_p))
  = (a_q b_q) * act_q(a_p b_p),
```
using that each action is a homomorphism and `G` is commutative. Thus cocycles are closed under pointwise multiplication. Inverting the cocycle identity gives
`a_p^-1 * act_p(a_q)^-1 = a_q^-1 * act_q(a_p)^-1`, so cocycles are closed under pointwise inverse. Therefore the scalar cocycles form an abelian subgroup of the pointwise group `p -> G`.

For any `h : G`, define the scalar coboundary `delta(h)_p = act_p(h) * h^-1`. Pairwise commutation of the actions gives
```
delta(h)_p * act_p(delta(h)_q)
  = act_p(h) * h^-1 * act_p(act_q(h) * h^-1)
  = act_p(act_q(h)) * h^-1
  = act_q(act_p(h)) * h^-1
  = delta(h)_q * act_q(delta(h)_p),
```
after cancelling and commuting factors. Hence every coboundary is a cocycle. Also
`delta(hk)=delta(h)delta(k)`, `delta(1)=1`, and `delta(h^-1)=delta(h)^-1`, so the coboundaries form a subgroup of the cocycle group. The quotient of an abelian group by a subgroup is again an abelian group, giving the rank-one Picard quotient skeleton.

## Gates
- [x] 0 -> 1  in-progress: exact R0 rank-one scalar cocycle/coboundary skeleton extracted from the Shafarevich gluing card.
- [x] 1 -> 2  fully-proven: paper proof above, using only commutative group algebra and pairwise commuting actions.
- [x] 2 -> 3  formalized: Lean theorems `scalarCocycle_mul`, `scalarCocycle_inv`, `rankOneCoboundary_cocycle`, `rankOneCoboundaryCocycle_mul`, `rankOneCoboundaryCocycle_inv`, and `rankOnePicard_commGroup`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the rank-one scalar cohomology skeleton.

## Log
- 2026-06-19 — Leaner split this exact rank-one scalar cocycle quotient skeleton from `multi-q-shafarevich-gluing-group` R0. The parent card remains in `2-fully-proven` because nonabelian `H^1`, the full Shafarevich kernel, character-variety/Procesi input, and C5-star regularity are not fully Lean-formalized.
