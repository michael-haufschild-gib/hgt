# Additive Koszul cocycle skeleton

- **ID:** additive-koszul-cocycle-skeleton
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/multi-q-shafarevich-gluing-group.md` R0; Lean file `formal/GaloisForLFunctions/HTGeometry/KoszulCohomology.lean`
- **Statement:** For commuting additive difference actions, the first Koszul differential detects joint invariants, the second detects additive 1-cocycles, and every first coboundary is an additive 1-cocycle.

## Goal
This banks the exact additive notation used in the rank-one Shafarevich gluing computation: writing `tau_p = sigma_p - 1`, the cocycle condition is `tau_p a_q = tau_q a_p`, and coboundaries have the form `(tau_p g)_p`. It does not formalize group cohomology, the quotient defining `H^1`, nonabelian Shafarevich kernels, exterior powers, cup products, infinite prime-lattice limits, or the `H^2` curvature obstruction.

## Paper Proof
Let `M` be an additive commutative group and let `act_p : M -> M` be pairwise commuting additive endomorphisms. Define
`d0(x)_p = act_p(x) - x`. Then `d0(x)=0` iff `act_p(x)-x=0` for every `p`, which is equivalent to `act_p(x)=x` for every `p`. Thus the kernel of `d0` is the joint invariant subgroup.

For a 1-cochain `c`, define
`d1(c)_{p,q} = (act_p(c_q)-c_q) - (act_q(c_p)-c_p)`. By definition, `d1(c)=0` iff
`act_p(c_q)-c_q = act_q(c_p)-c_p` for every `p,q`, which is exactly the additive 1-cocycle condition.

Finally, if `c=d0(h)`, then
```
act_p(c_q)-c_q
  = act_p(act_q(h)-h) - (act_q(h)-h)
  = act_p(act_q(h)) - act_p(h) - act_q(h) + h,
```
and the analogous expression with `p` and `q` exchanged is
`act_q(act_p(h)) - act_q(h) - act_p(h) + h`. These are equal because the actions commute and `M` is additive abelian. Therefore `d1(d0(h))=0`, so every additive coboundary is an additive 1-cocycle.

## Gates
- [x] 0 -> 1  in-progress: exact additive `tau_p = sigma_p - 1` skeleton extracted from the Shafarevich gluing R0 computation.
- [x] 1 -> 2  fully-proven: paper proof above, using only additive cancellation and pairwise commuting actions.
- [x] 2 -> 3  formalized: Lean theorems `koszulD0_eq_zero_iff_invariant`, `koszulD1_eq_zero_iff_additiveCocycle`, `koszulCoboundary_cocycle`, and `koszulD1_koszulD0_eq_zero`; names checked by scratch file; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: cite as the formal certificate for the additive first-Koszul cohomology skeleton.

## Log
- 2026-06-19 — Leaner split this exact additive Koszul cocycle/coboundary skeleton from `multi-q-shafarevich-gluing-group` R0. The parent card remains in `2-fully-proven` because the two-prime Shafarevich quotient, nonabelian `H^1`, character-variety/Procesi input, and C5-star regularity are not fully Lean-formalized.
