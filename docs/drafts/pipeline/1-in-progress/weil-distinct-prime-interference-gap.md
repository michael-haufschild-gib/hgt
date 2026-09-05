# Distinct outer-prime interference gap

- **ID:** WEIL-DISTINCT-PRIME-GAP
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `CCMRestrictedWeilPrimeOuterShell`, exact aperture cutoff calculus, Hilbert contraction and finite geometric identities in the current corpus.

## Full proof chain
Literal prime–Gamma source → joint source estimate on constrained ground → exclude zero-ground forced equations → positive ground at every aperture → weighted pole exclusion → RH. This card targets the joint prime estimate; all-aperture positivity remains unproved.

## Conjecture loop
The first idea, that distinct shifts cannot simultaneously preserve one vector's norm, is too strong: the overlap projections are nested, so common norm preservation is possible. The revised target is a quantitative obstruction to aligned outputs and hence to attaining the sum of separate operator bounds.

For `a<h<k<2a`, let `A=S_h` and `B=S_k` be actual outer-shell symmetric translations. Their product moves the left endpoint piece by `k-h` toward the centre and the right piece oppositely. Repetition is cut off; conjecture `(AB)^N=0` whenever `2a<N(k-h)`.

A nilpotent contraction `C` with `C^N=0` satisfies `||x||≤N||x-Cx||` by telescoping. Therefore `Re< Cx,x >≤(1-1/(2N²))||x||²`. Apply this to `C=AB` and self-adjoint contractions `A,B` to obtain, for nonnegative weights `u,v`,

`||(uA+vB)x||² ≤ ((u+v)²-u v/N²)||x||²`.

The positive survivor would be a strict joint prime norm bound with an explicit logarithmic-separation gain, even though each individual norm bound is sharp under pole constraints.

## Verification plan
Search existing general contraction/support results; prove in scratch using `lake env lean`; build only finished named leaves; wire imports without umbrella builds; audit public axioms and formal lint. No numerical experiment or oracle is needed for this candidate.
