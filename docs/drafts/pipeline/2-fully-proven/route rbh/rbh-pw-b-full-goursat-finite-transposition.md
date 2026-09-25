# RBH / PW-B full Goursat finite weak transposition

- **ID:** RBH-PW-B-FGWT
- **Stage:** 2-fully-proven
- **Role:** literal finite predecessor of the PW-B CTP seam

Fix a source branch `b`, base radial coordinate `y`, and angular target
`(X, exp k)`. On a null rectangle define

`K(u,v) = fullAngularRiemannKernel b ((u+v)/2) (y+(u-v)/2) y`,

and define `N` by replacing the full kernel with the native Riemann kernel.
For `u,v ≥ 0`, the literal full Goursat identity gives

`K(u,v) = H + ∫₀ᵘ∫₀ᵛ G(a,b) db da`,

where `H = fullAngularField b (X, exp k)` and

`G(a,b) = parameter(b) (K(a,b) + N(a,b)) / (4 cosh²(y+(a-b)/2))`.

If `φ, ψ` are `C¹` on `[0,U]`, `[0,V]` and vanish at their upper endpoints,
two integrations by parts give the exact weak form

`∫_0^U ∫_0^V K(u,v) φ'(u) ψ'(v) dv du`

`= H φ(0) ψ(0) + ∫_0^U ∫_0^V G(u,v) φ(u) ψ(v) dv du`.

## Proof

Insert the displayed Goursat identity into the left side. The constant term
factors. For the double primitive, integrate first in `v`:

`∫_0^V (∫_0^u ∫_0^v G(a,b) db da) ψ'(v) dv`

`= -∫_0^u ∫_0^V G(a,v) ψ(v) dv da`,

because `ψ(V)=0`. Integrating the remaining primitive against `φ'` gives a
second minus sign and the displayed bulk integral because `φ(U)=0`. Continuity
of the literal Goursat integrand on the compact rectangle legitimizes both
Fubini swaps and integrations by parts.

## Whole-route consequence

This is the branch-dependent full kernel, not the native half-square kernel:
its bulk term retains `K + N` and its boundary term is the literal full angular
field. Applying the identity separately to the direct and image cones is the
finite ordered source-to-boundary reduction required before the noncompact CTP
limit. The remaining hard theorem is to take that limit against both physical
source legs, retain the full-minus-native lift defect, and identify the result
with the contact-completed complementary current.

## Lean status

The prerequisite source `ThetaCuspHawkingBMFullAngularCircleGreen.lean` now
directly audits after its reflection-chain repair. Formalization of this
transposition is blocked only by its missing `.olean`; Lake's nominally
targeted build expands into a prohibited global replay, so no umbrella build
was run.
