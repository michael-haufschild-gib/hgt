# MC: separate absolute payment of the triangular short head fails

- **ID:** MC-C12.93-short-head-absolute
- **Stage:** 5-failed
- **Type:** FALSIFIED CONSTRUCTION; unconditional Lean audit complete,2026-10-04,1005r.
- **Source:** `../3-formalized/mc-triangular-short-head-scale-law.md`.

## Failed proposal and exact obstruction

For the actual source `A(U)=sum_(m<=U)mu(m)W_square(U^2/m)`, estimate its absolute
value separately at every half-plus-epsilon exponent in x=U^2, then pay the two
short terms in the triangular reconstruction independently.

`RHTower.LiouvilleTriangularShortHead.not_mobiusShortHead_isLittleO` proves
`A(U)!=o(U*sqrt(U))`. Any separate absolute `O(x^(1/2+epsilon))` estimate with
0<epsilon<1/4 would imply this forbidden little-o bound. Thus the proposal fails
on the actual Mobius coefficients, not merely on a freely chosen test vector.

This does not refute a one-sided bound for A, does not assert both signs of
excursion, does not sign the combined expression, and does not retire MC or RH.

## Strongest positive survivor

`RHTower.LiouvilleTriangularShortHead.mobiusShortHead_asymptotic` proves

    A(U)-Z*U^2*H(U)=o(U*sqrt(U)),
    Z=sum_(n>=1)1/n^2, H(U)=sum_(m<=U)mu(m)/m.

The exact proof also retains `A=Z*U^2*H-2U*V+E`, `|E|<=U`, with
`V=sum_(m<=U)mu(m)/sqrt(m)=o(sqrt(U))`. The new source information identifies the
moving harmonic Mobius prefix responsible for the obstruction. It is not a
renaming of the negative statement.

## Proof and audit status

The survivor card contains the dependency-closed paper proof and corpus audit.
Leaf `LiouvilleTriangularShortHead.lean` formalizes the positive asymptotic, harmonic
prefix obstruction and actual short-head obstruction. Targeted old-build and the
required direct `lake --old env lean` audit passed. All four public theorem axiom
checks report only propext/Classical.choice/Quot.sound. Umbrella import is unique;
no umbrella build was run. Index regeneration passed. Global lint retains13
unrelated reachability errors, none for this leaf.

## Surviving hard problem

Prove the complete signed bound `P(x)>=-C_epsilon*x^(1/2+epsilon)` for every
positive epsilon, preserving the interaction between both short terms. Neither
this obstruction nor its positive survivor supplies that bound. RH remains open
in this route.
