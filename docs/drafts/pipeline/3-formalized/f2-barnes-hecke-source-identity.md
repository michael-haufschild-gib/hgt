# The Barnes-cone source of the Lewis Hecke eigenvalue

- **ID:** f2-barnes-hecke-source-identity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** F2 reflection assembly; `MayerScattering/BarnesHeckeRelation.lean`.
- **Statement:** The actual two-boundary Barnes period satisfies the four-branch Hecke eigen-equation in its absolute chamber.

## Statement

Let `P_w(a,b)=ζ₂(a,b,w,a)+ζ₂(a,b,w,b)`, with `a,b>0` and `Re w>2`. Then

`P_w(2a,b)+P_w(a,2b)+P_w(a+b,2b)+P_w(2a,a+b)`
`= P_w(a,b)+2P_w(2a,2b)`.

Homogeneity `P_w(ca,cb)=c^(−w)P_w(a,b)` gives

`P_w(2a,1)+2^(−w)P_w(a/2,1)+2^(−w)P_w((a+1)/2,1)`
`+ (a+1)^(−w)P_w(2a/(a+1),1)`
`= (1+2·2^(−w))P_w(a,1)`.

## Proof

The Barnes Mellin formula gives

`Γ(w)P_w(a,b)=∫₀^∞ t^(w−1)K(e^(−at),e^(−bt)) dt`,

where `K(X,Y)=(X+Y)/((1−X)(1−Y))`. Both boundary-cone integrands are integrable at zero and infinity for `Re w>2`.

Clearing nonzero denominators proves the exact rational identity

`K(X²,Y)+K(X,Y²)+K(XY,Y²)+K(X²,XY)`
`= K(X,Y)+2K(X²,Y²)`.

Mellin integration and cancellation of the nonzero Gamma factor prove the cone relation. Termwise homogeneity of the Barnes sum proves the scaling formula. Scaling the last three cones by `2`, `2`, and `a+1` respectively gives the four-branch identity.

The cones count axis points once and interior points twice. The four images cover the original quadrant once and its even-even sublattice twice more. Thus the eigenvalue comes from the source multiplicities, including its boundary rays.

## Scope and continuation

This result concerns the convergent source series. [Pole-cleared and spatial continuation](f2-global-lewis-hecke-eigenvalue.md) now gives the actual Eisenstein and resonant period eigen-equations. No Weil-form identity is assumed here.

## Lean audit

- `barnesBoundaryPeriod_hecke_cones`
- `barnesBoundaryPeriod_scale`
- `barnesBoundaryPeriod_hecke`

Final check: `lake --old env lean GaloisForLFunctions/RenormalizedIntersectionTheory/MayerScattering/BarnesHeckeRelation.lean`.
The cone and four-branch identities have only `propext`, `Classical.choice`, `Quot.sound` in their transitive axiom lists. Imported by `RenormalizedIntersectionTheory.lean`.
