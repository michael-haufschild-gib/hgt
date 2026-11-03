# The seven determinant-three Barnes cones

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/BarnesPrimeThreeHeckeRelation.lean`.
- **Statement:** The actual boundary Barnes periods satisfy the seven-cone prime-three identity, giving eigenvalue `1+3·3^(−w)` in the absolute chamber.

For `P_w(a,b)=ζ₂(a|a,b;w)+ζ₂(b|a,b;w)`, positive `a,b`, `Re w>2`,

`P(3a,b)+P(a,3b)+P(a+b,3b)+P(a+2b,3b)`
`+P(3a,a+b)+P(3a,2a+b)+P(2a+b,a+2b)`
`=P(a,b)+3P(3a,3b)`.

The seven cones subdivide the four index-three sublattices. Nonzero residues belong to one such sublattice; vectors divisible by three belong to all four. Axis points have weight one and interior points weight two, including shared rays between adjacent cones.

For the formal proof, put `K(X,Y)=(X+Y)/((1−X)(1−Y))`. The two nontrivial fans reduce to

`K(XY,Y³)+K(X³,XY)=(X³+Y³+2XY+2X²Y²)/((1−X³)(1−Y³))`,

`K(XY²,Y³)+K(X³,X²Y)+K(X²Y,XY²)`
`=(X³+Y³+2X²Y+2XY²)/((1−X³)(1−Y³))`.

Adding the two remaining cones gives the seven-cone kernel identity. Substitute `X=exp(−at)`, `Y=exp(−bt)` and integrate against `t^(w−1)`; all terms are absolutely integrable. Cancel the nonzero Gamma factor. Homogeneity then gives the seven-branch period identity with eigenvalue `1+3·3^(−w)`.

## Lean audit

- `barnesBoundaryPeriod_hecke_three_cones`
- `barnesBoundaryPeriod_hecke_three`

Final individual `lake --old env lean` check passed without warnings. Both endpoint audits use only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.

[Continuation to the actual completed Lewis period](f2-global-prime-three-lewis-hecke.md) is also audited [K].
