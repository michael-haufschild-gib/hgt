# Original forcing and onset-pulse causal Green reconstruction

Status: formalized; foreground scratch check, exact-module build and three new public theorem axiom audits passed. RH remains unproved.

Lean module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOnsetGreenReconstruction`.
Namespace: `RHTower.D4BMOnsetGreenReconstruction`.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact result

Let `F=timeOriginalForcing`, `P=fullSourceOnsetPulse`, `U_Q=timeLiftField`, `U_H=timeAngularSeedField`, and `alpha=parameter q branch`. The new finite circular action satisfies

`R_F = U_Q - U_H/alpha + R_P/alpha`.

The source, angular fields, physical rate, smooth onset and pulse are the existing corpus definitions. The public theorems quantify over the original zero occurrence, either physical branch, arbitrary complex amplitude and angular base point. Nonnegative null time and radial width are encoded by `NNReal`; no inverse, PDE, boundary, spectral or extinction premise is supplied.

The result identifies the actual source convolution with its explicit wave image plus its original pulse response. Physical radial/left-QNM operator-domain admission and the complete signed current remain open. This theorem is not an RH proof.

## Circular action and original domains

For `p,w>=0`, set `r=p+w`, `T=(2p+w)/2`, `x=-w/2`, and angular base point `z0=(X,exp k)`. Source coordinates are `tau=(a+b)/2`, `y=(a-b)/2`. The direct source triangle is

`0<=a<=p, a<=b<=r`;

the image triangle is

`0<=a<=p, a<=b<=p`.

`retardedNullAction S` is one quarter of the direct integral of the actual source-circle mean, minus one quarter of the image integral. Its radii use the existing two-point invariant at `(T-tau,x,y)` and `(T-tau,x,-y)`. The normalization combines the original kernel factor one half and source null-coordinate Jacobian one half.

For continuity proofs the radius is written `arcosh(max(1,Z))`. The source-triangle inequalities prove the original causal inequality and hence `Z>=1`; the max is removed in both kernel identifications. Thus the continuous extension does not change the source-circle values on either integration domain.

## The diagonal cancellation

For either actual radial coefficient `c`, put

`beta(a,b)=c((a-b)/2) timeOnset(2s,a)`.

The seed and lift satisfy `c(0)=0`, giving `beta(a,a)=0`. The prescribed onset gives `beta_b(0,b)=0`. Joint continuity and all first and mixed derivatives used below are proved from the actual source-field derivatives.

For the reciprocal source kernel `K`, integrate

`K beta_ab-beta K_ab = partial_a(K beta_b)-partial_b(beta K_a)`.

Finite triangle Fubini and two fundamental-theorem identities give, on the direct triangle,

`datum beta(p,r) + integral_0^p K(a,a) beta_b(a,a) da`.

The image triangle contributes exactly the same diagonal integral. The equality of these terms follows from exchanging the two directions of the closed-cone Goursat double primitive. Subtracting the two original triangles recovers `datum beta(p,r)`.

The AdS term is retained through both integrations and then canceled. This handles the actual seed and pulse even though the odd extension of the pulse need not be continuous across AdS.

## Actual angular and wave identifications

The full angular kernel has mixed source derivative `alpha(M_H+M_Q)/(4 cosh(y)^2)`; the native half-square kernel has mixed source derivative `M_(Delta Q)/(4 cosh(y)^2)`. These are the existing full and native Goursat theorems, used with the exact reciprocity of the two-point invariant. The exchange of source and target also exchanges the two null integration directions.

The literal differential wave of each actual field, averaged on the source circle, is

`4 beta_ab M - beta M_Delta/cosh(y)^2`.

The time-onset second derivatives cancel between the actual time and radial derivatives. The metric identity `1-radialUnit(y)^2=1/cosh(y)^2` fixes the angular coefficient. The Green identity therefore proves separately

`R_(wave U_H)=U_H`, `R_(wave U_Q)=U_Q`.

The existing pointwise source identity is `F=wave U_Q-wave U_H/alpha+P/alpha`. Actual field and Laplacian continuity justify angular averaging; continuity of the resulting circle-wave and pulse functions justifies both finite triangular integral linearity steps. This gives the displayed original-forcing reconstruction. Nonvanishing of `alpha` is derived from the existing nonreal physical-parameter theorem.

## Public API

| Declaration | Result |
|---|---|
| `retardedNullAction` | Finite original direct/image circular-source integral |
| `retardedNullAction_seed_wave` | Actual full angular seed reconstruction |
| `retardedNullAction_lift_wave` | Actual half-square lift reconstruction |
| `originalForcing_retarded_reconstruction` | Original forcing equals wave image plus original pulse response |

## Remaining target

Prove that this concrete causal response belongs to the required physical radial/left-QNM operator domain. Apply the complete action current to the response, with the seed/lift wave image, pulse response, both cross terms and all physical faces retained. Establish the fixed Hawking-clock extinction statement from those actual objects. The present result supplies the finite source convolution for this task; it does not assume or prove extinction.

Search and analytical evidence are recorded in the [onset-pulse card](../1-in-progress/hb-onset-pulse-green-action.md). Broad and mechanism searches reported partial coverage and local runtime failures; no proposed group was accepted as a theorem. No numerical experiment was used.

## Validation

Foreground `lake env lean` scratch checks passed. Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOnsetGreenReconstruction` completed successfully with two jobs, processing only this new leaf. The isolated audit reused 3,995 cached project modules and installed dependency caches; no dependency, full-project or umbrella build ran.

All three new public theorem axiom reports contain exactly `propext`, `Classical.choice` and `Quot.sound`. Existing theorem axiom audits were not repeated. The installed source and all five build artifacts match the audited files byte for byte. The new module is wired once into `RHTower.lean`.

Source SHA-256: `856cfe7052fd39cdda816994a75492277d33b3c22957e284caf4ad59e3926554`.

The corpus index was refreshed once and reported zero changed and zero removed source records; all four new public API entries were verified in `LEAN_API.md`. Repository-wide `scripts/formal_tools.py lint` reported an unrelated unreachable module, `GaloisForLFunctions.RHTower.ChronologicalTailUnitNormal`, plus existing large-file warnings. The new module is reachable. The global lint failure does not change its successful exact-module build or new-theorem axiom audit.

All owned Lean/Lake and search processes terminated. The isolated audit cache, scratch sources, search-result files and temporary index/lint captures were removed. No numerical experiments, Git commands, launcher commands, full builds or umbrella builds ran. The frontier map and universal `STATUS.md` were not edited.

