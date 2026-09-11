# HB: full direct/image spin-two delay transfer

Stage: 3-formalized for the full finite direct/image source-delay transfer. Complete physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Direct hard target

The [original finite diagonal transfer](hb-spin-two-delay-characteristic.md) resolves the degenerate direct characteristic. The proved extension uses the same actual clock and native spin-two kernel at unequal radii and on the image branch, with their original causal lower limits. This is required before integrating the reduced source current over its full radial domain and comparing it with the physical currents.

## Conjecture and proof mechanism

For original tortoise radii `x,y<=0`, reflect the source as `y_e=y` on the direct branch and `y_e=-y` on the image branch. The invariant is literally

```
Z_e(h)=invariant(h-x+y,x,y_e),
A_e=partial_h Z_e, B_e=partial_h A_e,
a_direct=2 max(x-y,0), a_image=-2y.
```

At the original lower endpoint, `a_e-x+y=|x-y_e|`, so `Z_e(a_e)=1`. For `h>a_e`, `A_e(h)>0` and `Z_e(h)>1`. If `x!=y_e`, the derivative is already positive at the endpoint. The native primitive and its first jet then give zero lower boundary and zero bulk contact by ordinary continuity. If `x=y_e`, the physical radial signs force the already proved coincident direct geometry; for the image this occurs only at `x=y=0`.

Keep the exact finite clock `W(h)=clockDensity(q,branch,radialUnit x,radialUnit y,V,h)`. Its original smoothness and terminal jets are already derived. With `F''=-spinTwo`, define

```
C_e=-W F'/A_e+(W'/A_e^2-W B_e/A_e^3)F,
bulk_e=F[W''/A_e^2-3B_e W'/A_e^3+(3B_e^2-A_e^2)W/A_e^4].
```

The actual chain rule gives `partial_h C_e=W spinTwo+bulk_e`. Continuity of the exact source moments proves integrability on the original finite interval. Both boundaries are evaluated, giving

```
integral_(a_e)^V W(h) nativeSpinTwoTrace(e,q,h,x,[y,X,k]) dh
  = -integral_(a_e)^V bulk_e(h) dh.
```

Intervals with `V=a_e` have zero length. The degenerate branch uses the proved finite diagonal identity, including its retained bulk contact. No diagonal exclusion, source-clock replacement or boundary-vanishing premise is introduced.

## Remaining physical scope

The proved signed direct-minus-image identity retains both distinct domains. Its cutoff satisfies `V>=a_image`; the physical signs prove `a_direct<=a_image`. Joint radial/angular bounds, horizon/cusp limits, physical lift and source-contact currents, independent SS/SV/VV amplitudes, and complete cancellation remain required. The finite source transfer alone does not prove extinction or RH.

## Lean certificate

[ThetaCuspHawkingBMSpinTwoDelayCharacteristic](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSpinTwoDelayCharacteristic.lean), namespace `RHTower.D4BMSpinTwoDelay`, now also contains:

- `causalDelayStart_nonneg`, `causalDelayStart_direct_le_image`: exact physical branch domains.
- `delayArgument_characteristic`, `delay_original_trace`: original invariant and full physical kernel identification.
- `delayCurrent_endpoints`: both actual endpoint values, derived from the native primitive and original clock.
- `full_delay_finite_transfer`: exact finite transfer on either entire physical branch. Nondegenerate continuity and the already proved degenerate contact establish the integral identity.
- `signed_delay_finite_transfer`: direct-minus-image assembly with distinct lower endpoints.

The earlier nine public results remain unchanged. The new proofs introduce no boundary, smoothness, integrability, decay or cancellation premise. Physical-domain restrictions are carried by the radius and cutoff types. The endpoint-value theorem alone is not used to justify a singular integration by parts: the degenerate integral uses the previously proved limiting current and integrable bulk.

Scratch verification passed. Final audit of the exact changed leaf passed in 52 seconds, three jobs, using 4,136 cached own modules, 20,533 artifact links and twelve path dependency packages. No dependency or umbrella rebuild ran. Only the seven new public theorems were axiom-audited in a separate scratch file; each reported only `propext`, `Classical.choice`, and `Quot.sound`. Verified source and five artifacts were installed byte-identically after checking that the original source prefix was unchanged. The existing umbrella import remains unique; it was not built. Indexing completed with one changed file, and the generated API includes both transfer theorems. Formal lint passed with existing large-file warnings; fifteen local document links passed. All owned handles reached terminal status, and the owned Lean/Lake process check was clear. Scratch, isolated audit and search-result files were removed. The frontier map and universal ledger were not edited. No mathematical computation ran.

## Search applicability and next cancellation mechanism

Own deep queries were `moving endpoint transposition`, broad OR `characteristic reflection`, and broad OR `Green concomitant conserved bilinear density`. Candidate statements, source arguments, methods, proof ideas and ingredient sets were inspected. The source inventory reported 56,473 files and 385 pending/stale files; semantic coverage was incomplete, and most relevant compiler metadata was source-only. Reflection/eigenvector and quaternion-unit suggestions did not establish the actual causal endpoint transfer. The source-current query recovered the existing original complex-bilinear `CommonSourceGreen` transpose and angular/radial divergence, which must be paired with the transferred bulk under its actual measure.

Own broad arXiv searches used glancing, caustic and billiards with 2026 date terms. [Yi, Leakage detection, collision relation, and self-adjoint cancellation in multi-velocity systems](https://arxiv.org/abs/2606.25218) (June 2026; July v2 inspected) gives a useful pairing mechanism: decouple the operator and its conserved density together, so cross-sheet terms cancel modulo smoothing. Its Hermitian pairing, separated characteristic sheets and microlocal remainder do not establish the exact complex-bilinear HB current. The concrete candidate is to derive the corresponding exact weighted source-current identity, retaining the remainder and all physical faces. No paper premise enters Lean. [Bogaevskii and Rouleux, Asymptotic solutions: glancing trajectories, Lagrangian singularities, and Bessel cylinders](https://arxiv.org/abs/2606.26962) (June 2026) supplies a semiclassical normal-form perspective, but no applicable exact current identity was extracted.

A sharper analytical consequence of the transferred geometry suggests the next radial estimate. Put `t=h-x+y`, `d=x-y_e`, `C=cosh t`, `S=sinh t`, and `D=cosh x cosh y_e`. In the causal interior `t>|d|`, define

```
r=(Z-1)/A=(C-cosh d)/S,
b=B(Z-1)/A^2=C(C-cosh d)/S^2.
```

Since `1<=cosh d<=C` and `S^2=(C-1)(C+1)`, one has `0<=r<=S/(C+1)<=1`, `0<=b<=C/(C+1)<=1`, and

```
0 <= 3b^2-r^2
   = (2C^2+1)(C-cosh d)^2/S^4
   <= (2C^2+1)/(C+1)^2 <= 2.
```

The exact moment factorization therefore rewrites the bulk as

```
U(Z)[r^2 W''-3rb W'+(3b^2-r^2)W].
```

It yields the radius-independent geometric domination
`|bulk|<=|U(Z)|(|W''|+3|W'|+2|W|)`, including approach to the coincident characteristic from either branch. The [uniform transport proof](hb-uniform-spin-two-delay.md) now formalizes this geometric bound, confines the original invariant to `[1,exp(V)]`, bounds both actual source moments and both original clock derivatives, and proves one finite-delay bulk bound uniform over both entire radial domains. These eleven results are separate from the seven transfer theorems above. It targets the actual uniform radial transport needed to compare the transferred bulk with the full physical current.
