# HB: original full-source delay horizon limit

Stage: 3-formalized for the original finite-delay target-horizon transport. Complete physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target is `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and every physical current retained. The [uniform finite-delay bulk theorem](hb-uniform-spin-two-delay.md) supplies radial domination. This result derives the ORIGINAL target-horizon bulk, transports it through its full finite causal delay integral, and identifies the resulting limit of the original signed native spin-two source action. It supplies the source-side horizon term for the physical radial/left-QNM comparison.

## Analytical conjecture loop and exact result

1. Derive the original horizon geometry. For fixed source radius `y<=0`, write `w=radialUnit(y)`, `a_direct=0`, `a_image=-2y`. The identity `radialUnit(x)=(1-exp(2x))/(1+exp(2x))` gives its horizon limit one. Substitute into the already proved compact invariant formula and the exact first/second time derivatives:

```
Z_direct -> exp(h)(1-w)+w,
Z_image  -> exp(h)(1-w)-w,
A,B      -> exp(h)(1-w),             as x -> -infinity.
```

These are limits of the original functions, with no replacement kernel. For each finite physical source radius, `w<1`; therefore the limiting slope is strictly positive. The exact gap identity is

```
Z_horizon-1=(1-w)[exp(h)-exp(a_branch)].
```

2. Test the normalized coefficients in the strict causal interior. For `h>a_branch`, the gap is positive and both actual coefficients tend to `r=b=1-exp(a_branch-h)`. The original source moment `U(Z)` is continuous at every `Z>1`: the original primitive is differentiable there, and `U(Z)=J(Z)/(Z-1)^2`. This uses the already proved primitive identity, not a new smoothness premise.

3. Retain and transport the actual clock derivatives. The previously constructed jointly continuous scaled clock jets and their nonzero denominator identify the limits of `W`, `W'`, and `W''` with their actual compact target radius-one values. In particular the moving terminal endpoint and both onset derivatives remain. The complete original bulk tends to

```
H_e(h)=U(Z_horizon,e)(1-exp(a_e-h))^2
       [W_horizon''-3W_horizon'+2W_horizon].
```

Thus the literal horizon bulk exposes `(partial_h-1)(partial_h-2)`. This is a proved source-clock operator identity in the limit; it does not yet identify or cancel the full physical current.

4. Transport the finite integral and return to the native source. Once `x<=y`, the original direct start is exactly zero; the image start is already `-2y`. The moving integration interval is therefore eventually equal to its limiting interval. The actual bulk is continuous on its open causal interval, using the actual primitive derivative, positive original slope, and actual clock jets. This supplies measurability. The earlier uniform bound supplies an integrable constant majorant on that bounded interval. Filter dominated convergence gives, for `V>=a_e`,

```
lim_(x->-infinity) integral_(a_e(x))^V originalBulk_e(x,h) dh
  = integral_(a_e)^V H_e(h) dh.
```

Both sides use the original Lebesgue interval integrals. Removing singleton endpoints for this measure argument does not delete a physical Green face. Combine both branches for `V>=-2y`, then use the [proved full finite delay transpose](hb-full-spin-two-delay-transfer.md):

```
lim_(x->-infinity) [ integral_direct W_x nativeSpinTwo_direct
                   -integral_image W_x nativeSpinTwo_image ]
  = -integral_0^V H_direct(h) dh + integral_(-2y)^V H_image(h) dh.
```

The angular base point and finite source radius remain arbitrary. The full native angular source, original finite clock, two distinct causal starts, and signed branch coefficients are preserved.

## Search applicability

Own broad/deep queries were OR `radiation field limit`, a mechanism query about transporting a parameter limit through moving causal support, `dominated convergence`, and `concomitant`. Statement candidates, source arguments, proof methods, proof ideas and ingredient groups were inspected. Results were partial: 56,490–56,496 files, 396–400 stale/pending source files, incomplete semantic coverage, and mostly source-only compiler metadata. Available methods included the actual theta screen-jet dominated-convergence proof and the centered Schur boundary integral proof. The installed filter dominated-convergence theorem supplied the transport mechanism; all original-source premises were proved in this owner and verified in Lean.

The concomitant search exposed the BM horizon-coordinate determinant identity and integrating-factor source-current identity. Their source/response coordinates and separated radial jet equations require an identification with the native physical response before they can be used here. The next constructive test is that identification with the derived signed horizon source action, retaining the complex bilinear transpose and all physical boundary densities.

Own broad arXiv words included redshift, endpoint, gluing and polyhomogeneous, with 2026 filters. [Dias, Rankin-Selberg duality via gluing](https://arxiv.org/abs/2607.22965) (July 2026; manuscript title page dated August 2026) constructs an anti-symplectic involution from a modified gluing transition. Its concrete setting is a finite-dimensional complex reductive representation and its dual Hamiltonian variety. The transferable idea to test is an actual transition/intertwining identity before inferring a current symmetry. No such identification for HB is claimed, and the paper supplies no Lean premise.

## Lean certificate

[ThetaCuspHawkingBMSpinTwoUniformDelay](../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSpinTwoUniformDelay.lean), namespace `RHTower.D4BMSpinTwoUniformDelay`, adds seven public theorems to the already verified owner:

- `horizon_geometry_limits`: original invariant and both time-derivative limits.
- `horizon_ratio_limits`: both original normalized coefficients, with exact branch delays.
- `clock_horizon_limits`: original clock and its two actual derivative limits.
- `original_bulk_horizon_limit`: full original bulk on each strict causal interior.
- `original_bulk_horizon_integral`: original finite causal integral with its moving lower bound.
- `signed_bulk_horizon_integral`: both branch integrals with their original signs and starts.
- `signed_native_horizon_integral`: original signed native spin-two source action through the established finite transpose.

The new public theorem statements supply no additional regularity, integrability, domination, boundary-vanishing or current-cancellation premises. Finite radius/window restrictions are intrinsic domain types. The previously verified owner prefix is preserved.

Scratch checking passed. The exact isolated owner built successfully in 100 seconds, three jobs, using 4,137 cached own modules, 20,538 artifact links and twelve dependency path packages. No dependency or umbrella was rebuilt. The build emitted one informational `ring_nf` suggestion, with no warnings or errors. Only the seven new public theorems were axiom-audited in a separate scratch file; each reported only `propext`, `Classical.choice`, and `Quot.sound`. Verified source and five artifacts were installed byte-identically. The existing umbrella import remains unique and was not rebuilt. Indexing completed (two changed sources in the shared workspace), and the generated API contains all seven new theorem statements. All eighteen local links in the three affected route cards passed. Global formal lint reported one error: the separate module `GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyMeanSquare` is unreachable from its theorem-area umbrella. This task did not edit that module; the changed owner has its unique existing umbrella import. Large-file warnings also remain elsewhere. All owned handles reached terminal status, the owned Lean/Lake process check was clear, and this task’s scratch/audit/search files were removed. The frontier map and universal ledger were not edited. No mathematical computation ran.

## Remaining physical-current identification

The [original lift-current and source-contact theorem](hb-physical-lift-horizon-current.md) now gives both lift horizon fluxes and their finite original onset integrals. Its contact resolves into the actual square and gradient source pairings, with the terminal correction retained. Matching the causal response and cross-currents to these explicit terms remains the next current comparison.

This establishes the original finite source-delay horizon action at fixed source radius and angular point. Transport under the complete physical radial/angular measure, evaluation of the principal angular flux, the lift/response cross-currents, source-contact correction, physical temporal faces, infinite-time transport, and the independent SS/VV coefficients remain open. The direct attack is to insert the derived `(partial_h-1)(partial_h-2)` source action into the actual master/Einstein Green current on the same finite domain, then derive the remaining oriented faces. No current is assigned zero by the finite source-delay limit.
