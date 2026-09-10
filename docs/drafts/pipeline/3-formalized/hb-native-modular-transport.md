# HB: modular transport of the literal causal theta residual

Status: `FORMALISED`: eight public theorems in `ThetaCuspHawkingBMNativeModularTransport`. The physical inverse comparison, complete current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, retaining the independent SS/SV/VV amplitudes and every physical current. This result closes the actual modular compatibility needed in the native/physical inverse comparison. The original joint L2 residual now has a globally modular representative retaining its full local field near every point of the closed fundamental domain.

## Exact result

For the original complete theta circle source, `source_modular_shift` proves that, for each modular transformation `g`, source `q` and base point `z`, there is one real shift `phi` such that

```
source(q,d,theta+phi,(g z).re,log((g z).im))
 = source(q,d,theta,z.re,log(z.im))
```

for all real radii `d` and angles `theta`. No transformation law for the circle is supplied as a hypothesis.

`mean_modular` proves invariance of the original average with its original interval and normalization:

```
mean(q,d,(g z).re,log((g z).im))=mean(q,d,z.re,log(z.im)).
```

`fullNullResponse_modular` passes this through the original source integrals. It holds for arbitrary complex rate and amplitude and all real null endpoints `p,r`.

`fullNullResidual_cell_compatible` proves the full germ compatibility of the actual residual

```
V(p,r;X,k)=fullNullResponse(p,r;X,k)
  -sum_i principalNullResponse_i(p,r) cutoffPower(alpha_i,[X,exp(k)]).
```

All three original Weyl amplitudes and powers remain present. Whenever `z` and `gamma z` belong to the closed modular cell, the two angular expressions for `V` agree on a full neighborhood of `z`. This includes all paired seams and elliptic corners.

The definition `globalNativeResidual` extends that literal field by its compatible closed-cell representatives. Three theorems give its properties:

- `globalNativeResidual_invariant`: pointwise invariance under every `PSL2Z` element.
- `globalNativeResidual_germ`: agreement with the original residual on a neighborhood of every closed-cell point.
- `globalNativeResidual_eq_on_fd`: exact agreement at every point of the closed cell.

Finally, `nativeJointResidual_global_ae` proves that the previously constructed joint L2 class represents

```
(x,z) ↦ globalNativeResidual(q,s,amplitude,tau+x,tau-x,z)
```

in the original measure `radialMeasure.prod D4BMModularCore.measure`. Thus the globally modular representative belongs to the same strongly continuous joint L2 curve already constructed from the literal residual. The new theorem does not change that curve or its measure.

## Conjecture, proof and refinement

The initial conjecture was to identify the native circle mean with compact-stabilizer averaging. Broad rotation/stabilizer/spherical search recovered the existing principal-series equivalence between the stabilizer of `i` and the complex unit circle, along with `realSphericalRotation`, its addition law and surjectivity through `Circle.exp`. The proof reuses those constructions.

The actual chart identification is

```
circle(d,theta,z)=z.toSL2R k(theta/2) (i exp(d)),
k(phi)=[[cos(phi),-sin(phi)],[sin(phi),cos(phi)]].
```

The canonical section acts as `w ↦ z.re+z.im*w`. Direct real and imaginary parts of the original Möbius action give denominator

```
cos(phi)^2+exp(d)^2 sin(phi)^2
 = exp(d)[cosh(d)-sinh(d)cos(2phi)].
```

The hyperbolic identity and double-angle formulas then give exactly the original positive horizontal offset and height ratio. The half-angle convention is retained throughout.

The existing section cocycle satisfies `g(gamma z) k(gamma,z)=gamma g(z)`. Since that cocycle is an actual rotation, multiplication shifts the original circle angle by a constant independent of radius and angle. The original full theta half-square is modular invariant, yielding `source_modular_shift` pointwise.

The proof then uses `Function.Periodic.intervalIntegral_add_eq` directly on the original angular integral. This avoids a separate Haar-measure normalization construction: the original interval of length `2*pi` and its factor `1/(2*pi)` are unchanged. The resulting mean identity passes through both original causal integrals, with no exchange of integration order.

The next conjecture was that the cutoff residual preserves the required modular boundary data. Source search recovered the stronger existing full-germ mechanism in `SquareResidualModular` and `CellGermExtension`. If the matrix's lower-left entry is zero, its action is an integer translation, preserving every cutoff height power. Otherwise, `nonparabolic_cell_overlap_low` places both overlapping charts strictly below height two. Continuity keeps them there on a neighborhood, and every cutoff power is zero on that neighborhood. The actual full-response modular identity therefore proves equality of the complete residual germs.

The existing `cellGermExtension` construction uses proper discontinuity to control all nearby closed-cell representatives. Applying it to the proved residual compatibility gives the global invariant field and exact local agreement. Any existing derivative is preserved by germ equality; no extra differentiability claim is inferred from germ equality alone.

## Remaining mathematical construction

The missing inverse step is still the actual bounded-resolvent weak identity. For the continuous joint-L2 difference `u` and `W(t)=integral_0^t (t-s)u(s) ds`, the target is

```
B u+(I-B)W=0,
B=jointEmbedding * adjoint(jointEmbedding).
```

The refined analytical candidate is to prove the weak elliptic equation `A W=-u`, admit `W` to the original first-derivative energy graph, and then derive this identity by the adjoint definition. The active inverse-identification card records the concrete cutoff-energy estimate to attempt. Neither that estimate for the actual field nor its graph-limit argument is installed here. The corpus's `RadialEnergyFamily.graph_mem` supplies an admission mechanism for actual smooth compact angular-energy-valued radial families; its premises have not yet been constructed for the native time primitive.

Modular compatibility is now closed. Energy-form admission, the actual weak spatial action, physical inverse equality and the complete current pairing remain open. No onset, horizon, AdS, temporal or cusp current is evaluated or discarded by this result.

## Search and validation

Broad rotation/stabilizer/spherical and periodic-integral searches, followed by deep circle-transport method search, recovered the actual rotation group, section cocycle and shift-integral theorem. Broad cutoff/modular/boundary search found the actual full-germ gluing pattern. Declarations, candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. The deep circle group correctly exposed the orbit-identification obligation; unrelated generated inversion and residue groups did not prove the cutoff claim. Exact applicable statements were read and verified in Lean.

The initial energy-estimate searches returned weak-derivative candidates and unrelated semantic matches; none was treated as the missing energy estimate. Search inventory was complete for the circle and cutoff requests, with partial retrieval and predominantly pending or source-only compiler metadata. One later energy request reported coverage pending. These search results support discovery; the final Lean audit establishes the new theorem claims.

The completed scratch proof passed `lake env lean`; its unused tactic warning was removed before the final audit. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeModularTransport` passed in 11 seconds, two jobs, without warnings. The isolated audit reused 4114 existing project dependency caches and 11 installed dependency packages. No dependency or umbrella build ran.

Only the eight new public theorems were checked with `#print axioms`. All report exactly `[propext, Classical.choice, Quot.sound]`. The 299-line source and five build artifacts were installed byte-identically to the audit. The new module is wired once into `formal/GaloisForLFunctions/RHTower.lean`.

Formal lint passed with existing large-file warnings. Module-filtered lexical discovery finds all eight new public theorems at lines 153, 176, 213, 239, 268, 275, 282 and 290. The lexical result supplies no additional compiler-freshness metadata; the targeted build and new-theorem axiom audit are the validation evidence.

No mathematical computations, Git commands or launcher runs were used. The frontier map and route-independent STATUS ledger were not edited.

All owned Lean/Lake, search and lint processes finished. The owned scratch directory and isolated audit were removed.
