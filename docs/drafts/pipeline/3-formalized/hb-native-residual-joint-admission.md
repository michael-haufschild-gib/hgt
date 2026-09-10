# HB: literal residual in the original joint L2 space

Status: `FORMALISED`: seven public theorems in `ThetaCuspHawkingBMNativeResidualAdmission` and one exact source-integral identity in `ThetaCuspHawkingBMNativeSourceEquation`. The physical inverse comparison, complete current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, retaining the independent SS/SV/VV amplitudes and all onset, horizon, AdS, temporal and cusp currents. This result constructs the literal cutoff residual as a strongly continuous vector in the same spatial Hilbert space as the physical joint evolution. It removes an actual admission obligation in their comparison.

## Exact result

Let `V=fullNullResidual`, the original full theta response minus all three original principal radial responses multiplied by their cutoff powers. Define

```
v(tau,x,z)=V(tau+x,tau-x;z.re,log(z.im)),
mu=radialMeasure.prod D4BMModularCore.measure,
radialMeasure=volume.restrict {x | x<0}.
```

For every `q : XiZeroCopy`, complex rate `s`, complex amplitude and real time `tau`, the new module proves:

- `nativeJointResidualField_memLp`: the literal function `v(tau)` belongs to `L2(mu)`.
- `nativeJointResidual_continuous`: its constructed L2 class is strongly continuous in `tau` on all of `R`.
- `nativeJointResidual_original_ae`: that class represents the literal `V` in the original coordinates and measure.
- `nativeJointResidual_zero_of_nonpos`: the class is zero for `tau<=0`, including onset.

These results take no supplied integrability, continuity, boundary-value or evolution-identification premises. They are quantified source-family theorems; they do not assert RH.

Three further public theorems provide the actual estimates and integral identity:

```
nativeCutoffResidual_uniform_bound:
  for each D, exists B>=0, forall d in [0,D], z in fd,
  norm(nativeCutoffResidual(q,d,z))<=B.

nativeResidualIntegral_uniform_bound:
  for each T, exists B>=0, forall p,r in [0,T], z in fd,
  norm(nativeResidualIntegral(q,s,amplitude,p,r,z))<=B.

fullNullResidual_eq_nativeResidualIntegral:
  V(p,r;z.re,log(z.im))=nativeResidualIntegral(q,s,amplitude,p,r,z)
  for every real p,r.
```

Here `nativeResidualIntegral` is one quarter of the double source integral of the original `nativeCutoffResidual` at the causal radius against the original odd source. Its globally continuous radius is `arcosh(max(1,Z))`; on every nonnegative causal source rectangle this is the original physical radius. No kernel is changed on that rectangle.

## Conjecture, proof and refinement

The first conjecture was that the existing rapid cusp remainder estimate, applied uniformly over a bounded causal radius interval, supplies the missing joint-space admission. The proof realizes that estimate for the actual source integral.

Above height `3+exp(D)`, the cutoff equals one and `cuspMeanRemainder_rapid_bound q 0` gives a common bound. Below that height, the product of the bounded radius interval with the truncated modular cell is compact. Joint continuity of the full circle mean and the three transported principal powers gives another common bound. Their maximum bounds the original cutoff kernel on the entire modular cell.

On a bounded null-coordinate box, continuity bounds the causal radius and the odd source. Two interval-integral norm estimates then bound the double integral, including its factor `1/4` and the actual rectangle area. The scalar principal identity is exposed as `radialResponse_null_native` in `ThetaCuspHawkingBMNativeSourceEquation`: it expresses the actual radial response as its null-rectangle integral with the exact physical kernel and Jacobian. The residual proof subtracts all three principal integrals, using the previously proved circle/Legendre identity.

The initial positive-quadrant identity alone was insufficient for continuity across the characteristic edges. The refined conjecture was that the same integral identity extends to all real null endpoints because the original source vanishes when either source endpoint is nonpositive. Strict source-cone vanishing follows from the original onset condition; continuity extends it to the edge. The actual scalar responses vanish there by their retarded support and continuity. The full source integral also vanishes there. Thus the literal residual and its new integral representation both vanish whenever `p<=0` or `r<=0`, proving the global identity without imposing additional data.

For `abs(tau)<=T`, finite propagation confines the literal field to `abs(x)<=T`. The preceding bound supplies

```
norm(v(tau,x,z)) <= B_T indicator[-T,T](x),  z in fd.
```

This majorant belongs to L2 of the original product measure: the radial interval has finite restricted volume and the original modular measure is finite. The field's joint pointwise continuity follows from the global double-integral identity and continuity of moving-endpoint integrals. `continuous_toLp_two_of_dominated`, applied locally in time, proves strong L2 continuity. The exact `MemLp.toLp` representative then proves the original-field and zero-onset statements.

## Remaining mathematical construction

The residual now inhabits the actual spatial Hilbert space continuously. The [modular-transport extension](hb-native-modular-transport.md) now proves a globally modular representative with full germ agreement on every closed-cell chart. Membership in the closure of the first-derivative energy graph `jointDomain` and actual weak spatial action still need proofs. The interior mixed-null field equation and L2 admission alone do not establish those claims.

For the difference from the constructed joint evolution, the active analytical target is

```
B u(t)+(I-B) integral_0^t (t-s)u(s) ds=0,
B=jointEmbedding * adjoint(jointEmbedding).
```

The existing contractivity and dense range of `jointEmbedding` give a bounded-resolvent energy method once this actual identity is proved. It has not been assumed as a replacement for the missing construction.

Broad spherical-averaging search recovered the source-level Maass homogeneous-space dictionary and its section cocycle. The modular-transport extension now identifies the actual native chart with the corpus rotation orbit and proves invariance by a shift of the original periodic angular integral. It also proves full closed-cell germ compatibility for the actual residual; no change of the angular measure is required.

## Search evidence

Broad OR null/causal/rectangle intake and deep source-diamond method search recovered the actual scalar null-integral construction. Deep compact-parameter/cusp-L2 search recovered the needed rapid remainder estimate and dominated-continuity method. The latter's existing use in `FokasLenellsSecondTimeForcing` supplied a concrete proof pattern; the new proof constructs the majorant for this literal residual.

Broad joint-space and spherical-averaging searches, followed by deep weak-modular and compact-group method searches, located the actual joint measure, spatial space, first-derivative graph and homogeneous-space dictionary. Declarations, candidate lemmas, source arguments, proof ideas and ingredient sets were inspected. Unrelated proposed groups were not treated as discharged premises. Search inventory was complete; semantic coverage and source refresh were partial, one later search reported incomplete source indexing, and compiler metadata was predominantly source-only. Candidate applicability used in the result was checked in Lean.

## Validation

`lake env lean` passed the completed 599-line admission scratch proof without warnings. Final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeResidualAdmission` passed in 118 seconds, three jobs. Its isolated audit reused 4095 existing project dependency caches and 11 installed dependency packages.

The 669-line source-equation prerequisite passed final `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeSourceEquation` in 59 seconds, three jobs, reusing 4029 project caches and the same 11 dependency packages. Only its new `radialResponse_null_native` theorem was audited; previous theorem audits were not repeated.

The seven new admission theorems and the one new source-equation theorem each report exactly `[propext, Classical.choice, Quot.sound]`. No mathematical computations or proof oracles were used. Both sources and their five build artifacts were installed byte-identically to their audits. The source-equation import remains unique in the area umbrella; the new admission import is wired there once. No umbrella or dependency rebuild ran.

Formal lint passed with existing large-file warnings. Module-filtered lexical discovery finds all seven new public admission theorems at lines 80, 156, 465, 532, 548, 580 and 586. This lexical discovery exposes no additional compiler-freshness metadata; the final Lean checks above are the validation evidence.

The frontier map and route-independent STATUS ledger were not edited. No Git commands or launcher runs were used.

All owned Lean/Lake, search and lint processes finished. The owned scratch directory and both isolated audit directories were removed.
