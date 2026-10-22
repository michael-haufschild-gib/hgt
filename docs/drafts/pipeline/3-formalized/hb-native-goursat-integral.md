# HB: closed-cone integral equation for the full theta-source kernel

Status: `FORMALISED`: both public identities passed their exact-module build and axiom audit. The full angular inverse identification, complete physical current extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent tensor amplitudes and all original physical currents. This result supplies the full native kernel's source equation, including its causal edges, needed before matching its integrated residual to the constructed physical inverse.

## Literal full-source identity

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGoursat`. Namespace: `RHTower.D4BMNativeCircle`.

Write `Q(X,k)=fullSquarePotential q ![X,exp(k)]`, the complete theta half-square. The existing native kernel is

```
K(h,x,y;X,k)=mean(q,arcosh(Z(h,x,y)),X,k),
Z(h,x,y)=(cosh(h)+sinh(x)sinh(y))/(cosh(x)cosh(y)).
```

For a fixed source coordinate `y`, put `R(u,v)=K((u+v)/2,y+(u-v)/2,y;X,k)` and `Delta=exp(2k) partial_X²+partial_k²-partial_k`. The theorem `nativeRiemannKernel_goursat` proves

```
R(u,v)=Q(X,k)+integral_0^u integral_0^v
  Delta R(a,b)/(4 cosh(y+(a-b)/2)^2) db da,
u,v>=0.
```

Its Lean statement uses the original `CausalPoint` and `angularAction`, whose definition is that full basepoint Laplacian. It has no supplied source equation or inverse-identification hypothesis. The complete signed Fourier remainder and all cusp powers remain in `Q` and its angular action.

## Characteristic limits and FTC

The exact invariant factorization is

```
Z=1+2 sinh(u/2)sinh(v/2)/(cosh(y+(u-v)/2)cosh(y)).
```

Thus `Z>1` in the open quadrant and `Z=1` on both axes. The existing full-source Darboux equation and the literal derivatives of `Z` give

```
partial_v partial_u R=Delta R/(4 cosh(y+(u-v)/2)^2)
```

in the open quadrant. For fixed `u>0`, the proved characteristic limit of `argumentFirst` is `Delta Q/2`, and the geometric factor `partial_u Z` tends to zero as `v` decreases to zero. Consequently the actual interior `partial_u R` tends to zero on that axis.

The full angular action is continuous on the closed physical chart because it equals the average of the full source Laplacian. A private extension replaces `Z` by `max(1,Z)` only to apply global continuity lemmas; it equals the original kernel and action at every integrated point. FTC with the actual endpoint limits gives `partial_u R(u,v)=integral_0^v Delta R(u,b)/(4 cosh²) db` for positive `u,v`. A second FTC step uses continuity of `R` on the closed interval and its original characteristic value `R(0,v)=Q`. Zero-length edges are included directly.

The proof does not assign an endpoint derivative by evaluating the interior quotient formula at `Z=1`. It uses the previously proved one-sided limit. No second derivative at the characteristic, wave-domain admission or angular integral interchange with an unbounded operator is assumed.

## Original Dirichlet source kernel

`nativeDirichletCausalKernel` is the literal causal direct-minus-image kernel

```
K_D(h,x,y)=1/2 [1_(|x-y|<=h) K(h,x,y)
                -1_(|x+y|<=h) K(h,x,-y)].
```

`nativeAngularCorrection` is the displayed double integral on its original causal support. `nativeDirichletCausalKernel_volterra` proves the exact decomposition into the free causal interval kernel multiplying the full `Q`, plus half the direct-minus-image angular correction. Both support conditions and the original factor one half remain explicit.

## Remaining comparison

The three principal native responses already equal the constructed `principalTimeResponse`. The full kernel identity above must now be integrated against the original radial forcing. The actual angular derivatives must pass through that integral, and the cutoff-subtracted response must be admitted to the original joint wave form with its modular side identifications, cusp control and Dirichlet trace. Those steps are not supplied by this kernel theorem. The complete physical current pairing still requires evaluation.

## Search and verification

Broad Darboux and Friedrichs searches found the actual full-source Darboux equation and completed joint form. Deep hyperbolic-mean and weak-wave searches recovered the original native interior kernel equation and the joint energy uniqueness theorem. The available nonseparated radial-family admission requires an angular-energy-valued smooth family with compact support strictly inside the negative radial ray; those premises have not yet been established for the native residual. Generated ingredient groups did not supply them.

The proof uses the existing full-source characteristic contact and actual mathlib FTC with endpoint limits. Candidate declarations and source-argument views were inspected. Searches reported incomplete semantic coverage and predominantly source-only metadata; a later squared-radius smoothness search also reached its deadline. No generated ingredient group was accepted as a proof.

Validation: `lake env lean` checked the scratch proof. Final `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeGoursat` passed in 38 seconds, three jobs, using an isolated exact-module audit with 3,944 existing own-module caches and 11 package caches. No dependency, full or umbrella rebuild was run. The 455-line source and five build artifacts were installed byte-identically to the audit. The unique import is wired into `formal/GaloisForLFunctions/RHTower.lean` without building that umbrella.

Only `nativeRiemannKernel_goursat` and `nativeDirichletCausalKernel_volterra` were checked with `#print axioms`; both report exactly `[propext, Classical.choice, Quot.sound]`. Formal lint passed with existing large-file warnings. Module-filtered corpus discovery finds both public theorems at source lines 392 and 442. Mathematical computations were not run. The frontier map and route-independent STATUS ledger were not modified.

Broad Milne and OR Huygens/Kirchhoff searches also returned no usable wave uniqueness ingredient in their inspected results. The latter retrieved Kirchhoff incidence results and the actual continued-field Laplacian decomposition, which retains a residual forcing. These searches reported incomplete semantic coverage; this is not a claim of corpus-wide absence.
