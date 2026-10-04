# SZ: actual Gamma pairing across both sharp boundaries

- **Stage:** 3-formalized
- **Route:** SZ, actual ground global Gamma-domain admission
- **Parent:** ../1-in-progress/sz-ground-global-gamma-domain.md
- **Status:** all boundary and sharp-test theorems passed production and public-declaration axiom audits

## Exact new statement

Let rho(h)=exp(-h/2)/(1-exp(-2h)), T_h f(x)=f(x+h), Rf(x)=f(-x), and Z denote positive-half-line zero extension. The literal operator

Bf(s) = integral over t>0 of rho(s+t) f(t)

is a bounded complex-linear operator on positive-half-line L2. For arbitrary f,g in that space, with no smoothness or full Gamma-domain assumption,

integral over h>0 of rho(h) <(T_h-1)Zg,(T_h-1)RZf> = -<g,Bf>.

The integral is absolutely convergent. For an actual aperture-supported f on [-a,a], the right exterior action is B applied to t -> f(a-t); its mixed Gamma pairing with the physical exterior test T_(-a)Zg is exactly the negative pairing with this action. The left action follows by reflection. Both are bounded in ordinary L2. The constants merely establish boundedness; no sharp-constant claim or numerical experiment is made.

Separately, every sharp restriction to [-a,a] of a compact smooth global test belongs to the full Gamma multiplier domain. Its form lift is the actual derivative primitive plus g(-a) times the actual zero-slope pole. This does not assume the test vanishes at the endpoints.

## Dependency-closed paper proof

1. Exponential convexity gives rho(h)<=2/h for h>0. Apply the corpus Carleman square inequality to rho/2. The resulting majorant controls the literal Bochner integral action and its L2 norm. Almost-everywhere integrability, additivity and scalar compatibility construct B as a continuous linear map.
2. Holder applied to the Carleman majorant proves absolute integrability of conj(g(s))*rho(s+t)*f(t) on the positive quadrant. This validates Fubini before any exchange of integrals.
3. Extend the kernel by zero to the whole plane. The measure-preserving shear (h,t)->(h-t,t), followed by Fubini, identifies its integral with the Gamma-weighted translation correlation <T_h Zg,RZf>. The integrand vanishes for h<=0. Reflection in the inner-product integral fixes the complex conjugation convention.
4. For h>=0, <Zg,T_h RZf>=0 by disjoint supports, and <Zg,RZf>=0. Translation unitarity then gives the exact negative mixed-jump identity. The absolute integrability from step 2 transfers to the mixed jump.
5. Translate the aperture's right endpoint to zero. Reconstruct the translated source as RZ applied to its reflected positive restriction; its value at the endpoint is irrelevant because singleton measure is zero. Translation covariance transfers the identity to the actual aperture. Reflection exchanges the endpoints and preserves the mixed-jump pairing, establishing the left identity.
6. For a compact smooth test g, FTC gives primitive(g')=g-g(-a) on the aperture. Add g(-a) times the pole profile at slope zero. Existing unconditional primitive and polar multiplier-admission theorems yield full Gamma-domain admission of this literal sharp restriction.

## Relevance and remaining gap

This proves the actual cross-boundary block previously left outside `CCMScrewNullLogRegularity`; it does not postulate a bound or an exterior operator. It removes the sharp-boundary identification obligation in the proposed global-ground-domain proof. Combining both exterior actions with the exact interior ground forcing, extending from tests by density, and proving global multiplier admission still remain. No H1 regularity, prime dilation derivative, canonical-head sign, or RH conclusion follows yet.

## Corpus and novelty audit

Searches1224131,1224144,1224159,1224312 and1224434 were partial; freshness and compiler metadata were inspected. The last search had pending coverage. Existing results supply actual Gamma mixed-jump energy, the Carleman inequality, and primitive/polar multiplier admission. No retrieved result supplied the sharp mixed boundary identification. Search absence is not a claim of novelty beyond this corpus. No route is being retired.

## Lean audit

Production `CCMRestrictedWeilGammaBoundaryPairing.lean` (23 public declarations) passed final direct foreground audit37470 with no diagnostics. `CCMRestrictedWeilSharpSmoothDomain.lean` (4 public declarations) passed final direct foreground audit54474 with no diagnostics, after adding its explicit `SuzukiDirichletFormCore` import. Both used `lake --old env lean <leaf> -o <leaf.olean>`. No umbrella build. Both leaves have exactly one umbrella import.

All27 public-declaration axiom queries passed audit17789 with only `propext`, `Classical.choice`, and `Quot.sound`. No added axiom, unfinished proof, computation, heartbeat increase, full build, or subagent.

Global lint99878 exited1 on twelve unrelated unreachable modules, with no new-leaf or prohibited-declaration error. This is not a clean global lint result. Exact errors:


```text
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureChainProfile
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMApertureTranslationChains
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MertensProductDiamondPintz
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra
```
