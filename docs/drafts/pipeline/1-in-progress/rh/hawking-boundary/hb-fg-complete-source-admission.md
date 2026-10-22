# HB FG: complete source admission at the physical weight

Target: full temporal/metric/left-QNM matching; RH remains open.
Prior authoritative progress: `WeightedResponseAdmission` proves weighted
absolute integrability of the original smooth response for every `p>5/2`.

[BRIDGE] The complete source `F=B-s(s-1)Q/4`, with the original fundamental
rate `s=physicalRate(q,branch)`, is absolutely integrable on the hyperbolic
plane against `exp(-(1-2 Re(s))*dist(z,i))`. No cusp, cutoff, cross term,
clock shift, or angular remainder is removed.

Analytical proof: write `H=max(1,y,1/y)`. Each of the three actual principal
cusp powers has real exponent at most two. On height above two its absolute
value is at most a constant times `y^2`; below two the actual cutoff vanishes.
Modular invariance and orbit-height control give `|globalCuspCutoff|<=C H^2`.
The corpus bound for the full square, with exponent `gamma<2`, gives the same
quadratic ceiling because `H>=1`. On a radius-R ball, `H<=exp(R)` and area
is at most `8 exp(R)`. Both terms therefore have absolute ball mass at most
`C exp(3R)` and admit every radial weight with exponent `p>3`.
The actual response already admits these weights. Sum and scalar multiplication
preserve absolute admission of the complete F. The original Xi strip gives
`-2<Re(s)<-1`, hence the unchanged physical exponent exceeds three.

Whole-route implication: this supplies the complete source input for the
fixed-plane cap representation and differentiation argument. It is not the
polar change-of-variables theorem, parameter differentiation theorem, or
physical noncompact left-QNM matching theorem. Those obligations remain.

Formal source status: `ThetaCuspHawkingBMCompleteSourceAdmission` proves the
cutoff and full-square estimates, admission of the complete F, change of radial
center, and the original physical-rate specialization. Final scratch check
87.91 seconds; exact single-leaf audit 42.58 seconds, two jobs, no warnings.
The umbrella import is wired without an umbrella build. Frontier map is read-only.

## Original plane kernel

Set `D=cosh(x)cosh(d)+sinh(x)` and `c_x=min(cosh(x),exp(x))/2>0`.
The identity `D=cosh(x)(cosh(d)-1)+exp(x)` gives `D>=2 c_x cosh(d)>=c_x exp(d)`.
The corpus theorem `timeOnset_pair_bound(v,-Re(v))` supplies a constant B with
`|onsetFirst(v,u)|<=B exp(Re(v)u)` for every real u, including the onset region.
Consequently the unchanged kernel
`K_v(tau,x,d)=cosh(x) onsetFirst(v,tau+log(D))/D` obeys
`|K_v|<=cosh(x) B exp(Re(v)tau+(Re(v)-1)log(c_x)) exp(-(1-Re(v))d)`
whenever `Re(v)<=1`. At `v=2s` its exponent is exactly the admitted physical
exponent. The constant is independent of the source and target points when
tau and x are fixed. This proves absolute integrability of `K_(2s) F` around
every target. All terms in both arms can be retained with the original factor
`parameter(q,branch)*power(2s,2)*amp^2/(2*pi)`.

The exact pointwise identity is
`sourceJac(x,log(cosh(d))) onsetFirst(v,sourceTime(tau,x,log(cosh(d)))) *
 sinh(d)/cosh(d) = K_v(tau,x,d)*sinh(d)`.
It retains the original Jacobian. It does not by itself prove the global
hyperbolic polar integration formula or identify the plane integral with a cap.
Formal kernel status: `ThetaCuspHawkingBMPlaneKernelAdmission` proves the bound,
continuity, exact pointwise density identity, single-arm admission, and
`original_combined_plane_integrable`, which retains both arms, squared amplitude,
and original normalization. Final scratch check 9.54 seconds; exact single-leaf
audit 10.03 seconds, two jobs, no warnings. Both new leaves use default heartbeats.
Both umbrella imports are wired. Repository lint reports only the pre-existing
unreachable `ThetaCuspHawkingBMOnsetTransgressionHorizon` error plus existing
file-size warnings; it is not reported as passing. Installed sources match the
audited copies. Both oleans are installed; owned processes and scratch files
are cleaned up. Only successful check/audit logs and the lint log are retained.
Full matching and RH remain open: the global cap identity, parameter
differentiation, and physical left-QNM pairing have not been proved by these leaves.

Search evidence: broad OR search for cusp/growth, deep mechanism searches for
weighted admission and parameter differentiation, and broad onset/coarea/polar
queries. Completed requests report partial=false and complete inventory;
compiler metadata is largely source-only/pending, so retrieved candidates are
checked in Lean. Broad coarea hits were mostly discrete fibre identities.
Refining `polarCoord` to mathlib found the usable Euclidean integral and
lintegral change-of-variables theorems in
`Mathlib.Analysis.SpecialFunctions.PolarCoord`; their adaptation to the actual
hyperbolic circles is still required and is not claimed proved.

Broad recent-paper search `transmutation` found Jin–Ma–Zuazua,
[arXiv:2601.03616](https://arxiv.org/abs/2601.03616), revised June 2026.
Its abstract describes a Gaussian wave-propagator representation of diffusion.
That operator-specific transform does not identify the fixed causal/Hawking
kernel here; no result from the paper is assumed.
