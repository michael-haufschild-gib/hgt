# PM: isolated canonical admission on the imaginary damping axis

- **ID:** pm-complex-damping-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** literal finite Möbius Fermi source, canonical Mellin boundary decay, unconditional Hardy critical zero and analytic zero isolation.
- **Lean:** `GaloisForLFunctions/RHTower/PMPowerDampedMobiusComplexBoundary.lean`.

## Exact positive classification

There exists delta>0 such that, for every real y with |y|<delta, the actual complex power-damped source A_(iy) belongs to L2((0,infinity),dt) if and only if y=0. This includes both signs of y and needs no RH, simplicity, zero enumeration, or unproved norm bound.

The source is literally `A_z(t)=-sum_(1<=d<=floor(1/t))mu(d)*d^(-z)*phi_d(t)`. Its coefficients and source agree exactly with the existing real power-damped definitions when z is real. All finite summands are retained. No completed prime support or substitute damping operator enters.

A stronger structural lemma proves critical-zero transport: if A_z is admitted, Re z=0, rho is a positive critical zero, and Im(rho-z)>0, then zeta(rho-z)=0.

## Dependency-closed paper proof

The finite source equals minus the supported dilation series of the first Fermi generator, since the remaining terms vanish pointwise. The damped Möbius Dirichlet series at s is exactly 1/zeta(s+z) when Re(s+z)>1. The first Fermi generator is canonically L2, so its Mellin transform is analytic for Re s>1/2. Analytic uniqueness extends its existing strip identity to the upper half-plane in that half-plane. Absolute dilation interchange then gives

`M(A_z)(s)=(1-2^(1-s))*zeta(s)/(s*zeta(s+z))`

when Re s>1, Im s>0 and Re(s+z)>1.

Now suppose Re z=0 and A_z is canonically L2. Its supported Mellin transform is analytic for Re s>1/2. The two functions `zeta(s+z)*M(A_z)(s)` and `-M(phi_1)(s)` are analytic on the connected convex tube Re s>1/2, Im s>0, Im(s+z)>0. Neither zeta pole occurs there. Their initial equality near `2+i*(max(0,-Im z)+1)` continues throughout that tube, retaining the exact numerator above.

Fix a positive critical zero rho and let s0=rho-z, with positive imaginary part. For real x decreasing to zero, the generic canonical Hilbert estimate gives `x*M(A_z)(s0+x)->0`. Differentiability of zeta gives `zeta(rho+x)/x->zeta'(rho)`, regardless of zero multiplicity. Multiplication therefore makes `zeta(rho+x)*M(A_z)(s0+x)` tend to zero. The cleared identity and continuity identify the same limit with `(1-2^(1-s0))*zeta(s0)/s0`. On Re s0=1/2, both s0 and the dyadic factor are nonzero. Thus zeta(s0)=0, proving transport.

Choose one positive critical zero using the unconditional Hardy theorem. The entire pole-removed zeta function is not locally identically zero, so analytic isolation supplies a radius r>0 with no other zero in the punctured disk at rho. Set delta=min(r,Im rho)>0. If 0<|y|<delta and A_(iy) were admitted, transport would make rho-iy a zero. This point is distinct from rho, has positive imaginary part, and has distance |y|<r, contradicting isolation. At y=0 the literal source equals the supported dyadic Haar function almost everywhere, which is canonically L2. This proves the full equivalence.

## Conjecture tested and consequence

An interpolation argument from the admitted real endpoints zero and one half requires estimates along their imaginary translates. The proposed admission of the imaginary boundary near zero is false, even pointwise at every small nonzero shift. The positive replacement is the exact isolated-admission classification and critical-zero transport law above.

This closes that interpolation boundary proposal. It does not exclude another interpolation family, prove an upper bound for real damping, or settle RH. The hard surviving target remains the complete signed natural-cutoff energy, equivalently its full weighted critical-line mixed moment, for arbitrarily small positive real damping.

## Corpus grounding

Search165 completed with inventory65036 complete and mixed compiler freshness. All20 candidate statements,20 source arguments and both ingredient steps were inspected. It supplied no literal complex PM source identity. Applicable existing inputs are the actual supported dilation/L-series APIs, `pm_mellin_L2_boundary_decay`, the Hardy critical zero, and the pole-removed zeta zero-isolation lemmas. Generic complex damping operators do not instantiate the source.

## Verification — 2026-10-04

All fifteen public exports (two definitions and thirteen theorems) are audited. Targeted `lake --old build GaloisForLFunctions.RHTower.PMPowerDampedMobiusComplexBoundary` passed, compiling the new leaf in148s and replaying existing dependencies. Mandatory `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusComplexBoundary.lean` passed with exit0 and no diagnostics. Separate /tmp `#print axioms` queries passed for every public export with only propext, Classical.choice and Quot.sound. Umbrella import appears once, generated indexes include the new declarations, and whitespace checks passed. No full or umbrella build, numerical experiment, heartbeat increase, added axiom or RH assumption.

Formal lint exits1 on twelve unrelated unreachable leaves: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving, and HTGeometry.CompactMonoidMeasureAlgebra. No finding names this leaf. No global lint pass or RH conclusion is claimed.
