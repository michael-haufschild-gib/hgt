# BAG actual selected local Mellin energy

- **Stage:** 3-formalized

2026-10-06,01ax. Dependency-closed paper proof and Lean production closure.
ChiCubicSelectedLocalMellinEnergy227lines/API7. Complete scratch99827/log03
terminal0PASS/all7 axioms standard3; production78981/log01 emptyPASS;
all7 imported production axioms79187/log01 standard3; index14164PASS/API7;
RHTower importonce23584; scoped diffcheckPASS. Lint44890/log01 terminal1:
362warnings,10 unrelated unreachable modules, noownedfinding/globalnotclean.
Exact modules: RHTower.KontorovichLebedevTransform;
Sieve.TwistedSelbergCoefficient,Factorization,Forms,GcdLog,GcdLogForms,
RatioForms,Summability; VerticalProgressionRatioForm;
HTGeometry.CountableObservableEntropy. Logs /tmp/bag-selected-local-mellin-*01ax.log.

Define the normalized cone Schwartz function as the literal original
controlled physical cone transform multiplied by(log N)^3/N. The existing
exact physical theorem identifies it with the actual normalized oscillatory
kernel, including the physical2*pi*N prefactor and1/R reciprocal density.
Its exact Fourier transform is2*pi times the full reciprocal kernel at
(2*pi*a,2*pi*b,2*pi*a*b/N). Therefore curvature in scaled frequency variables
is tau/N with tau=1/(2*pi). Neither the height factor nor the phase is removed.

The one-dimensional nonnegative Jacobian formula proves that integrating
c*F(c*x) equals integrating F for c>0. Applying it in each coordinate proves
the exact two-dimensional scaling identity without assuming integrability.
The Fourier amplitude squared is(2*pi)^2, exactly the Jacobian factor.
Since2*pi>=1, the original physical Fourier weight is bounded by the scaled
reciprocal-kernel weight. This proves the complete physical Fourier energy
bound directly from the literal reciprocal kernel, before using admission.

Define the total selected family with the literal widthH=N^(1/4); it is zero
only outside the admissible parameter range. The relative width is exactly
H/N=N^(-3/4). The native negative-rpow limit proves admissibility eventually,
and an exact eventual theorem identifies every selected physical value with
the original normalized kernel. Existing selected reciprocal-kernel energy
at tau=1/(2*pi) supplies an admitted globally uniform bound at every order
0<=s<3/2. Nonnegative product integration and the proved real-integral
admission identify its iterated energy with the existing bound.

Apply LocalMellinSobolevTransfer at fractional ordertheta in(0,1/2), using
physical order1+theta. The result is ONE full local logarithmic Fourier
H^(1+theta) bound for the actual selected family, uniformly over all Mellin
parameters in[1,2]^2. The output is the literal compact weighted log profile;
there is no stationary-limit replacement or assumed uniform seminorm.

Still open: exterior weighted log energy, complete Mellin line tails,
lower-growth full arithmetic source envelope, moving-test cancellation,
the original full sharp-action bridge, moments/cofactors and deterministic
common-height return. RH remains unproved.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.HTGeometry.LocalMellinSobolevTransfer` | `compactLocalizedMellinSchwartz_uniform_energy` |
| `GaloisForLFunctions.RHTower.ChiCubicSelectedLocalMellinEnergy` | `bagCubicNormalizedConeSchwartz_apply`, `bagCubicNormalizedConeSchwartz_fourier`, `bagCubicSelectedNormalizedCone_eventually_apply`, `bagCubicSelectedNormalizedCone_uniform_energy`, `bagCubicSelectedNormalizedCone_uniform_local_mellin_energy` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
