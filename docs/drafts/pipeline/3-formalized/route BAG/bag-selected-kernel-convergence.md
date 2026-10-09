# BAG strong convergence of the actual selected reciprocal kernels

- **Stage:** 3-formalized

01ax. Dependency-closed paper and production Lean proof COMPLETE.
ChiCubicSelectedKernelConvergence479lines/API5 (two definitions, three
unconditional theorems). Complete scratch23076PASS; final production6711
emptyPASS. All five axiom prints in93079 report only propext,
Classical.choice, Quot.sound. The combined scratch93079 exited1 on the NEXT
physical-identity candidate, not the convergence leaf. Index88424PASS;
umbrella import once and scoped diffcheckPASS. Lint94988terminal1:
one unrelated unreachable module UnitClassInverseLBounds,362warnings;
no finding in this leaf. Global lint is not clean. No full/umbrella build,
resource-limit override, numerical experiment, subagent or added axiom.

Let K_N(a,b)=K_(N^-3/4,1/logN)(a,b,(tau/N)*a*b), tau>0. Define
F_infty=1_(1,2)*smoothAFECutoff and K_infty by the same literal reciprocal
triple integral, with F_infty replacing all three slices and c=0.
For every 0<=s<3/2, claim:
- K_infty has finite integral (1+|a|+|b|)^(2s)*|K_infty|²;
- the same weighted square of K_N-K_infty is eventually integrable;
- its full-plane integral tends to zero.
All actual Gaussian/log/window/conjugate factors remain before the limit.
There is no assumed profile, regularity budget or cancellation estimate.

1. Actual slice convergence. Its norm is at most one, by the exact cutoff
range, Gaussian norm bound and denominator 1+h log x>=1 on[1,2]. The exact
plateau eventually contains every x in(1,2); off this interval the cutoff is
zero, including endpoints. The logarithmic parameter tends to zero. This
proves pointwise F_N->F_infty.

2. Literal kernel convergence. The full triple integrand is supported in
[1,2]^3 and has norm at most one. Its reciprocal factor is <=1 there, the
physical window lies in[0,1], and the oscillation has norm one. The curvature
tends to zero. Joint measurability, an integrable fixed-cube majorant and
Fubini identify the joint integral with the original nested kernel. DCT gives
K_N->K_infty pointwise. The same majorant gives one uniform bound on all
frequencies for the eventual family and its limit; both are measurable.

3. Local energy convergence. On each fixed frequency box[-R,R]^2, the
weight and kernel difference are uniformly bounded. Finite-box DCT gives
vanishing weighted square difference there.

4. Fatou admission. Choose s<t<3/2. The audited selected global-energy
result bounds integral w^(2t)|K_N|² by C. Fatou admits K_infty at order t
with the same bound. Eventual rather than universal parameter admission is
handled by replacing N by max(N0,N), preserving the limit. No undefined
nonintegrable Bochner integral is used as a bound.

5. Uniform tails. The triangle inequality gives
 integral w^(2t)|K_N-K_infty|² <=4C.
Since w>=1, this admits order s too. Outside[-R,R]^2 with R>=1, w>=R and
 w^(2s)|difference|² <=R^(2s-2t)*w^(2t)|difference|².
The tail is <=4C*R^(2s-2t), which tends to zero. First choose R, then use
step3 on the fixed box. This proves global strong weighted convergence.

Corpus evidence: actual amplitude/cutoff/kernel definitions and selected
energy leaf; installed dominated-convergence, product integration, Fatou
and positive real-power comparison APIs. Deep search43046 (JSON retained
/tmp/bag-strong-weighted-kernel-search-01ax.json) nonpartial, all66739files
indexed; index1252959, coverage1252971=current, no errors; semantic coverage
unmeasured and background refresh incomplete. All20 candidates,20 source
arguments and the proposed ingredient set inspected. The latter concerns
discrete weighted counting norms and does not discharge this continuous
kernel problem. Direct installed-source verification supplies the needed
lintegral_liminf_le', hasFiniteIntegral_iff_ofReal and integral comparison.

Next hard obligations: exact physical limit identification, nonstationary
physical tails with enough derivatives/weights for logarithmic pullback,
fractional regularity through that pullback, Mellin line-tail transfer,
lower-growth complete arithmetic envelope, moving signed-source cancellation,
full sharp-action bridge, growing moments/cofactors and common-height return.
This is ordinary-frequency convergence, not a proof of those transfers or RH.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicSelectedKernelConvergence` | `bagCubicNormalizedSlice_selected_tendsto`, `bagCubicReciprocalKernel_selected_tendsto`, `bagCubicReciprocalKernel_selected_energy_tendsto` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
