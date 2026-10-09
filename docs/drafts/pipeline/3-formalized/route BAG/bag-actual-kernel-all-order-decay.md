# BAG actual reciprocal kernel all-order frequency decay

- **Stage:** 3-formalized

01ax. Dependency-closed paper and production Lean proof COMPLETE.
ChiCubicKernelFrequencyDecay315lines/API1. Complete scratch65533PASS;
finalproduction55738PASS with one informationalring suggestion, no errors
or warnings. Axiom14295standard3; index91438PASS/API1/importonce;
scoped diffcheckPASS. Lint6955terminal1: twelve unrelatedunreachablemodules
DeckPoincareMajorantUnfolding,EisensteinStarLevelCoefficient,
PluckerCovarianceObserverSubunitDefect,PluckerCovarianceSquareRootPurification,
VerticalProgressionBumpSums,VerticalProgressionCutoffSums,
VerticalProgressionFirstMoment,VerticalProgressionFirstMomentExpansion,
VerticalProgressionLatticeSums,VerticalProgressionMollifier,
VerticalProgressionResonance,HTGeometry.FrameOperatorPurity;
362warnings,noownederror. No full/umbrella build or resource-limit override.

For everypositivenaturaln, oneCn>0 bounds
 max(|a|,|b|)^n*|K_delta,h(a,b,c)| <= Cn/delta^(n-1)
for ALL admissibledelta,h and reala,b,c. K is the full actual kernel;
the defectc is arbitrary and may later equal a growingcurvaturetimesab.
This is the missing derivative-driven estimate for complementary
highfrequencyenergy, not a numerical constant improvement.

Proof. The fixed complexphysicalwindowW has smooth compact support,
so everyderivative has a globaluniformboundBj. For|k|<=2, thej-th
 derivative ofW(kx) has norm<=2^j*Bj. Leibniz and the audited actual
slice derivative budgets give
 integral|deriv^n(F_delta,h(x)*W(kx))|<=Cn/delta^(n-1).
All derivatives are integrable byactualcompact support. Fori<=n,
delta^(n-1)<=delta^(i-1) because0<delta<1; this pays everyLeibnizterm
without an assumeduniform highSchwartz bound.

The existing native Fourier/iteratedderivative theorem gives
 |integral F(x)W(kx)exp(-i*xi*x)|<=Cn/delta^(n-1)/|xi|^n.
In the actualP integral, k=Q/R andxi=b/R. OnQ,R in[1,2], |k|<=2 and
R^n<=2^n. Pull the literal constantphase factors outside theP integral;
allGaussian/log/window factors stay. IntegrateQ against|F(Q)| andR
against|F(R)|/R². The latter reciprocal factor is<=1 on theactualsupport.
Uniformactualmass pays bothremaining integrals, givingtheb-frequency
bound. Atb=0 its multiplied form iszero because n>0.

For eachfixedR, the fullP/Q integrand is continuous with compact support
[1,2]^2, includingR=0 under totalfielddivision. Fubini plus algebra proves
exactK(a,b,c)=K(b,a,c). This supplies thea bound. Split bywhichfrequency
has largermodulus to obtaintheclaimedmax-frequencydecay.

Corpus: actualamplitude budgets and fullkernel identity; deepsearch12393
found HTGeometry.norm_integral_mul_cexp_le_of_iteratedDeriv and its
compactderivativeintegrability helper in FourierIteratedDerivDecay.
Existingmathlib iteratedDeriv_mul anditeratedDeriv_comp_const_smul pay
the actualproduct derivativebudget. No analytic/cancellation premise,
addedaxiom or numericalexperiment.

Next: fixed sufficientlyhighorder, a separatedintegrable frequency
majorant andtheactualdelta=N^-3/4 substitution pay thecomplementarytail.
Combine withtheauditedactualstripenergy to establishglobalmoving-family
regularity, then compactconvergence, log/Mellintails and movingsigned
arithmetictransfer. Fullsharpaction/growingmoments/commonheightrecurrence
and RH remain open.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicKernelFrequencyDecay` | `bagCubicReciprocalKernel_frequency_decay` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
