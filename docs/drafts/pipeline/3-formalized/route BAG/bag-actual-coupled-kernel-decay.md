# BAG actual coupled reciprocal kernel decay

- **Stage:** 3-formalized

01ax. Dependency-closed paper and production Lean proof COMPLETE.

Source: ChiCubicCoupledKernelDecay723lines/API3. Final foregroundaudit44357
emptyPASS using lake --old env lean on the leaf with outputolean.
Axiom97812: allthree declarations use only propext, Classical.choice,
Quot.sound. Index18086PASS; API3 verified, umbrellaimport exactlyonce.
Lint78177terminal1: six unrelated unreachablemodules
PluckerCovarianceSquareRootPurification,VerticalProgressionCutoffSums,
VerticalProgressionFirstMomentExpansion,VerticalProgressionLatticeSums,
VerticalProgressionMollifier,HTGeometry.FrameOperatorPurity;362warnings,
noownederror. Scoped diffcheckPASS. No full/umbrella build or resource hack.

Let F=bagCubicNormalizedSlice(delta,h), delta in(0,1/2), h in[0,1],
and w=|F|+|F'|. Retain the full original windowW. Define
 K(a,b,c)=integral_RQP F(P)F(Q)conj(F(R))*W(PQ/R)/R²
                           *exp(-i*(Pb+Qa+c)/R).
Claim: oneC>0, uniform in delta,h and ALL reala,b,c, satisfies
 |K(a,b,c)| <= C integral_PQ w(P)w(Q)/
                   ((1+|a|)*(1+|b|)*(1+|Pb+Qa+c|)).
The positive majorant is integrable. This includes bothzero frequencies
and zero curveddefect. It assumes no cancellation, variation or energy bound.

Proof. For every compact smoothf, full-line integration byparts gives
 (R+ib)*integral_P exp(-ibP/R)*f(P)
 =R*integral_P exp(-ibP/R)*(f(P)+f'(P)), R nonzero.
Apply first inP and then inQ. WritingU=F+F' andW_j=W^(j)(PQ/R)/R^j,
the differentiated amplitude is exactly
 C0*W0+C1*W1+C2*W2,
 C0=U(P)U(Q),
 C1=P*U(P)F(Q)+Q*F(P)U(Q)+F(P)F(Q),
 C2=P*Q*F(P)F(Q).
The resultingR² cancels the originalR^-2. Both denominatorsR+ia,R+ib
are nonzero for realR nonzero. AtR=0 the originalintegrand and the
resolvedintegrand vanish by literal support ofF. The phasec/R is retained.

Every coefficient is continuous and supported on[1,2]^2. Every full
resolvedjet Cj(P,Q)*exp(-i*(Pb+Qa+c)/R)*conj(F(R))*W_j/
((R+ia)(R+ib)) is continuous on[1,2]^3 and zero outside. Hence it is
jointly integrable, allowing the completeR/P/Q swaps. No differentiation
under an integral or assumedFubini premise is needed.

On[1,2]^2 the three coefficient norms are bounded by1,5,4 timesw(P)w(Q).
The audited actual heightdecay theorem supplies constantsK0,K1,K2 with
 norm(integral_R exp(-iD/R)*conj(F(R))*W_j/((R+ia)(R+ib)))
 <=Kj/((1+|a|)*(1+|b|)*(1+|D|)).
UseD=Pb+Qa+c. Triangle inequality gives the stated bound with
C=K0+5K1+4K2. Off thephysicalbox the coefficients vanish. The positive
majorant is continuous with compact support; the admitted normintegral
inequality therefore pays its finalP/Q integral.

Exact original attachment: (logN)^3/N times the selected physical cone
Fourier transform at(a,b) is2pi*K(2pi*a,2pi*b,2pi*a*b/N), with
F=F_(H/N,1/logN). The nativecurvature is1/(2pi*N). All Gaussian/log,
conjugation, shrinkingcutoff and window factors remain.

Corpus basis: audited ChiCubicNormalizedFourier,
ChiCubicPhysicalAmplitudeBudgets, ChiCubicReciprocalHeightDecay,
and prior reciprocalIBP search /tmp/bag-reciprocal-ibp-search-01ax.json.
Complete scratch identified two final Fourier notation/unfolding fixes;
both corrections are included in the passed productionaudit. Private
singlefibre, doubletangent, compactFubini and exact fullkernel identities
are used by the actual uniform theorem; unused helperwrapper removed.
Public API: bagCubicReciprocalKernel,
bagCubicReciprocalKernel_coupled_decay,
bagCubicControlledCone_normalized_reciprocal_kernel.

Next: weightedCS/Tonelli and the provedU5 scalar stripenergy give actual
lowfrequency energy. Highfrequency energy, compactconvergence,
log-coordinate/Mellin tails, moving arithmetic signedtransfer, entire
sharpaction bridge, growingmoments/cofactors and commonheight recurrence
remain open. RH remains open.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicCoupledKernelDecay` | `bagCubicReciprocalKernel_coupled_decay`, `bagCubicControlledCone_normalized_reciprocal_kernel` |
| `GaloisForLFunctions.RHTower.ChiCubicNormalizedFourier` | `bagCubicControlledCone_normalized_fourier` |
| `GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets` | `bagCubicNormalizedSlice_properties`, `bagCubicNormalizedSlice_derivative_budgets`, `bagCubicNormalizedSlice_eq_actual`, `bagCubicControlledSlice_derivative_budgets` |
| `GaloisForLFunctions.RHTower.ChiCubicReciprocalHeightDecay` | `bagCubicReciprocalHeight_uniform_decay` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
