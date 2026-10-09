# BAG selected global reciprocal kernel energy

- **Stage:** 3-formalized

01ax. Dependency-closed paper and production Lean proof COMPLETE.
ChiCubicSelectedKernelEnergy248lines/API2. Complete scratch73079emptyPASS;
final production13417emptyPASS. Both axiom prints in scratch42001 report
only propext, Classical.choice, Quot.sound; that combined scratch exited1
because the NEXT convergence proof had elaboration errors, not this leaf.
Index36595PASS, umbrella import once, scoped diffcheckPASS.
Lint64836terminal1:14 unrelated unreachable modules and362warnings:
DeckPoincareMajorantUnfolding, EisensteinStarLevelCoefficient,
KuznetsovEisensteinCoefficient, PluckerCovarianceObserverSubunitDefect,
PluckerCovarianceSquareRootPurification, VerticalProgressionBumpSums,
VerticalProgressionCutoffSums, VerticalProgressionFirstMoment,
VerticalProgressionFirstMomentExpansion, VerticalProgressionLatticeSums,
VerticalProgressionMollifier, VerticalProgressionResonance,
VerticalProgressionResonantMass, HTGeometry.FrameOperatorPurity.
All errors inspected; no finding in this leaf. Global lint is not clean.
No full/umbrella build, subagent, numerical experiment or resource hack.

For every0<=s<3/2 and everyfixedtau>0, the LITERAL selectedfamily
 K_N(a,b)=K_(N^-3/4,1/logN)(a,b,(tau/N)*a*b)
has, eventuallyN, an admitted globallyuniformweightedenergy
 integral_R² (1+|a|+|b|)^(2s)*|K_N(a,b)|² <= C_(s,tau).
The original physicalFourier normalization corresponds tau=1/(2pi),
followed by the alreadyprovedfrequencydilation(a,b)->(2pia,2pib).
Allactual Gaussian/log/window/conjugation/cutoff factors remain.

First prove the actualtail theorem, uniformALLstructuraldelta,h,realλ,
andR>=1:
 integral_{max(|a|,|b|)>=R} (1+|a|+|b|)^(2s)*|K(a,b,lambdaab)|²
 <=Cs/delta^22 * R^(2s-20),
with fullintegrability. The audited allorderfrequencytheorem atorder12
boundsM^12|K| byC/delta^11, M=max(|a|,|b|). OnM>=R>=1,
1+|a|+|b|<=3M and(1+|a|)^2(1+|b|)^2<=16M^4.
Consequentlythewhole weightednormsquare is bounded by
 Cs/delta^22 * R^(2s-20)/((1+|a|)^2*(1+|b|)^2).
The negativeexponent2s-20 allows replacingM byR. The separatedmajorant
is globallyintegrable, proving bothadmission andthetailbound.
Kernelmeasurability is paid fromtheliteraltripleintegral.

Forselecteddelta=N^-3/4,h=1/logN,λ=tau/N, takeR=N/(4tau).
Allparameters areeventuallyadmissible. The complementof theauditedstrip
|lambda*a|<=1/4 lies inthetailmaxfreq>=R. Exactpositive-rpow algebra gives
 delta^-22*R^(2s-20)=(4tau)^(20-2s)*N^(2s-7/2).
The lastpoweris<=1 forN>=1, since s<3/2. Combine theuniformstripbound
and tailboundby admittedcomplementaryintegrals. No boundaryassumption,
stationarysubstitution, highSchwartzbudget or growingintegralexchange
is assumed.

Corpus: ChiCubicCoupledStripEnergy,ChiCubicKernelFrequencyDecay,
ChiPrimeGaussianCubicSharpEdges.edge_quarter_small mechanism,
ChiCubicPhysicalAmplitudeBudgets actualparameter construction;
mathlibintegrable_one_add_norm, powercomparison, parameterintegral
measurability andcomplementaryintegral APIs. Scale-searchmetadata and
exactargumentaudit inparentP1 bag-actual-reciprocal-kernel-energy.

The full selected global energy theorem has passed its production Lean audit.
Hard nextobligations: compactfrequencyconvergence andstronglowerHs
convergence, physicallog-coordinate tails andMellinline tails,
lowergrowtharithmetic envelope, movingsignedtransfer, entireoriginal
sharpaction bridge, growingmoments/cofactors and deterministiccommonheight
selfreturn. RH remainsopen.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicCoupledStripEnergy` | `bagCubicReciprocalKernel_uniform_strip_energy` |
| `GaloisForLFunctions.RHTower.ChiCubicKernelFrequencyDecay` | `bagCubicReciprocalKernel_frequency_decay` |
| `GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets` | `bagCubicNormalizedSlice_properties`, `bagCubicNormalizedSlice_derivative_budgets`, `bagCubicNormalizedSlice_eq_actual`, `bagCubicControlledSlice_derivative_budgets` |
| `GaloisForLFunctions.RHTower.ChiCubicSelectedKernelEnergy` | `bagCubicReciprocalKernel_tail_energy`, `bagCubicReciprocalKernel_selected_uniform_energy` |
| `GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicSharpEdges` | `primeGaussianCubicMainEntry_norm_le`, `primeProfileBand_card_le_twice`, `exists_primeGaussianCubic_smooth_band_comparison`, `exists_primeGaussianCubic_smooth_band_negligible_error`, `primeGaussianCubic_controlled_cutoff_negligible_error` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
