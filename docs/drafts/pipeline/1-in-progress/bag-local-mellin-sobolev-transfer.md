# BAG local Mellin H^(1+theta) transfer

2026-10-06,01ax. Hard local assembly after actual compact Mellin coefficient
construction. Target: one constant independent of sigma in[1,2]^2 and
Schwartz f bounds the full weighted Fourier energy of the exact localized
logarithmic profile by the same physical Fourier H^(1+theta) energy,
for0<theta<1. BAG's actual physical energy supplies the range theta<1/2.
No input energy bound or uniform Schwartz seminorm is assumed.

Corpus-based proof components now available:
- LocalLogFractionalEnergy: full scalar and planar nonnegative chart estimate.
- FractionalCompactMultiplier: joint-parameter uniform admitted energy.
- CompactMellinLocalization (production/audit closed): actual compact weighted coefficients,
  both first Euler coefficients, fixed positive support, uniform mass and
  fractional bounds, exact first derivative and exact Schwartz realization.
- ChiCubicReciprocalFourier: exact measure-preserving E-to-real-pair coordinates,
  using volume_preserving_finTwoArrow and PiLp.volume_preserving_ofLp.
- Native SchwartzSpace/Fourier: fourier_lineDerivOp_eq, with the literal
  2*pi*I times directional coordinate multiplier.
- DirectionalGagliardoFourier: strictly positive admitted fractional constant.
Search10622 /tmp/bag-local-mellin-sobolev-transfer-search-01ax.json completed.
Partial due to reranking deadline; 66825/66825 inventoried/indexed, no inventory
errors; index1256000, coverage1256019=current, semantic coverage unmeasured,
refresh incomplete (background indexer). All20 candidates/source arguments
and ingredient set inspected. Native Schwartz directional Fourier law and
own chart/multiplier mechanisms apply; unrelated localization hits do not
close the required full estimate. Scratch83562/log01 tests the Euclidean
coordinate/Tonelli assembly; no assumed missing analytic budgets.

Proof plan. Convert the planar chart estimate to either Euclidean coordinate
axis through the measure-preserving coordinate equivalence and nonnegative
Tonelli. For a coefficient-weighted input, combine that chart bound with
actual coefficient fractional energy and mass. Apply the same construction
to each of the TWO terms in the exact first Euler derivative. The squared
sum costs at most twice each squared difference; physical first derivatives
remain literal Schwartz derivatives. Native Fourier differentiation turns
the corresponding input energy into physical spectral moments of order
2+2*theta. Use the positive directional Gagliardo constant to recover the
same moment for the output Fourier transform. A finite-coordinate power
inequality bounds the full two-dimensional weight by mass plus the two
DIAGONAL directional moments. No mixed-jet product estimate is used or needed.

Still separate: attach the actual selected normalized BAG family and its
proved exterior tails, derive Mellin line tails against the complete source,
prove the lower-growth arithmetic envelope and moving-test signed cancellation,
then the full sharp-action bridge/growing moments/common-height return.
RH remains open; a local operator estimate is not the endgame.

2026-10-06 01ax Euclidean chart helper audit62495/log02 emptyPASS.
Actual coefficient product support and uniform log fractional bounds, the
exact two Euler terms, double-Jacobian mass transfer, Fourier derivative
norm, full-weight/axial-moment comparisons and positive Gagliardo inversion
are now assembled in a complete candidate. Scratch99577/log06 running;
/tmp/bag-local-mellin-sobolev-transfer-01ax.lean is source of truth. P2 paper
proof written; no production closure yet. Earlier failures were coordinate
swap transparency, typed continuity/measurability, integral calc parsing,
Schwartz derivative coercions, scoped infinity ambiguity and numeral
normalization; no missing hypotheses or resource increases were inserted.
Next attachment search74506 /tmp/bag-selected-local-mellin-energy-search-01ax.json
is running. Exact physical Fourier expression is2*pi times reciprocal kernel
at(2*pi*a,2*pi*b,2*pi*a*b/N), hence the source curvature parameter is
1/(2*pi). The physical profile remains the literal normalized cone Schwartz
function; no stationary-limit replacement has been made.

Next mechanism to test after actual-family attachment: the corpus already
proves strong weighted physical Fourier convergence of the selected kernels.
A uniform bounded local log operator therefore transfers Cauchy control of
physical differences at fixed Mellin parameter. Parameter variation then
requires an actual operator-continuity estimate, obtainable in principle
from the same jointly compact smooth coefficients and their parameter
jets; it is NOT supplied by a bare uniform bound. Coupled with the proved
physical exterior decay this could give moving logarithmic profiles a
strong weighted limit without identifying a stationary physical profile
first. A source bound in the matching weighted dual space would then turn
fixed-test cancellation into moving-test cancellation by approximation.
This is a conjectured proof mechanism, not a completed transfer: exact
Fourier scaling, parameter continuity, exterior log energy, and the full
source dual bound all remain to prove. No source-envelope premise is added.

2026-10-06 01ax full local Mellin H^(1+theta) transfer CLOSED.
LocalMellinSobolevTransfer630/API1: scratch81394/log08PASS, production14804
emptyPASS, imported axioms61350standard3, index6054PASS/API1/importonce16686,
scoped diffcheckPASS. Lint49164terminal1:362warnings,10 unrelated unreachable;
exactnames P2/P3 bag-local-mellin-sobolev-transfer, noownedfinding/globalnotclean.
The actual compact log operator is bounded uniformly over EVERYsigma in[1,2]^2
for every0<theta<1 and Schwartz input, in the FULL planar Fourier weight.
It derives admission and pays both Euler terms/Jacobians without a uniform
high-Schwartz premise. Next P1 bag-selected-local-mellin-energy attaches
literal normalized physical cone profiles with curvaturetau=1/(2*pi), then
exterior log energy/Mellin tails remain. RH and BAG endgame remain unproved.

2026-10-06 01ax actual selected local Mellin energy CLOSED.
ChiCubicSelectedLocalMellinEnergy227/API7: scratch99827/log03PASS/all7standard3;
production78981emptyPASS; imported all7axioms79187standard3; index14164PASS,
RHTower importonce23584/scoped diffcheckPASS. Lint44890terminal1:362warnings,
10 unrelated unreachable, exactnames P2/P3 bag-selected-local-mellin-energy;
noownedfinding/globalnotclean. Literal N^(1/4) family has uniform global
physical H^s energy0<=s<3/2 and actual compact Mellin H^(1+theta) energy
0<theta<1/2, uniformly allsigma in[1,2]^2. Exact2*pi scaling/curvaturetau=1/(2*pi)
and double Jacobian cancellation are proved. Actual physical identity retained.
Next P1 bag-exterior-logarithmic-energy: pure physical jet -> weighted log
mass/second derivatives -> full exterior H^2 energy. RH/endgame remain open.
