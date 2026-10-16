# Contribution 015: strong BV theta parameter calculus

Status: **FORMALIZED; 15/100 contributions completed.**

## Structural result

The literal charged theta parametrix is strongly differentiable in its
original whole-line and closed-interval BV norms, at every complex parameter.
Its actual difference quotient converges to the literal first parameter jet
in point value plus total variation. This closes the parameter-admission gap
left by separate BV admission of each jet.

The same family is entire in the complete complex arithmetic difference
graph. Its Taylor series converges there at every center and every complex
parameter. The original full Weil energies of its real and imaginary parts
converge through this infinite synthesis and differentiate along every affine
complex parameter direction. Gamma, every prime power, negative mass, both
polar moments and the actual cut charge are retained.

At every actual Xi support point, jets below full multiplicity are independent
of the cut in the arithmetic graph. At the multiplicity order, the map from
cut to graph jet is injective. L2 completion does not erase the first surviving
native Meyer charge.

This is one contribution: its estimates, complex graph companion and scalar
projection tools are ingredients, not additional counted contributions.

## New mechanism and dependency-closed proof

For parameter center z and cut a, let L(x)=V(-z,-x), R(x)=V(z,x), and
S=L(a)+R(a), using RN's native variation budgets. Set W(x)=L(x) below a and
W(x)=2S-R(x) at or above a. W is monotone and lies between 0 and 2S.

RN's parameter-circle bounds control same-side increments by W(y)-W(x).
Across the cut, the common trace -1 cancels; the two remaining tails cost
L(x)+R(y), at most 2S-L(x)-R(y)=W(y)-W(x). The maximum principle preserves
these bounds inside the disk. This single scalar BV control is the missing
uniform ingredient; the actual jump is included rather than discarded.

Two Cauchy derivative estimates and two complex mean-value applications give
an actual slope remainder bounded by 8 B |h| for |h|<1/4. Apply this to a
spatial increment with B=W(y)-W(x). Every increasing partition telescopes,
so the whole remainder variation is at most 8 |h| (2S). Point-value error
vanishes simultaneously. The original source BV difference quotient therefore
converges strongly. The compact remainder has zero endpoint traces and the
AC branch limits supply one-sided continuity. Closing the interval preserves
variation; the monotone onto quantile map preserves its interior variation
exactly. Thus the same strong derivative exists in the original compact BV
norm, even at charged parameters.

CHMD's unconditional BV theorem admits W's full difference in the actual
edge-L2 measure; bounded source values have a constant mass-L2 majorant.
The corpus Cauchy-to-L2 theorem supplies strong holomorphy of both coordinates.
Closedness of the literal endpoint-difference graph keeps derivatives inside
that complete graph. Continuous source projection identifies every jet with
its original representative. Entire Banach-valued Taylor synthesis then
converges globally in the graph. Continuous real and imaginary projections
into the original real CHMD graph retain its full signed Weil form.

HF/RN full charge multiplicity makes every lower jet native and cut independent.
If terminal graph jets at two cuts were equal, their representatives would
agree almost everywhere on the interval between cuts. The actual mass
measure dominates volume, and this interval has positive measure. On it the
branches differ by the nonzero terminal charge, a contradiction.

## Corpus inputs

- RN: `parameterVariationBudget_antitone`,
  `flatQuotient_increment_parameter_circle`,
  `flatQuotient_add_one_parameter_circle`, admitted AC quantile branches.
- CHMD: `bv_memLp_difference`, original complete difference graph and
  `sourceWeilEnergy_bvLift`, with both polar moments retained.
- Actual analytic sections: `Family.hasDerivAt_section`,
  `Family.coe_iteratedDeriv_section` from `AnalyticDominatedL2Derivatives`.
- HF/RN: `cutParameterJet_eq_native`,
  `terminalParameterJet_jump_ne_zero`, full original Xi charge multiplicity.

## Formal leaves and main declarations

All paths are beneath `formal/GaloisForLFunctions/`.

- `HTGeometry/CauchySlopeRemainder.lean`: Cauchy remainder proportional to the
  original scalar majorant.
- `RHTower/PaperThetaUniformCutControl.lean`: bounded monotone control for
  both literal tails and their actual cross-cut increment on a parameter disk.
- `RHTower/PaperThetaBVParameterDifferentiation.lean`:
  `tendsto_cutParameterSlopeRemainder_globalBV`.
- `RHTower/PaperThetaCompactBVParameter.lean`:
  `eVariationOn_cutQuantileSlopeRemainder`,
  `tendsto_cutQuantileSlopeRemainder_BV`.
- `RHTower/CHMDComplexJumpGraph.lean`: complete complex literal difference
  graph; ambient derivatives stay in that graph.
- `RHTower/PaperThetaArithmeticHolomorphy.lean`:
  `differentiable_cutArithmeticSection`,
  `cutArithmeticSection_jet_source`, `cutArithmeticSection_jet_edge`,
  `hasSum_cutArithmeticSection_taylor`.
- `RHTower/CHMDComplexWeilForm.lean`: continuous scalar projections into the
  original real graph; exact full real/imaginary BV expression.
- `RHTower/PaperThetaArithmeticWeilCalculus.lean`:
  `tendsto_cutArithmeticTaylorPartial_fullWeil`,
  `hasDerivAt_cutArithmetic_fullWeil`,
  `cutArithmeticSection_native_jet_cut_independent`,
  `cutArithmeticSection_terminal_jet_cut_injective`.

## Conjecture loop

Original-Frechet density was investigated first. Existing Hilbert density
supplies no original-source approximation theorem; no spectral-synthesis
proof was obtained. This lead is deferred, not declared impossible.

Whole-quotient Euler inversion was investigated next. Finite Xi-jet inverses
do not discharge surjectivity of periodized actual Poisson boundaries.
Pointwise division therefore did not yield a source inverse. This lead is
also deferred, with no no-go or contribution claimed.

Uniform two-tail variation control succeeded. It first gave complete
arithmetic graph holomorphy. A further conjecture strengthened this to the
literal source BV derivative and exact compact variation transport; both
are now proved. The exact terminal cut injectivity was also extracted and
formalized, ensuring the stronger topology does not erase the obstruction.

## Audit

- Eight direct foreground leaf audits passed, one owned Lean process at a
  time, using `lake --old env lean -o <leaf.olean> <leaf.lean>` from `formal/`.
- Final API audit passed. Main declaration types have no unproved admission,
  positivity, zero-location or simplicity premise.
- Expanded `#print axioms` audit passed for all **66 public declarations**.
  Only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.
- Eight imports wired exactly once in their theorem-area umbrellas; all
  eight direct artifacts are newer than their sources. No umbrella/full build.
- No heartbeat raises, numerical experiments, `sorry`, `admit`, unsafe or
  opaque declarations introduced.
- Global `scripts/formal_tools.py lint` reports eight unrelated missing
  umbrella imports: `RHTower.CHMDPrimeRowBound`,
  `RHTower.EvenSectorHermitianScalarization`,
  `HTGeometry.CanonicalProductSubquadraticType`,
  `HTGeometry.EvenEntireAxisType`, `HTGeometry.EvenEntireCompactSource`,
  `HTGeometry.EvenHermitianAxisMultiplicity`,
  `HTGeometry.EvenHermitianCanonicalFactor`,
  `HTGeometry.EvenHermitianSpectralFactor`.
  None belongs to this contribution. Unrelated work is preserved.
- Sixteen owned scratch files removed; none remain. Final metadata check
  confirms all eight artifacts current and all eight imports unique. No
  owned Lean process remains. No commits or pushes made.

## Scope

Strong BV difference-quotient convergence is proved directly on original
functions; the BV carrier has not been packaged as a new Banach-space type.
Global Taylor synthesis is proved in the complete arithmetic graph norm.
Arbitrary infinite native Xi-packet realization, directed nonlinear current
orientation and the missing signed positivity remain open. No direct
spectral formula for discontinuous complex BV profiles is claimed beyond
the established full-form extension. RH is not proved.
