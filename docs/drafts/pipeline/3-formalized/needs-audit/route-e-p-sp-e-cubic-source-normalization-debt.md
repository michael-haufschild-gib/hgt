# Route E/P/SP-E cubic source-normalization debt

- **ID:** `route-e-p-sp-e-cubic-source-normalization-debt`
- **Stage:** 3-formalized / needs audit
- **Type:** `[THEOREM] [NO-GO CLOSURE] [EXACT POSITIVE SURVIVOR]`
- **Parent:**
  `route-e-p-sp-e-cubic-hellinger-plucker-load-bridge.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RouteEPCubicSourceNormalizationDebt.lean`

## Conjecture attacked

Pair every primitive cell (pe) with its twice depth-squared partner (D^2 pe).  Their rates are
(lambda,4 lambda), so the unit-diagonal cubic Cauchy Gram has Pluecker defect

\[
  \Delta_4=\frac{11529}{15625}
\]

and normalized quadratic ratio (Delta_4/4=11529/62500>1/6).  Conjecture: these canonical blocks
can be assembled cofinally while retaining Route P's coefficient-faithful prime--Gamma source
weights.

## Exact killing theorem

Corpus already proves one coefficient-faithful depth-square transport law

\[
  w(Dpe)g(pe)^2=\frac{w(pe)}8,
\]

where (w) is native cubic prime--Gamma diagonal and (g) is modular amplitude gain.  Composition is
not unitary: with (G_4(pe)=g(Dpe)g(pe)),

\[
  w(D^2pe)G_4(pe)^2=\frac{w(pe)}{64}.                 \tag{1}
\]

The same identity holds for literal base-Cauchy diagonal weight
(w_B=(216/115)w).  A two-column Gram with diagonal weights (x,y) and normalized Pluecker defect
(Delta) has degree-two ratio

\[
  \mathcal R(x,y;\Delta)=\frac{xy\Delta}{(x+y)^2}.   \tag{2}
\]

Putting (x=w_B(pe)), (y=x/64), and (Delta=Delta_4) gives the exact source-faithful ratio

\[
  \mathcal R_{\rm sf}
   =\frac{64\Delta_4}{65^2}
   =\frac{737856}{66015625}
   <\frac{13}{98}<\frac16.                           \tag{3}
\]

Therefore unit-diagonal normalization was doing essential work.  Literal coefficient-faithful
fourth-depth blocks do not clear even the uniform-Boolean ceiling, much less theta's (1/6) floor.
This kills canonical block repetition as a source-faithful SP-E assembly.

## Strongest positive survivor

Obstruction exposes exact normalization debt rather than only failure.  If transported partner is
given one additional nonnegative amplitude (c), diagonal balance is equivalent to

\[
  \frac{x}{64}c^2=x
  \quad\Longleftrightarrow\quad c^2=64
  \quad\Longleftrightarrow\quad c=8.                 \tag{4}
\]

Thus required amplitude correction is uniquely (8).  Coefficient-faithful pair trace is
(65x/64); balanced trace is (2x).  Exact added trace is

\[
  2x-\frac{65x}{64}=\frac{63x}{64}.                  \tag{5}
\]

Equations (4)--(5) specify missing completion quantitatively: successful Gamma/co-Poisson/Stokes
transport must create amplitude (8) while paying or redistributing trace debt (63x/64).  Treating
unit normalization as projectively harmless is impossible because Route P's global `<2` budget
is diagonal-energy sensitive.

## Higher principle

Projective separation and source capacity live in different geometries.  Rate ratio controls
normalized Cauchy angle, but arithmetic depth changes source Radon--Nikodym mass.  A local
Pluecker producer is globally usable only when transport is simultaneously projectively
separating and measure-compatible.  Repeated depth-square amplifies rate gap while exponentially
depleting cubic carrier energy; these are two faces of same modular cocycle.  Missing completed
Gamma correction is therefore a Radon--Nikodym compensation law, not another stability or
combinatorial-order argument.

## Conjecture loop audit

1. **Conjecture:** rate-four canonical pair gives source-native floor-clearing block.
   **Failed:** unit normalization erased exact (1/64) transported diagonal.
2. **Pivot:** retain coefficient-faithful diagonal and recompute determinant ratio.
   **Proved:** exact ratio (3), strictly below both relevant thresholds.
3. **Conjecture:** arbitrary scalar rebalancing might be a harmless degree of freedom.
   **Failed:** balance forces unique nonnegative amplitude (8) and positive trace debt (5).
4. **Positive pivot:** search completed four-leg/Gamma/Stokes corpus for an intrinsic (8)-gain
   channel whose global trace contribution is offset by an exact negative/cross-channel budget.

## Open core exposed

1. Find source-derived completed correction with squared gain (64) on fourth-depth channel.
2. Prove its cross-channel or Stokes contribution pays exact trace debt (63w/64) inside Route P's
   global `<2` budget; arbitrary rescaling is disallowed.
3. Only then assemble cofinal blocks and compare aggregate degree-two ratio with theta coefficient.
4. Extend corrected transport from two-minors to all principal minors and determinant limit.

## Novelty audit

Targeted corpus search found one-step (1/8) depth-square Radon--Nikodym law and unit-diagonal
rate-four Pluecker ratio separately.  It found no two-step (1/64) source-faithful Gram-ratio no-go,
unique amplitude-eight correction, or exact trace debt (63/64).  Result is internal cross-module
deduction; no external priority claim is made.

## Formal status

Lean proves unconditionally, without added axioms:

- `routePPrimitiveFourthDepth_cubicWeight_modularGain_sq`;
- `routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq`;
- `routePPrimitiveFourthDepth_cubicPluckerDefect`;
- `routeEPCubicSourceFaithfulFourthDepthPairGramRatio_eq`;
- `routeEPCubicSourceFaithfulFourthDepthPairGramRatio_lt_thirteen_div_ninetyEight`;
- `routeEPCubicSourceFaithfulFourthDepthPairGramRatio_lt_one_div_six`;
- `routeEPCubic_fourthDepth_rebalance_iff`;
- `routeEPCubic_fourthDepth_rebalance_eq_eight`;
- `routePPrimitiveFourthDepth_baseCauchy_rebalance_iff`;
- `routePPrimitiveFourthDepth_baseCauchy_rebalance_eq_eight`;
- `routePPrimitiveFourthDepth_sourceFaithful_pairTrace`;
- `routeEPCubic_fourthDepth_rebalancingTraceDebt`.

Verification uses direct `lake env lean` and target-only module build.  Umbrella import is wired;
no umbrella build was run.
