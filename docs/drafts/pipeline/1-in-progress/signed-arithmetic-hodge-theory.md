# Signed arithmetic Hodge theory with source-compatible renormalization

## Objective

Develop source-faithful signed block, residual and renormalization estimates on the actual Weil
source. Complete signed complement, growing modal complement and critical-energy upper control
are research endpoints; no positive interface may assume them.

## Objects

Actual real Weil tests and their source-graph completion; proved positive arithmetic sections
and Weil projections; full mixed pairing and both poles; Ramanujan prime modes; canonical critical
source energy. Programme: formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/.

## First research question

Determine the exact optimal energy after correction by an arithmetic positive section.
Extract quantitative distance, mixed-charge and nested-removal laws. Instantiate them on the
actual unbounded fixed-log-cell carrier, preserving its residual radical.

## Method and proof obligations

Search the existing corpus for variational and nested projection results. Read exact source
statements. Prove only genuinely missing statements with all arithmetic inputs supplied.
Formalize each dependency-closed proof directly; audit using foreground Lean and #print axioms.
Do not turn residual positivity, growing-source bounds or critical-energy upper estimates into
assumptions.

## Research record

Foundational exposition: programme README.md.
Working evidence and continuation state: logs/signed-arithmetic-hodge-research.log.
No proof is classified as complete until formalized.

## Source-compatible scaling question

Determine how exact Weil translation isometry interacts with the complete source graph norm.
The source mass weight is cosh(u/2)/Phi(u), so compact-source translations may retain their
Weil value while their graph size diverges. Seek a quantitative escape theorem for every
nonzero compact test, with exact pole scaling and a positive aperture-dependent comparison.
This tests whether dyadic coarse renormalization can use a single uniform graph topology.
No blanket claim of unboundedness of each fixed translation is made without proof.

## Scalar renormalization question

For a nonzero compact source f, combine full-Weil translation invariance and
all-rate source-graph escape. Seek a bound, uniform in every scalar amplitude a,

c exp(B |t|) |W(a tau_t f)| <= |W(f)| ||a tau_t f||_graph^2.

This measures the exact loss of signed energy under any graph-bounded scalar
renormalization, rather than only ruling out fixed exponential amplitudes.
A positive replacement uses two-sided comparisons on explicitly bounded source
windows and bounded translation ranges. It does not assert a global bounded
action of every fixed translation on the complete graph.

## Completed aperture transport target

Use the existing CHMD apertureGraphCore and apertureGraphCompletion. The proved
bounded-window estimate should extend literal compact-source translation to a
bounded linear map from the completed aperture a into the completed aperture
 a+|t|. On smooth representatives the map must be the original translated test;
on the completion it must preserve the full mixed Weil form and transport both
pole coordinates by their exact exponential factors. Constants remain dependent
on the source aperture and translation range.

Do not identify the signed-source radical with the full Weil radical. The
CHMDQuotientWeilForm two-pole classification remains part of the source data.
