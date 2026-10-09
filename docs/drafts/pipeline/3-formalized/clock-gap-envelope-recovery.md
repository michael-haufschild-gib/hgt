# Exact weighted Lipschitz recovery by the least envelope

- **ID:** clock-gap-envelope-recovery
- **Stage:** 3-formalized
- **Type:** CORPUS BRIDGE / exact feasible-value classification
- **Source:** `ConformalClockContinuousMatrixRecovery`; corpus tent construction in
  `RHTower/TentMellinFactor.lean`.
- **Statement:** For an arbitrary pseudometric space X, anchor p, nonnegative weight
  g:X→NNReal, constants L,epsilon:NNReal, and real a, an L-Lipschitz u with u(p)=a
  and g(x)|u(x)|<=epsilon everywhere exists iff
  g(x) max(0,|a|-L dist(x,p))<=epsilon everywhere.

## Paper proof [PROVED HERE]

Every admissible u satisfies |u(x)|>=|a|-L dist(x,p) by the reverse triangle
inequality and its Lipschitz bound. Absolute values are nonnegative, so the positive
part E(x)=max(0,|a|-L dist(x,p)) is a pointwise lower bound. Multiplication by the
nonnegative weight proves necessity.

The distance function is 1-Lipschitz. Thus E is L-Lipschitz, E(p)=|a|, and E>=0.
Use u=E for a>=0 and u=-E for a<0. This single function realizes u(p)=a and
|u(x)|=E(x) simultaneously at every point. It proves sufficiency for every weight;
no continuity, nonvanishing, or attained supremum is required of the weight.
This is stronger than a pointwise numerical bound: the least absolute envelope
is realized by one globally compatible function, even on arbitrary metric domains.

An equivalent, division-free formulation is
g(x)|a|<=epsilon+g(x)L dist(x,p) for every x. Necessity follows by dropping the
positive part to its underlying affine expression. Conversely, if that expression
is negative the envelope is zero; otherwise the affine inequality is precisely
the weighted envelope inequality. In particular, points with g(x)=0 impose no
false division constraint. This eliminates the unknown field from feasibility.

For X=R, p=0, g(x)=|x|, the condition reduces exactly to a^2<=4 L epsilon.
If L>0, evaluating the envelope at t=|a|/(2L) gives necessity. Conversely,
4L t(|a|-Lt)<=a^2 follows from (|a|-2Lt)^2>=0; the positive part vanishes
when |a|-Lt<=0. If L=0 and a is nonzero, choose
t=(epsilon+1)/|a| to contradict t|a|<=epsilon. If a=0 the zero function works.
These arguments cover L=0, epsilon=0, and both signs of a without extra assumptions.

## Corpus audit

`research "Lipschitz distance cone weighted recovery" --no-refresh --json` returned
weight multiplication, factor-through Lipschitz bounds, and unrelated energy recovery.
No exact feasible-value classification appeared. Results are source-only, not a
completeness certificate; partial=false, older-generation coverage, semantic coverage
unmeasured. Only Lean source entries were read. The corpus tent construction uses
min/max-preserved Lipschitz constants; it does not classify arbitrary weighted data.
The local Lean dependencies supply the metric and Lipschitz APIs. No external search.

## Plan

- [x] Corpus overlap search and dependency-closed paper proof.
- [x] Formalize least envelope and unconditional weighted feasibility iff.
- [x] Formalize sharp linear-gap iff including zero endpoints.
- [x] Direct leaf, axioms, umbrella, index and lint audits.

## Final audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ClockGapEnvelopeRecovery.lean` contains nine
theorems and two definitions. The final direct command
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ClockGapEnvelopeRecovery.olean GaloisForLFunctions/HTGeometry/ClockGapEnvelopeRecovery.lean`
passed with no diagnostics. Imported `#print axioms` for all eleven declarations
reported only `propext`, `Classical.choice`, and `Quot.sound`. No added premise,
proof debt, heartbeat increase, numerical experiment, or full build was used.
Lipschitz and noise conditions are classified inside existential iff statements;
they are not assumed source estimates. The minimal-envelope theorem states an
attained minimum without an unproved helper premise.

Umbrella integration contains exactly one import; index regeneration passed, with
all eleven generated API rows present. Whitespace checks passed. The authoritative
global lint exited 1 on five unrelated unreachable HTGeometry modules:
`ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`.
No owned-leaf error was reported; unrelated files were left untouched.

Serena symbol retrieval rejected this new Lean leaf as an ignored path; the small
proof edit used a targeted patch instead. Owned `/tmp/hgt-clock-*` scratch is
cleaned after the audit; proof status and open work are retained on these cards.

The general power-order closed constant is now formalized in
`clock-collision-sharp-stability.md`. No external-novelty or RH claim.
