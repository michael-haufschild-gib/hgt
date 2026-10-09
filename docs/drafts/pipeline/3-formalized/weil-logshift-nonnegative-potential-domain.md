# Nonnegative coefficients discharge potential convergence

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Claim and plan

The unrestricted convergence-free criterion failed through a rapidly growing
negative coefficient tail. Test its natural positive-domain replacement:
assume lam(n)>=0 for n>=2 and summable normalized excess.

1. Prove a pointwise normalized-deviation bound by max(log n,total excess).
2. Derive signed-potential convergence at every real shift without positivity.
3. Remove the explicit convergence premise from the potential characterization
   on this coefficient domain.
4. Classify nonnegative minorants: the integer-log potential inequalities hold
   exactly when lam(n)=vonMangoldt(n) for every n>=2.
5. Compile, audit every public theorem, wire/index, lint, clean owned scratch.

## Dependency-closed paper proof

Let a(n) be normalized deviation and E the sum of excess e(n)=max(a(n),0).
Nonnegative summability gives a(n)<=e(n)<=E.

For n>=2, sqrt(n)>=1, vonMangoldt(n)<=log n, and lam(n)>=0. Therefore

`a(n)=(lam(n)-vonMangoldt(n))/sqrt(n)>=-log n`.

For n<2, a(n)=0 by its guard, so the same inequality holds. Hence
`|a(n)|<=max(log n,E)<=2 log n+E`, with E>=0 and a(0)=0.

The existing `summable_potential_term`, using the corpus's exponential kernel
decay, now gives convergence at every real shift. This uses neither full Weil
positivity nor asymptotic panel positivity. Insert these convergence facts into
`weilLogShiftAsymptoticPositive_iff_sampled_potential`; on the nonnegative
coefficient domain, only the integer-log inequalities remain on its right side.

If also lam(n)<=vonMangoldt(n) for n>=2, excess is identically zero. Potential
inequalities imply asymptotic positivity by the new criterion. The existing
`abs_weilDeviation_le_total_excess_of_logShiftAsymptoticPositive` then forces
a(n)=0 everywhere. For n>=2, the positive square root yields lam(n)=vonMangoldt(n).
Conversely that equality on n>=2 makes all normalized deviations and potentials
zero, so every potential inequality holds.

## Corpus dependencies and boundary

Inspected `WeilFullConeNearNullPositiveDefinite.lean`: verified its use of
vonMangoldt_le_log, one_le_sqrt, and its general logarithmic-growth summability
lemma. The sampled characterization and one-sided excess bound are already
formalized. Toolchain API checks, leaf compilation, and all four public axiom
audits now pass. Each theorem uses exactly `[propext, Classical.choice, Quot.sound]`.

This is a domain restriction that discharges convergence, not a revival of
the unrestricted false receiver. No claim of general mixed-sign rigidity,
deficit summability, RH, or external novelty. No numerical experiments, new
axioms, or heartbeat increases.

## Exact new insight

Nonnegativity of the original coefficients controls the negative normalized
deviation before any test positivity is available. Together with finite excess,
this removes the convergence premise from the potential characterization on
this domain. For nonnegative minorants, no summability hypothesis remains:
the potential inequalities characterize von Mangoldt exactly on n>=2.

The unrestricted convergence-free counterexample remains valid. The new theorem
identifies a natural coefficient domain that excludes its divergent negative tail.

## Lean artifact and validation

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftNonnegativePotential.lean`.

- `abs_weilDeviation_le_max_log_excess_of_nonneg`
- `summable_potential_of_nonneg_coefficients`
- `weilLogShiftAsymptoticPositive_iff_potential_of_nonneg_coefficients`
- `nonneg_minorant_potential_iff_exact`

Initial leaf, scratch axiom audit, and final `lake --old env lean ... -o ...`
passed with default heartbeats and no diagnostics. The local `.olean` is exported.
Module wired into `RHTower.lean`; index refresh passed and all four API rows
were verified. Scoped whitespace checks passed.

Authoritative lint exited 1 with five unrelated unreachable HTGeometry modules:
`ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. No reported lint
error concerns this leaf. No unrelated module was modified.

Exact local lexical search found no hit for the four-term conjunction. Broader
local search returned 3068 declarations across 665 modules and found the existing
full-positivity convergence results and general potential-summability ingredient.
This is a corpus-local dependency and duplication audit, not an external novelty
claim. All owned jobs exited; all ten owned scratch files were removed and
their absence verified. The exported Lean artifact remains available.

## Remaining frontier

General mixed-sign rigidity remains open. The new criterion removes convergence
on a natural domain but does not prove that every nonnegative coefficient
sequence satisfying the potential inequalities equals von Mangoldt; the exact
classification here also requires the minorant hypothesis.
