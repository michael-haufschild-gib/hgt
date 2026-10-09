# Countable sampled convergence recovers the full potential cone

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no external papers or web searches.

## Plan and exact claim

1. Extract the corpus's generic logarithmic-block-to-Cauchy argument.
2. Recover deficit block bounds from convergent integer-log potential samples
   and their inequalities, assuming summable excess.
3. Prove an exact characterization of asymptotic log-shift positivity, audit
   every public result, wire/index the leaf, run lint, and clean owned scratch.

Let `a=weilDeviation lam`, `e=deviationExcess lam`, `v=deviationDeficit lam`,
and `psi=deviationPotential lam`. On the domain `Summable e`, the conjectured
equivalence is:

`WeilLogShiftAsymptoticPositive lam` iff, for every integer `m>=2`,
the signed series defining `psi(log m)` is summable and `psi(0)<=psi(log m)`.

No Cauchy bound, growth bound, deficit summability, or origin convergence
is assumed on the right-hand side.

## Dependency-closed paper proof

Write `E=sum e` and `K=riemannAutocorr`. Since `0<=K<=K(0)`, excess
potentials converge at all shifts and are at most `2 K(0) E`.

At each sample `log m`, convergence of the signed series and the excess
series implies convergence of the deficit series, using `v=e-a`. Thus
`psi(log m)=potential_e(log m)-potential_v(log m)` is a legitimate series
identity. The assumed potential inequality gives

`0 <= potential_v(log m) <= S := 2 K(0) E-psi(0)`.

In particular `S>=0`. This deduction treats the total expression `psi(0)`
only as a real number; it never uses an unproved series decomposition at zero.

For every natural `j`, the existing choice `m=floor(exp j)+1` has `m>=2`
and lies within logarithmic distance one of every n with `floor(log n)=j`.
The existing kernel lower bound `K>=kappa>0` on `[-1,1]` and finite-sum
comparison with the convergent deficit series at that sample yield

`sum (n in F),v(n) <= S/kappa`

for every finite subset F of every logarithmic block. No growth hypothesis
is needed for this finite-sum comparison because summability is already known.

Adding the finite total excess gives the same block control for `|a|<=e+v`.
For a nonnegative weight w with w(0)=0, a block bound B supplies w(n)<=B by
singleton sets. Hence the existing logarithmic-growth hypotheses follow.
The corpus's block estimate bounds its kernel potential at every real shift;
positive Cauchy smoothing then gives `CauchyBounded w D` for some D>=0.

Apply this generic result to |a|. The previous Cauchy/potential equivalence
now proves asymptotic log-shift positivity. Necessity of sampled convergence
and inequalities follows from the existing one-sided excess-control theorems.
All-real convergence, including the origin, and uniform whole-panel convergence
are recovered consequences, not assumptions.

## Audit boundary

This reduces the previous Cauchy side condition to convergence at countably
many actual samples. It does not eliminate all convergence hypotheses, prove
mixed-sign rigidity, or assert external novelty. No full Weil positivity,
new axiom, numerical experiment, or increased heartbeat limit is used.

## Lean artifacts and validation

New leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftSampledPotentialCone.lean`.
Public results:

- `exists_deficit_logBlock_bound_of_sampled_potential`
- `exists_cauchyBounded_absDeviation_of_sampled_potential`
- `weilLogShiftAsymptoticPositive_iff_sampled_potential`

In `WeilLogShiftDeficitTranslation.lean`, exposed
`exists_integer_log_probe_for_block` and extracted
`exists_cauchyBounded_of_logBlock`. The previous deficit Cauchy theorem now
uses this generic theorem; its public statement is unchanged. The generic
theorem requires nonnegativity, weight zero at zero, and uniform block mass;
the absolute normalized deviation satisfies these structural conditions.

Both changed leaves passed `lake --old env lean ... -o ...` with default
heartbeats and no diagnostics. Scratch signatures and axiom checks passed
for all three new results, all six public results in the changed shared
module, and all five dependent Cauchy/potential results. All fourteen use
exactly `[propext, Classical.choice, Quot.sound]`.

Module wired into `RHTower.lean`. Index refresh passed; all five new API rows
were verified. Scoped whitespace checks passed. Authoritative lint exited 1
with eight unrelated unreachable modules: RHTower's
`CCMGroundEnergyZeroSumBound`, `CanonicalProductE1RealLineBounds`, and
`PaperCircleObservationHistory`; HTGeometry's `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
and `BoundaryCoronaCStarAlgebra`. No reported lint error concerns these leaves.

The exact local lexical search for `summable nullPotential block` found no
indexed match. Broader search and source inspection located the existing
one-sided control, finite-sum comparisons, and potential-to-Cauchy estimates.
Search coverage supports this dependency reduction, not external novelty
or exhaustive semantic coverage of the corpus.

## Exact insight and next frontier

Countable sampled convergence plus the potential inequalities regularizes
the entire signed potential: local mass bounds, Cauchy control, all-real
convergence, and uniform panel convergence follow. The proof never uses a
series identity at the origin before obtaining its convergence.

The sparse-convergence conjecture is now proved in
`weil-logshift-sparse-convergence.md`: convergence at floor(exp j)+1 suffices,
retaining all integer-log potential inequalities. Its generalized covering
theorem allows any fixed finite radius. Do not drop every convergence
condition without auditing totalized divergent `tsum` values.
Mixed-sign summable-excess rigidity remains open.
