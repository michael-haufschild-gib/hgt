# Optimal Gram reversal factor and dimension-equality rigidity

Status: FORMALIZED, 2026-10-09. All three conjectures proved and natively verified.

## Formalization and exact insight

`WeilLogShiftGramOptimalReversal.lean` defines `atomReversalRatio` as S/p_w-1,
proves that it is the actual atom reversal ratio, and proves it is nonnegative.
`nativeGauge_atom_ratio_controls_iff` classifies every atom attaining the
uniform reversal bound: exactly the atoms minimizing p_w. The theorem
`exists_optimal_reversal_atom` supplies a minimum atom, equality at that atom,
the dimension lower bound, and the exact threshold for every real bound r.
It explicitly separates the empty dictionary, whose zero gauge admits every
real r and therefore has no least real reversal constant.

`WeilLogShiftGramReversalRigidity.lean` proves the dimension bound holds iff
(d+1)*p_w=S for every atom, equivalently iff every p_w agrees. The unconditional
receiver is `exists_finiteWeilGram_optimal_reversal_rigidity`: dictionary choice
precedes all functionals and constants. No new model premise is introduced.

## Verification

- Both new leaves passed native `lake --old env lean <leaf> -o <leaf.olean>`
  builds with empty final diagnostic logs. The only first-pass issue in the
  optimal-reversal leaf was an unnecessary `ring` after `field_simp` had already
  closed the goal; removing it gave a clean build. The rigidity leaf passed first try.
- `/tmp/hgt-weil-gram-rigidity-final-audit.lean` passed, checking eight API terms
  and all ten authored public declarations with `#print axioms`. Only
  `propext`, `Classical.choice`, and `Quot.sound` occur. Source-to-audit coverage
  was checked for every public declaration.
- Both source/olean pairs are fresh. Both imports appear exactly once in
  `RHTower.lean`. Targeted `git diff --check` passed. Index refresh passed;
  exact local lexical search finds the new unconditional receiver.
- Global lint exited 1 with four unrelated HTGeometry umbrella gaps:
  `PaperPrimeFlowCoefficients`, `PaperPrimeTerminatingSlice`,
  `PaperPrimeTerminatingSupport`, and `QKrawtchoukCompanionTriangular`.
  No diagnostics for either new leaf; no placeholder findings. Global lint
  is not claimed clean.

Logs: `/tmp/hgt-weil-gram-optimal-reversal-build.log`,
`/tmp/hgt-weil-gram-reversal-rigidity-build.log`,
`/tmp/hgt-weil-gram-rigidity-final-audit.log`,
`/tmp/hgt-weil-gram-rigidity-index.log`, `/tmp/hgt-weil-gram-rigidity-lint.log`,
`/tmp/hgt-weil-gram-rigidity-search.json`.

## Target

Use the existing unconditional canonical dictionary D. Write k_w for its
actual B=1 tail cost, a_w for its positive balance, p_w=a_w*k_w,
S=sum_w p_w, and G for its native gauge. Only local Lean corpus supplies
mathematical evidence; no web, external papers, or numerics.

Conjectures:

1. The atom reversal ratio R_w=S/p_w-1 equals G(-F_w)/G(F_w).
2. R_w bounds G(-L)/G(L) on all functionals exactly when p_w is a
   minimum of the finite family p. Thus the optimal uniform reversal
   factor is attained by an actual dictionary atom, with a precise
   classification of every attaining atom.
3. The dimension lower bound d=|s| is a valid reversal factor exactly
   when all balance-weighted actual costs p_w agree. This is a rigidity
   criterion, not an assertion that such an actual dictionary exists.

## Dependency-closed proof before Lean

The existing atom-cost identities give
G(F_w)=k_w>0 and G(-F_w)=S/a_w-k_w. Division by k_w proves (1).
For a nonempty dictionary, S>0 and every p_w>0. The existing sharp
finite criterion says R_w is a global bound iff, for every v,
S <= (R_w+1)*p_v = (S/p_w)*p_v. Multiplying by p_w and canceling S
gives exactly p_w<=p_v. A minimum exists on the finite nonempty set.
Necessity of every bound r>=R_w follows by evaluating F_w; sufficiency
follows from the attained bound R_w and G(L)>=0. The empty dictionary
is recorded explicitly, rather than inventing a least real constant
for its identically zero gauge.

For (3), the finite criterion at r=d gives S <= (d+1)*p_w for all w.
In a nonempty dictionary there are exactly d+1 atoms, so the sum of the
nonnegative slacks (d+1)*p_w-S is zero. Each slack must vanish. The
positive factor d+1 then forces all p_w equal. Conversely equal p_w
sum to S=(d+1)*p_w, supplying all finite inequalities. The empty case
is vacuous on both sides and is handled explicitly.

## Work plan (completed)

- Check required installed Lean APIs in scratch.
- Formalize atom ratios, attainment classification, and a minimizing witness.
- Formalize dimension-bound rigidity and an unconditional joint receiver.
- Native leaf builds, complete public axiom audit, umbrella/freshness checks,
  local index refresh, and formal lint.

Global cutoff-cost upper bounds, exact single-test image surjectivity,
existence of a balanced actual dictionary, and a bundled symmetric norm
are not claimed by this increment.
