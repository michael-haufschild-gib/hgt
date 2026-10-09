# Sharp reversal cost for canonical Gram gauges

Status: FORMALIZED, 2026-10-09. All four targets proved and natively verified.

## Formal result and positive survivor

`WeilLogShiftGramAntipodal.lean` proves the canonical unit-coordinate and
negative-atom formulas, their exact actual costs, and the antipodal balance
identity for every functional. `WeilLogShiftGramReversalCost.lean` proves
the sharp reversal criterion, its equivalent finite atom test, the exact
dimension-weighted reverse-cost sum, the dimension lower bound, and a strict
asymmetry witness whenever the support has at least two coefficients.

The unconditional receiver is `exists_finiteWeilGram_reversal_geometry`.
The canonical dictionary is constructed before all constants and functionals.
No new model assumption is required. The norm-symmetry obstruction is accompanied
by the exact positive survivor: reversal on the whole functional space is
classified by finitely many inequalities using actual Gram costs.

## Verification

- Native `lake --old env lean <leaf> -o <leaf.olean>` passed for both leaves,
  with empty final diagnostic logs. The antipodal leaf's tactic-style warning
  was removed. The reversal leaf's zero-dimensional cast simplification was
  replaced with an explicit equality/order calculation; all branches then passed.
- `/tmp/hgt-weil-gram-reversal-final-audit.lean` passed: 17 API terms checked
  in this toolchain, and all 15 authored public declarations audited using
  `#print axioms`. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
  A source-to-audit coverage check confirmed no public declaration was omitted.
- Both source/olean pairs are fresh. Both leaves are imported exactly once in
  `RHTower.lean`. Targeted `git diff --check` passed. Index refresh passed;
  exact local lexical search finds the unconditional receiver.
- Global lint exited 1 with three unrelated HTGeometry umbrella gaps:
  `PaperPrimeFlowCoefficients`, `PaperPrimeTerminatingSupport`, and
  `QKrawtchoukCompanionTriangular`. No diagnostics for either new Gram leaf;
  no placeholder findings. Repository-wide lint is not claimed clean.

Logs: `/tmp/hgt-weil-gram-antipodal-build.log`,
`/tmp/hgt-weil-gram-reversal-build.log`,
`/tmp/hgt-weil-gram-reversal-final-audit.log`,
`/tmp/hgt-weil-gram-reversal-index.log`,
`/tmp/hgt-weil-gram-reversal-lint.log`,
`/tmp/hgt-weil-gram-reversal-search.json`.

## Conjecture and scope

For the existing unconditional minimal dictionary D, put a = D.balance,
q(L) = D.weights L, k(w) = finiteWeilGramTailCost 1 w, and
S = sum_w a(w) k(w). Determine the exact cost of reversing a functional.
All mathematical evidence is the local Lean corpus. No web, papers, or numerics.

Targets:

1. Antipodal coordinates satisfy q(L) + q(-L) = t a for some t >= 0.
2. For each dictionary atom F_w, q(F_w) is the unit coordinate, and
   q(-F_w)(v) = a(v)/a(w) - 1_{v=w}. Hence G(F_w)=k(w), and
   a(w) * (G(F_w)+G(-F_w)) = S.
3. Exact reversal criterion, for every real r:
   [for every L, G(-L) <= r G(L)] iff
   [for every w, S <= (r+1) a(w) k(w)].
4. Sum_w a(w) G(-F_w) = |s| S. Every nonnegative universal reversal
   constant is at least |s|. If |s| >= 2, at least one dictionary atom
   costs strictly more to reverse. Include an unconditional existence
   receiver whose dictionary is chosen before all scalars/functionals.

## Proof argument before Lean

The existing addition-defect theorem at (L,-L), together with q(0)=0,
gives (1). For an atom, a nonempty dictionary has |s|+1 >= 2 members,
so its unit coordinate has a zero coordinate. It represents F_w and is
nonnegative; boundary uniqueness gives its canonical weights. The vector
a/a(w)-e_w represents -F_w by the proved balance relation, is nonnegative,
and vanishes at w. Boundary uniqueness proves the second formula. Summing
against actual positive costs proves (2).

Necessity of (3) follows by testing F_w and multiplying by a(w)>0.
For sufficiency in a nonempty dictionary, take the antipodal scalar t.
The zero coordinate j of q(-L) gives q(L)(j)=t a(j), so
G(L)>=t a(j) k(j). Summed antipodal identity gives G(L)+G(-L)=t S.
The atomic inequalities and S>0 imply r+1>=0; therefore
t S <= t(r+1)a(j)k(j) <= (r+1)G(L), yielding the bound.
An empty dictionary has G identically zero, so both sides hold for every r.

Sum a(w)(G(F_w)+G(-F_w))=S over the |s|+1 atoms; the forward
weighted cost is S. This proves (4), including the empty case separately.
Summing any universal atomic reversal bound gives |s|S<=rS. Since S>0
when s is nonempty, r>=|s|. If every atom were no dearer to reverse,
the same exact identity would imply |s|<=1. Thus the asymmetry obstruction
has a positive survivor: exact reversal geometry and sharp finite inequalities.

## Work plan (completed)

- Verify required local Lean APIs in a scratch file.
- Formalize antipodal coordinates and actual atom costs.
- Formalize sharp reversal criterion, dimension law, and asymmetry witness.
- Compile each leaf natively, wire umbrella, audit every public declaration,
  check freshness, refresh local index, and run formal lint.

No symmetry or bundled norm is assumed. No global cutoff-cost upper bound
or exact single-test image surjectivity is claimed.
