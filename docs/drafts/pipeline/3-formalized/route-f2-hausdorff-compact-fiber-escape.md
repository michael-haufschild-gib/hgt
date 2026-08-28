# Route F2 Hausdorff compact-fibre escape

- **ID:** `route-f2-hausdorff-compact-fiber-escape`
- **Stage:** 3-formalized
- **Type:** FALSIFIED proof class / exact moment-space countermodel
- **Route:** F2 — Sonin trace-moment weld
- **Source:** `rh-current-frontier-map.md` · F2 simultaneous higher-moment gate
- **Verdict:** `FALSE` for compactness plus complete Hausdorff/Bernstein positivity as synchronizer

## Exact claim under attack

F2 already knows that separate minimum attainment does not force a common zero.  The stronger
candidate tested here adds the corpus's complete Hausdorff/Bernstein positivity on both sides:

> A nonempty compact exact-zeroth fibre, continuous source moments, and complete Hausdorff moment
> positivity of every source sequence and the target sequence force one fibre point matching all
> target moments.

## Gates

- [x] 0 → 1 in-progress: exact countermodel and stronger Hausdorff candidate fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile audit complete
- [x] 2 → 3 formalized: closed unconditional Lean theorem, leaf build and axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and external priority audit

## Countermodel

Let the aperture fibre be the compact interval `K=[0,1]`.  At `a∈K`, use the source probability
measure `mu_a=delta_a`; use target measure

```text
nu = (delta_0 + delta_1) / 2.
```

Their moment sequences are

```text
s_a(n) = a^n,
t(0) = 1,
t(n+1) = 1/2.
```

Every source sequence and the target sequence is a Hausdorff moment sequence because it is the
moment sequence of a positive probability measure supported on `[0,1]`.  More explicitly, for the
radius-one scaled Hausdorff recursion `D`:

```text
D(s_a,k,r) = a^k (1-a)^r >= 0,
D(t,k,0) = t(k) >= 0,
D(t,0,r+1) = 1/2,
D(t,k+1,r+1) = 0.
```

All source sequences have exact target zeroth moment: `s_a(0)=t(0)=1`.  Every coordinate is
continuous in `a`, so every defect attains its minimum on `K`.

No common moment match exists.  Equality at degree one forces `a=1/2`; equality at degree two
would then force `1/4=1/2`, contradiction.

## Killing theorem `[PAPER-PROVED]`

Compact exact-zeroth normalization plus complete Hausdorff positivity of the entire source family
and target does not imply a common all-moment point.  This remains false when all source sequences
are extreme Hausdorff sequences (Dirac measures) and the target is a two-atom probability measure.

## Strongest positive survivor `[PAPER-PROVED]`

The obstruction gives a sharp convex-geometric discriminator.  A one-parameter Dirac moment curve
can meet a non-extreme target moment sequence in individual coordinates without containing that
target.  Viable F2 completion must therefore supply at least one of:

1. nested nonempty finite-block zero sets on the compact fibre;
2. a source-specific rigidity theorem forcing the target measure to be an extreme point of the
   Sonin moment curve;
3. an injective recurrence determining every higher source moment from the matched zeroth and one
   additional source coordinate.

Under item 1, compactness genuinely works: the nested closed finite-block zero sets have nonempty
intersection.  Hausdorff positivity alone supplies only membership in the same convex moment cone,
not membership in the one-dimensional source curve.

## Hostile audit

- The example uses positive probability measures, not arbitrary continuous defect functions.
- Both sides satisfy every order of the Hausdorff finite-difference inequalities.
- Fibre is compact and nonempty; zeroth matching holds everywhere, stronger than F2's requirement.
- Source moments vary continuously and each source sequence is an extreme point of the Hausdorff
  moment cone.
- The countermodel does not disprove the literal Xi/Sonin common-zero statement.  It kills only
  compactness plus joint Hausdorff/Bernstein positivity as its producer.

## Literature boundary

Classical Hausdorff theory identifies completely monotone sequences with moments of finite positive
measures on `[0,1]`.  Modern treatments likewise describe the full convex moment class and its
generating functions; see Liu--Pego, *On generating functions of Hausdorff moment sequences*,
arXiv:1401.8052.  Nothing in that classification puts a fixed target measure on a prescribed
one-parameter Dirac curve.  This countermodel is standard moment convexity, not new scientific
knowledge.

## Route effect

- **Killed:** `compact zeroth fibre + source/target Hausdorff positivity → common all-moment zero`.
- **Survives:** F2 only through a genuinely Xi-specific finite-block nesting, extremality, or moment
  recurrence law.
- **Representation lesson:** F2 is an intersection problem inside a convex moment cone, not a
  positivity problem.  Cone membership cannot replace curve incidence.

## Lean certificate

`RHTower.f2HausdorffCompactFiberEscape` is a closed theorem with no parameters, premises, local
hypotheses, or added axioms.  It packages compactness, exact zeroth matching, complete scaled
Hausdorff nonnegativity for every source and for the target, and failure of every all-moment
aperture match.

- Module: `GaloisForLFunctions.RHTower.F2HausdorffCompactFiberEscape`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/F2HausdorffCompactFiberEscape.lean`
- Targeted final audit: `lake build GaloisForLFunctions.RHTower.F2HausdorffCompactFiberEscape`
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only

## Log

- 2026-08-28 — generic compact-minimizer counterexample rejected as already present in frontier.
- 2026-08-28 — stronger source/target Hausdorff-positive probability-measure escape isolated after
  auditing `SoninCoupledQuantumHausdorff` and the exact zeroth-fibre compactness module.
- 2026-08-28 — dependency-closed proof and hostile audit complete; promoted before Lean work.
- 2026-08-28 — exact escape theorem checked directly, built as a leaf, audited with
  `#print axioms`, and wired into `GaloisForLFunctions.RHTower` without building the umbrella.
