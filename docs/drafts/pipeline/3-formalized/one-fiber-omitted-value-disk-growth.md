# A unique center fiber gives a uniform omitted-value growth bound

- **ID:** ONE-FIBER-DISK-GROWTH-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, including ray growth and actual Xi factor exclusion)
- **Parent:** `../1-in-progress/xi-single-mark-infinite-cover-exclusion.md`

## Exact statement

There is B>1 such that for every disk D(c,R), every holomorphic f on that disk, and every omitted value a, if c is the only preimage of f(c) in the disk, then
|f(z)−a|≤B|f(c)−a| whenever |z−c|≤R/2.

Injectivity is sufficient but stronger than needed. This strengthens the earlier inverse-chart plan: no global inverse, covered-circle filling lemma or Koebe theorem is required.

## Corpus basis

- `Bottcher/AnalyticRoot.exists_analyticOnNhd_pow_eq`: analytic square root of a nonvanishing function on a simply connected open set.
- `HTGeometry/ModularDiskChart.exists_bound_of_omitting_compact_base`: uniform Schottky bound for maps omitting 0,1, with center value in a fixed compact set.
- Mathlib `Analysis/Complex/RiemannMapping.lean` contains partial square-root embedding results, not full uniformization. It suggested the useful normalization; no external link was opened.

## Complete paper proof

Since f−a never vanishes and the disk is simply connected, choose an analytic square root s with s²=f−a. Put psi(z)=−s(z)/s(c). It is holomorphic and nonzero, and psi(c)=−1. If psi(z)=1, then s(z)=−s(c), hence f(z)=f(c). The unique-center-fiber hypothesis forces z=c, contradicting psi(c)=−1. Thus psi omits both 0 and 1.

Apply the corpus's compact-base Schottky bound with K={−1} and rho=3/4. It gives a universal M for |psi| on the smaller open disk, which contains |z−c|≤R/2. Enlarge M to at least 1. Then
|f(z)−a|=|s(z)|²≤M²|s(c)|²=M²|f(c)−a|.
Taking B=M²+1 supplies B>1.

## Application being pursued

For an injective inverse logarithm phi on the right half-plane omitting a, apply the disk bound at center x>0 and radius x. This gives |phi(3x/2)−a|≤B|phi(x)−a|. Iteration yields a polynomial bound along x=(3/2)^n. Combined with F(phi(x))=R exp(x), R≥1, this proves positive lower order of the projection. The ray iteration and all-radii passage are now formalized. Construction of the logarithmic tract and uniformization of the completed image cover remain open.

Novelty outside the corpus is unverified. This theorem is a research ingredient, not an RH proof or a declared new field.

## All-radii passage: paper proof completed

Suppose samples z_n satisfy |z_n|≤A B^n and |F(z_n)|≥exp(q^n), with A>0, B>1, q>1. Choose N≥1 with B≤q^N and put δ=1/(2N). For r≥max(A,(AB)^2), choose n with B^n≤r/A<B^(n+1), using the corpus's `exists_nat_pow_near`. Then |z_n|≤r and r<AB(q^n)^N. Since (AB)^2≤r, this forces AB<(q^n)^N, hence r<(q^n)^(2N). Therefore r^δ≤q^n and exp(r^δ)≤|F(z_n)|. This is exactly `PositiveLowerOrder F` on every sufficiently large disk.

For the inverse-chart application, |phi(q^n)|≤|a|+B^n|phi(1)−a|≤A B^n with A=max(1,|a|+|phi(1)−a|), while the logarithmic identity supplies the exponential sample bound. Thus the local one-fiber estimate plus a genuine inverse logarithmic tract suffices for positive lower order. No numerical asymptotics or unproved distortion constant is used.

## Stronger statement exposed by the root argument (separate conjecture)

A bound on the number k of distinct preimages of the center value should suffice, with a constant B_k. Take an analytic (k+1)-st root s of f−a. Among the k+1 roots of unity, at least one eta is omitted by s/s(c), since each attained root requires a distinct point of the center fiber. The attained center root is 1, so eta≠1. Dividing by eta yields a map omitting 0,1, whose center lies in the finite set of reciprocals of nontrivial (k+1)-st roots of unity. Compact-base Schottky applies uniformly over that finite set. Raising the norm bound to k+1 gives the claimed ratio bound.

This stronger finite-fiber form has not been audited or formalized; retain it as a new conjecture rather than silently broadening the checked one-fiber theorem. The current RH attack needs only the one-fiber case for inverse logarithmic charts.

## Formal progress

- 2026-10-09: exact one-fiber disk theorem checked in Lean with zero warnings and no placeholders. Promoted to `HTGeometry/OneFiberDiskGrowth.lean` and wired to its umbrella; production verification in progress.
- Ray recurrence, all-radii geometric sample theorem and positive-lower-order conclusion drafted in `/tmp/hgt-logarithmic-tract-growth.lean`; not yet checked.
- Actual Xi geometric-factor corollary drafted in `/tmp/hgt-xi-logarithmic-factor.lean`; not yet checked.
- Slow verification diagnosed by a one-second sample of the owned Lean process: it was loading imports (`lean_mark_persistent`), not spending time in proof tactics. The run completed successfully. No other process was interrupted and no heartbeat setting changed.

- Production leaf build of `OneFiberDiskGrowth`: PASS, 3953 jobs, no warnings. Axiom audit and final direct source checks follow the ray-growth extension.

- Ray recurrence, geometric-sample lower order, and inverse-chart positive lower order all passed Lean on their first check, warning-free. Promoted as `HTGeometry/LogarithmicTractGrowth.lean`, wired to umbrella.
- Actual Xi consequence promoted as `RHTower/XiLogarithmicTractFactorRigidity.lean`, with an explicit nonexistence capstone and no assumptions on Xi; production build and audits pending. It excludes the defined geometric factor class, not the full hypothetical image cover until chart construction and uniformization are proved.

- Production leaf build of `XiLogarithmicTractFactorRigidity`: PASS, including all three geometric-growth declarations and both Xi exclusions. Only replayed dependency warnings. Log: `/tmp/hgt-xi-logarithmic-factor-build.log`.

- Six-declaration axiom audit: PASS, only `propext`, `Classical.choice`, `Quot.sound`. Log `/tmp/hgt-xi-logarithmic-factor-axioms.log`. Direct checks of all three new source files are in progress; the source/kernel-checked production build already passed.

- Final direct `OneFiberDiskGrowth.lean` check: PASS, exit 0, empty log `/tmp/hgt-one-fiber-growth-final.log`.
- Final direct `LogarithmicTractGrowth.lean` and `XiLogarithmicTractFactorRigidity.lean` checks: PASS, exit 0, empty logs `/tmp/hgt-logarithmic-tract-growth-final.log` and `/tmp/hgt-xi-logarithmic-factor-final.log`. All six public declarations are audited. Obsolete implementation scratch files removed; audit scripts and logs retained.
- Index regenerated. Latest global lint: FAIL on eight unrelated unreachable modules: RHTower.CCMFullGroundZeroSideEigen, ChronologicalMobiusEscape, ThetaCuspRatioKineticLeading.JetHeads; HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation, ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No own-source or forbidden-declaration failure. Full log `/tmp/hgt-xi-logarithmic-factor-lint.log`.
