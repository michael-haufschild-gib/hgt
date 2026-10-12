# Finite Weil quadratic adaptive replication

Status: formalized and natively audited (2026-10-12).

## Question and local frontier

Use only local Lean mathematical sources; no web, external papers, or numerical
experiments. The preceding affinity increment proves single-copy affinity tends
to one exactly for equal diagonal coefficients, and r-copy separation for
unequal diagonals. It leaves same-diagonal growing products unresolved.

Result: an exact adaptive classification, without assuming convergence rates.
Equal diagonals admit a monotone replication count m(r)<=r tending to
infinity with product affinity tending to one. Unequal diagonals give
affinity tending to zero under every replication count tending to infinity.
This does not classify a prescribed schedule such as m(r)=r for equal diagonals.

## Paper proof

1. General slow diagonal selection. Let F(n,r) tend to a countably generated
   target filter L for each fixed n. Choose an antitone basis B(n) of L and
   thresholds T(n) such that r>=T(n) implies F(n,r) belongs to B(n). Define
   m(r) as the greatest n<=r with T(n)<=r, defaulting to zero. The local
   `Nat.findGreatest` API proves m(r)<=r and monotonicity. For each n, all
   r>=max(n,T(n)) have m(r)>=n, so m tends to infinity. Once r>=T(0), the
   selected index qualifies, hence F(m(r),r) belongs to B(m(r)). Antitonicity
   of the basis proves diagonal convergence to L.
2. Apply this selection to F(n,r)=h(r)^n when h(r)->1 in ENNReal. Every fixed
   power tends to one by the corpus's continuous-power theorem. No distance,
   convergence rate, or pointwise h(r)<=1 assumption is required.
3. If h(r)->c<1 and m(r)->infinity, choose c<b<1. Eventually h(r)<=b, hence
   h(r)^m(r)<=b^m(r)->0. This extends the preceding r-th power squeeze to
   arbitrary diverging schedules.
4. For actual finite Weil quadratic tilts, use the proved affinity limit and
   `bhattacharyya_pi`. Its limiting kernel equals one iff s=S and is strictly
   below one iff s differs from S. Steps 2 and 3 give existence of stable
   monotone bounded schedules iff s=S, and universal separation iff s differs
   from S. Opposite directions follow from uniqueness of limits 0 and 1.

All actual-law roots have only the established subcritical coefficient domain;
analytic assumptions in generic helpers are discharged from existing Lean laws.

## Local discovery

- `diagonal tendsto sequence`: 16 declarations in 16 modules, all returned
  names/docs inspected, no markers. Specialized approximation and return
  sequences do not supply the needed monotone inverse-threshold selector.
- Broad `slow diagonal` OR search was exploratory (4698 eligible declarations,
  first 20 inspected), not a complete novelty audit. Its `choose_slow` hit is
  a finite averaged conditional-iid selector, not a diagonal limit selector.
- Installed Lean sources provide `Filter.exists_antitone_basis`,
  `HasBasis.tendsto_right_iff`, `eventually_atTop`, and all required
  `Nat.findGreatest` specification/monotonicity lemmas.
- Refined `schedule convergence`: 11 declarations in 10 modules, all returned
  names/docs inspected, no markers. Existing specialized cofinal source and
  transport schedules do not state this general slow diagonal selector.

## Formalized leaves

- `HTGeometry/MonotoneDiagonalSelection.lean`: `exists_monotone_diagonal_tendsto`,
  the general monotone selector into any countably generated target filter.
- `HTGeometry/AdaptiveAffinityReplication.lean`:
  `exists_monotone_ennreal_powers_tendsto_one` and
  `tendsto_ennreal_powers_zero_of_tendsto_lt_one`.
- `RHTower/WeilLogShiftQuadraticReplication.lean`:
  `exists_finiteWeilCanonicalJointQuadraticTilt_stable_replication_iff` and
  `forall_finiteWeilCanonicalJointQuadraticTilt_replication_zero_iff`.

## Verification

- All three final leaves passed foreground `lake --old env lean ... -o ...`
  natively with exit 0, empty logs, and fresh objects. One owned native Lean
  process at a time; no edits to live/queued sources or dependencies.
- Native `/tmp/hgt-weil-replication-final-audit.lean` passed: all five axiom
  reports and 13 API checks. Only `propext`, `Classical.choice`, `Quot.sound`;
  no residual diagnostics, new axioms, admitted proofs, or heartbeat increases.
- All five declarations unique; six direct import edges and five incoming
  imports inspected. Owned source/object and direct dependency freshness
  checked. Each new module wired exactly once into its theorem-area umbrella.
- Scoped local index publication: 5/5 declarations (2 actual classifications,
  1 selector, 2 power results), no markers, partial results, pagination gaps,
  or stderr. Source and umbrella whitespace checks clean.
- Global lint snapshot: exit 1, five unrelated errors and 367 warnings.
  Unreachable RHTower modules: `CCMPolarOddPrimeJumps`,
  `JointAncestryRandomPhaseParseval`, `PaperThetaUniformFourier`;
  unreachable HTGeometry module: `QKrawtchoukCompanionTriangular`.
  Existing `sorry`: `CCMPolarOddPrimeJumps.lean:104`.
  No error references this increment; unrelated files untouched.
- No web, external papers, numerical experiments, full/umbrella builds,
  subagents, commits, or pushes.

Audit artifacts: `/tmp/hgt-weil-replication-{metadata,audit-summary,index-summary}.json`,
`/tmp/hgt-weil-replication-final-audit.{lean,log}`, `/tmp/hgt-weil-replication-lint.log`;
native leaf logs `/tmp/hgt-<Leaf>.log`.

## Remaining boundary

Existence of a stable adaptive schedule is settled. The subsequent
finite-weil-quadratic-fast-replication card settles fast separating schedule
existence exactly when the actual finite laws are eventually unequal, for
arbitrary coefficients and depth schedules. Coefficient-level equality and
behavior under prescribed same-diagonal schedules remain open here. The corpus-wide goal
remains active.
