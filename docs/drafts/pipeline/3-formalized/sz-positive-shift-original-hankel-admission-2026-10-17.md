# SZ: original arithmetic Hankel admission for every positive shift

## Objective and scope

Selected SZ, not previously worked in this cross-route goal. The required result
must remove a hard source-level obstruction toward RH. A new receiver, an
improved estimate alone, or a changed target receives no contribution credit.
PM's previous turn was verified progress; the full 44-route/candidate objective
remains active.

The read-only frontier identifies two connected gaps: a source Wronskian law
paying the moving infinite head and shell leakage, and a uniform cusp-preserving
passage from shifted canonical Xi functions to the original Xi function.

Evidence is restricted to the local Lean corpus and documented research search.
No external search, novelty audit, old research Markdown, numerical experiments,
extra analytic premises, or heartbeat increases. One owned foreground Lean build
at a time. Preserve concurrent edits and leave the frontier map unchanged.

## Plan

- [x] Audit exact original sources, existing infinite-head laws, and cusp domains.
- [x] State competing falsifiable conjectures and attack each against the corpus.
- [x] Complete a dependency-closed paper proof of the admission theorem below.
- [x] Formalize the exact theorem, run direct Lean and axiom audits, wire modules.
- [x] Assess contribution strictly, record remaining gaps, and clean owned scratch.

## Initial evidence

- `SuzukiScrewPointwiseNonnegativityCriterion`: exact nonnegative-screw RH receiver.
- `SuzukiCanonicalShiftedXi`: canonical shifted functions and existing local
  uniform convergence; the latter alone is not the missing cusp passage.
- `CCMUnitRieszSuzukiGreenPositiveInverse`: exact positive inverse but no
  unconditional arithmetic source sign.
- Three targeted deep corpus searches completed. Exact source identities and
  kernel admission domains were checked directly in Lean source.

## Conjecture ledger

1. Local uniform convergence of the canonical shifts suffices to supply the
   missing source passage: `BRIDGE`. Already proved; it supplies no source sign.
2. The prescribed coercive aperture source can converge to the Xi target:
   `FALSE` in those exact coordinates. The corpus proves its first defect tends
   to zero whereas the Xi first defect is strictly positive.
3. Strong continuity of the full shifted boundary operator resolves the missing
   passage: `BRIDGE`. Already proved, including boundary-zero layers; fixed
   vectors do not control moving infinite sources.
4. **All-positive-shift literal Hankel admission:** for every `omega > 0` and
   every aperture `a > 0`, the exact unsmoothed arithmetic kernel
   `suzukiSourceHFinite omega (x*y)` on the original `IntervalL2 0 a` defines a
   compact self-adjoint bounded operator. For `omega > 1/2` it is exactly the
   existing `suzukiCompressedHankelOperator`. No meromorphic-inner or RH premise.
   `PAPER PROVEN; LEAN VERIFIED`. Targeted discovery found no existing
   all-positive-shift literal operator theorem. Both exact-source capstones
   and compatibility with the old operator pass Lean and the axiom audit.

The actual barrier is the existing construction's use of square-integrable
cusp rows, available only for `omega > 1/2`. The proposed construction uses
integrable cusp mass and norm approximation of the exact source. It does not
claim a sign, invertibility at every aperture, or a uniform zero-shift limit.

## Dependency-closed paper proof of conjecture 4

Write `h = suzukiSourceHFinite omega`. Existing exact arithmetic Mellin identity
is absolutely convergent for every `omega > 0` on `Re s > 1 + omega` and equals
`xi(s-omega)/xi(s+omega)`. Take real `s = omega+2`. Hence `u^(-s) h(u)` is
integrable on the positive half-line. On `[1,a^2]`, multiplication by `u^s` is
bounded and continuous. Thus the literal `h` is integrable on `[1,a^2]`.
Existing source identities give measurability, `h(u)=0` for `u<=1`, and
`conj(h(u))=h(u)`. No arithmetic term has been removed.

If `a<=1`, `xy<=1` on `[0,a]^2`, so the literal operator is zero. Suppose
`a>1`. Put `p(u)=1_(1,a^2](u) h(u)` and
`M=integral_R |p(u)| du < infinity`. The original kernel equals `p(xy)` at
every point of `[0,a]^2`, including all totalized cusp points.

For `0<=x<=1/a`, the entire row is zero. For `1/a<x<=a`, change variables
`u=xy` and use nonnegativity to obtain

`integral_0^a |p(xy)| dy <= (1/x) M <= a M`.

The same estimate holds for columns by commutativity of `xy`. The measurable
kernel therefore meets the corpus Schur test. Its Schur operator is a bounded
operator on the original `IntervalL2 0 a`; for every input, the literal integral
exists for almost every output point and represents the output in `L2`.
Uniqueness follows from equality of the almost-everywhere integral formula for
every input. Reality of `h` and symmetry in `x,y` make the operator self-adjoint
by the Schur adjoint identity.

For positive integers `N`, define the intermediate truncation
`p_N = p * 1_{|p|<=N}`. Its square-integrable kernel on the finite square gives
a Hilbert-Schmidt, hence compact, operator `T_N`. These truncations serve only
to prove compactness of the original operator; they do not define a changed
source or a different final target. Set
`R_N = integral_R |p-p_N|`. Pointwise convergence and domination by the
integrable `|p|` give `R_N -> 0`. The same row/column argument applied to
`p-p_N` yields `||T-T_N|| <= a R_N -> 0`. Compact operators are closed in
operator norm, so the original `T` is compact.

Finally, when `omega>1/2`, both the old Hilbert-Schmidt construction and `T`
have the same literal integral formula on the same original `IntervalL2 0 a`.
Their equality follows for each input by `Lp.ext`. This gives an exact
extension across the construction's half-shift barrier, not a new receiver.

All quantifiers are explicit. Parameters are only the positive shift and
positive aperture; local integrability, row bounds, compactness and symmetry
are proved from the actual source. Remaining formal dependencies are ordinary
change of variables, dominated convergence, the already proved Schur operator,
Hilbert-Schmidt compactness and norm-closedness of compact operators.

## Search coverage

Both initial deep searches completed with `partial=false`, no errors, and
73,118 inventoried/indexed files. Most compiler metadata is source-only or
pending/stale, so applicability is checked in source and then Lean. Background
indexer refresh was deferred. The broad results include unrelated name matches;
the useful kernel threshold and exact source Mellin facts were inspected directly.

The third search, for integrable weakly singular Hankel compactness and the
positive-shift source below one half, completed with `partial=false`, no errors,
and 73,119 indexed files. It located the Schur and Hilbert-Schmidt tools used
above, but no existing theorem admitting this exact arithmetic operator for
every positive shift. Proposed search ingredients were not accepted as proofs.

## Formal checkpoint

New generic module: `HTGeometry/IntegrableMultiplicativeHankel.lean` (211 lines,
14 public theorems). New exact-source module:
`RHTower/SuzukiCanonicalPositiveShiftHankel.lean` (163 lines, seven public theorems).
The initial elaboration errors were repaired. Each module passes its direct
`lake --old env lean -j1 -o ... <module>` check with exit 0, no warnings, and
default heartbeats. Both modules are wired into their corresponding umbrellas;
no umbrella or full build was run.

The scratch axiom audit checks all 21 public theorems and exits 0. Every theorem
uses only `propext`, `Classical.choice`, and `Quot.sound`. Mathlib API checks
also pass against this toolchain. No analytic hypothesis, new axiom, proof hole,
numerical experiment, or altered source was introduced.

Exact-source namespace: `RHTower.SuzukiPositiveShiftHankel`.

- `integrableOn_source`: complete arithmetic source is locally integrable for
  every positive shift.
- `operator`, `ae_integrable`, `operator_coeFn`: bounded operator on the original
  `IntervalL2 0 a`, represented by the literal unsmoothed kernel for every input.
- `operator_isCompact`, `operator_isSelfAdjoint`: unconditional compact and
  self-adjoint admission for every `omega>0` and every real aperture.
- `operator_eq_existing`: equality with `suzukiCompressedHankelOperator` on its
  old domain `omega>1/2`, `a>0`.
- `operator_unique`: the literal integral formula uniquely identifies this
  operator on the original space.

## Contribution assessment and remaining frontier

The removed obstruction is the original source construction's half-shift
admission barrier: the entire critical range `0<omega<=1/2` now has the exact
compact self-adjoint arithmetic Hankel operator on the original Hilbert space.
Credit is for this source existence and compactness theorem. The row estimate
is only a proof ingredient. Compatibility with the existing operator certifies
that the target and source were preserved.

SZ's moving infinite-head Wronskian law, source positivity, all-aperture
invertibility, and uniform cusp-preserving zero-shift passage remain open.
The result supplies no RH proof or unconditional sign. The 44-route/candidate
goal remains active.

## Final repository checks

- Both direct module checks: exit 0, no warnings.
- Scratch audit of all 21 public theorems and toolchain API names: exit 0.
- `scripts/formal_tools.py index`: exit 0. A second refresh resolved index drift
  from concurrent source edits.
- `scripts/formal_tools.py lint --check-generated`: final exit 1 solely because
  two concurrently added modules are not yet reachable from `RHTower.lean`:
  `ArchimedeanResonanceRange` and
  `EvenSectorBlindMinimumSmallAperturePositivity`. The final check reports no
  stale generated files, no new-SZ-module issue, and 381 existing large-file
  warnings. Those other sessions' unfinished modules were preserved. No global
  lint pass is claimed.
- Each new module appears exactly once in its corresponding umbrella.
- All three owned search JSON files and both owned Lean scratch files were
  removed; absence was checked. All owned research, Lean and guarded jobs ended.

Paper and exact-source Lean status: `COMPLETE`. Mathematical contribution:
`POSITIVE SOURCE ADMISSION OBSTRUCTION REMOVED`. Shared repository lint status:
`BLOCKED BY CONCURRENT UNWIRED MODULES`, independently of the direct proof checks.
