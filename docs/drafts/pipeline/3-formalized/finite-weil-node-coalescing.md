# Coalescing actual Gram nodes and removing cancellation cost

Status: FORMALIZED, 2026-10-10. All owned verification processes are terminal.

## Scope and evidence

Only local Lean corpus and installed Lean dependencies. No web, papers, or
numerics. Search: `/tmp/hgt-weil-coalescing-search.json` (cached lexical,
20 returned declarations; no freshness/coverage claim). Exhaustive text search
of WeilLogShift leaves found no node-coalescing theorem. Actual form/cost
definitions and the newly verified signed-duplication law are the starting
evidence. This is a bridge to representation-independent cost analysis;
external novelty is unassessed.

## Exact conjecture and attack

Every actual finite test admits an actual encoding with distinct node positions,
the same Gram form on EVERY coefficient support, and no greater tail cost for
ANY nonnegative normalization. For positive outer scale and positive tail
normalization, merging has equal cost exactly when every node fiber satisfies
`abs(sum amplitudes) = sum(abs amplitudes)`.

Potential failure: quadratic cross-terms could frustrate scalar cancellation.
They do not: after grouping, the exponential cost kernel is strictly positive
entrywise. This is not a positive-semidefinite assertion. Its positive diagonal
detects every strict loss of absolute mass. Zero scales and empty node sets
must be handled explicitly. Distinct positions may still have zero amplitudes;
no claim of minimal encoding or minimal cost across equal Gram forms is made.
Verdict: BRIDGE, with a precise rigidity law worth preserving.

## Dependency-closed paper proof

For finite types I,J and q:I→J, let m_y=sum_{q(i)=y}u_i and
A_y=sum_{q(i)=y}|u_i|. For ANY kernel K:J×J→R, distributing both
fiber sums and regrouping yields
sum_yz m_y*m_z*K(y,z)=sum_ij u_i*u_j*K(q(i),q(j)).
Apply to every pairedLogKernel coordinate to preserve all actual Gram forms.

For cost kernel H(y,z)=B*exp(2|x_z-x_y|), old cost equals
a*sum_yz A_y*A_z*H(y,z), while merged cost equals
a*sum_yz |m_y|*|m_z|*H(y,z). Triangle inequality gives
0<=|m_y|<=A_y. For B>=0 every summand is ordered, proving contraction.
For a>0,B>0 equality of costs forces equality of all ordered summands.
At diagonal (y,y), H(y,y)=B>0, hence |m_y|^2=A_y^2; nonnegativity
forces |m_y|=A_y. Conversely these fiber equalities identify every summand.

For an actual test (N,x,u,a), take J=univ.image x as a subtype of R,
q(i)=x_i in J, and node map J→R the subtype projection. It is injective.
Reindex J with finiteWeilGramTestOfFinite: resulting Fin-indexed nodes remain
injective. The previous identities give an unconditional receiver for each
actual test, including a=0 and N=0 (contraction still holds).

Transport every test in the existing unconditional coordinate dictionary through
this normalization. The verified form-preserving-reencoding theorem supplies
an equivalence preserving balances and canonical weights. Nonnegative canonical
weights and termwise cost contraction give no larger native gauge for every
functional. Thus a minimal dictionary with distinct nodes in every test exists
unconditionally; there is no new producer hypothesis.

## Plan

- [x] Verify finite-fiber and ordered-sum APIs in scratch Lean.
- [x] Prove grouping identity, all-support form preservation, cost contraction,
  and exact equality criterion for positive scales.
- [x] Construct distinct-node actual receiver and normalize full dictionaries.
- [x] Native leaf builds, all-public axiom audit, wiring/freshness/index/lint run.

Three leaves written: `WeilLogShiftGramFiberCost.lean`,
`WeilLogShiftGramNodeCoalescing.lean`, and
`WeilLogShiftGramCoalescedDictionary.lean`. First native leaf passed (exit 0,
empty diagnostic log); actual-node normalization also passed (exit 0, empty
diagnostic log). Its first attempt exposed an unfolding-order mismatch:
global simplification unfolded cost before reindexing. An explicit reindexing
equality fixes this without changing the theorem. Dictionary leaf passed on
its first native build (exit 0, empty diagnostic log). All three oleans are
fresh and all imports occur exactly once in the theorem-area umbrella. API probe
`/tmp/hgt-weil-coalescing-api.lean` passed after adding the ring big-operator
import and explicit universe levels; no mathematical premise changed.

Final audit `/tmp/hgt-weil-coalescing-final-audit.lean` passed (exit 0), covering
all 14 public declarations and 34 API terms. Source-to-audit coverage is complete;
only `propext`, `Classical.choice`, and `Quot.sound` occur, with no diagnostics.
Index refresh passed and exact search finds the unconditional dictionary receiver
at `WeilLogShiftGramCoalescedDictionary.lean:56`. Global lint ran,
with no diagnostics for the new leaves and five unrelated umbrella gaps:
`RHTower.JointAncestryUnitResiduePoleTrace`,
`HTGeometry.PaperMoebiusEulerFactor`, `HTGeometry.PaperMoebiusPrimeClock`,
`HTGeometry.PaperPrimeConstantProjection`,
`HTGeometry.QKrawtchoukCompanionTriangular` (all under GaloisForLFunctions).
Global lint is not clean; unrelated shared-worktree files remain untouched.

## Limits and next frontier

This removes a precisely classified encoding defect. It does not bound total
dictionary cost as cutoff grows, and does not identify representations sharing
a Gram form but different signed node measures. Global cost upper control and
single-test exact-image surjectivity were open at this step. Exact-image
surjectivity is now discharged by the formalized follow-up below; cost growth
control remains open.

Stronger follow-up formalized in
`finite-weil-exact-single-test-image.md`: the actual finite quadratic amplitude
map is surjective on one fixed distinct-node configuration. A positive
balanced dictionary gives a regular zero at the separated block-diagonal
limit; the installed strict-derivative local-surjection theorem supplies the
parameter-stability mechanism. Four native leaves and all 17 public declarations
passed the final Lean audit on 2026-10-10.
