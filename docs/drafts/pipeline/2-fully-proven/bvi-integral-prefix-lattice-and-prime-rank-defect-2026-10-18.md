# Integral prefix lattice and prime rank defect

- **Field:** Bézout–Valuation Incidence Mechanics
- **Type:** THEOREM (core paper proof closed); Lean verification pending; no count credit
- **Source:** The exact real prefix determinant and explicit column operations of
  the initial-prefix observability package.
- **Target:** Determine the integral obstruction hidden by real interpolation.
  A determinant alone is insufficient; seek explicit integral equivalence and its
  prime-by-prime consequences.

## Candidate statements

For the integer Ramanujan prefix matrix on rows `1,…,n` and moduli `2,…,n+1`,
conjecture integral equivalence to `diag(1,2,…,n)`: there exist integer matrices
`U,V` with unit determinants taking the prefix matrix to that diagonal.
This is a diagonal equivalence claim, not a claim that the listed entries already
form the divisibility chain of Smith normal form.

Candidate consequences to audit as one connected package:

- Its integer cokernel is a product of cyclic groups of orders `1,…,n`.
- After reduction modulo a prime `p`, the exact rank loss is `floor(n/p)`.
- More generally, the number of diagonal prime-power obstructions of order at least
  `p^a` is `floor(n/p^a)`. State a precise module invariant before formalizing this.

## Proposed mechanism

The observability proof already uses the floor matrix `floor(m/d)`, lower triangular
with diagonal one. Its column shear and cyclic permutation are integral and
unimodular. The scaled centered-floor matrix therefore has an explicit integral
equivalence to a diagonal with entries `1,…,n`, up to signs and permutation.

The factorization `A=R*T` becomes `B=R*E` after clearing the column denominators,
where `E(e,d)=1_{e|d}` on moduli `2,…,n+1`. This incidence matrix is upper triangular
with diagonal one and should be inverted integrally by the existing Möbius transform.
Transport the same equivalence to the actual Ramanujan primitive matrix. Verify
integrality directly from the existing finite divisor formula; do not introduce an
unrelated surrogate matrix.

For a precise candidate factorization at positive dimension, let `F(m,d)=floor(m/d)`
on `1,…,n`, and let `S` subtract the last column from every preceding column.
Let `P` move that last column to the first position and let `Q=diag(-1,1,…,1)`.
Then the intended identity is `R*E*S*P*Q=F*diag(1,…,n)`. Both `E` and `F`
are integral unitriangular matrices; `S` is unitriangular and `P,Q` are unimodular.
Thus proposed witnesses are `U=F⁻¹`, `V=E*S*P*Q`. Treat dimension zero separately.
This identity remains a paper/formal verification target, not a completed theorem.

## Prior-work audit and gates

- Deep query `Ramanujan primitive integer matrix unimodular diagonal equivalence`
  returned 20 candidates and 20 source arguments, all inspected. Retrieval was
  partial, coverage pending, with a semantic deadline. It gave no exact competing
  integral-prefix classification.
- Focused lexical `SmithNormalForm` returned 41 declarations, all inspected across
  offsets 0, 20, 40. Existing `SmithNormalFormMatrix.lean` provides general integer
  unimodular diagonalization; `SmithNormalFormDVR.lean` provides DVR Smith form and
  cokernel tools. Reuse them where applicable; general diagonalization is not new.
- Relevant corpus sources are under `formal/GaloisForLFunctions/HTGeometry/`.
  Complete the applicability and novelty audit, paper proof, and exact prime-rank
  statement before any new Lean. No numerical computation or experimental evidence.
- The preceding observability package is now verified as contribution 005.
  This candidate is in progress and remains uncounted. Do not count this card or its proposed consequences separately.

## Further uncounted refinement: canonical invariant factors

After proving the integral equivalence for the actual Ramanujan matrix, audit the
candidate Smith chain

`s_j = lcm(1,…,floor(n/(n-j)))`, for `0≤j<n`.

This is a proposed application of diagonal Smith classification, not a claim that
generic Smith theory or the integer sequence itself is new. The symbolic mechanism
is that the `k`-th largest prime valuation among `1,…,n` has size
`max {a : p^a≤n/k}`: exactly `floor(n/p^a)` diagonal entries have valuation at least
`a`. Sorting prime valuations independently gives the displayed chain. A complete
paper proof and corpus audit remain required before any Lean or count credit.

The deep query `Smith diagonal consecutive integers lcm invariant factors` returned
20 candidate lemmas and 20 source arguments; every statement was inspected. It was
partial (generation 1449445 pending; reranking deadline; background refresh active).
No exact Ramanujan-prefix classification was returned. The source-text sweep for
Smith/invariant-factor and lcm/consecutive combinations had one unrelated prose hit.
These searches do not establish novelty outside the local corpus.

A reusable general cokernel theorem was found and its source checked:
`HTGeometry.ConstraintRelativity.nonempty_coker_equiv_pi_of_smith` in
`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SimpleHorizonTransmutation.lean`.
For a commutative ring, unit-determinant matrices `P,Q`, and
`P*M*Q=diagonal d`, it supplies the cokernel equivalence to the product of
`R/(d_i)`. Reuse this theorem; a general cokernel decomposition is prior work.

## Active plan

`update_plan` is unavailable; this card stores the plan. Previous goal turn made
progress by completing contribution 005. Current verified total remains 5 / 250.

1. [x] Renew corpus novelty/API searches, including actual primitive integrality,
   generic cokernel transport, modular rank, and valuation-layer counts.
2. [x] Close a dependency-closed paper proof for the integral classification and
   its exact arithmetic consequences. Audit the canonical Smith refinement.
3. [x] Verify every required toolchain API in scratch Lean, then formalize the
   actual arithmetic matrices and full proved package in the field directory.
4. [ ] Named-source check, all public axioms, umbrella wiring, exhaustive index
   comparison, lint, ledger/memory update, and owned-process/artifact cleanup.

Fresh deep query `Ramanujan primitive integer divisor floor formula unimodular`
completed (session 17017, `/tmp/bvi6-integral-search.json`); results are audited below.
The existing `pmRamanujanPrimitive_eq_floor` expresses the actual complex primitive
as a finite divisor-antidiagonal sum of integer-cast terms, supplying integrality.
Serena symbol lookup refused the field source as ignored; use targeted source reads
for that path without changing ignore configuration.

## Dependency-closed paper proof of the integral classification

The core package concerns the lattice of integer Ramanujan amplitudes, equivalently
weights whose normalized coefficients `c(d)/d` are integers. Do not conflate this
with unrestricted integer raw coefficients: their normalized coordinates can be
fractional. The bridge to the actual arithmetic primitive is essential.

Let `R_Z(m,e)=Σ_{uv=e} u*μ(v)*floor(m/u)`, for rows `1≤m≤n` and columns
`2≤e≤n+1`. The existing primitive floor theorem identifies its real cast exactly
with the already defined Ramanujan prefix matrix. Let `E(e,d)=1_{e|d}` and
`B(m,d)=d*floor(m/d)-m`. Clearing the column denominators in the proved real
factorization `A=R*T` gives `R_Z*E=B`, since the integer-to-real map is injective.
This identifies the lattice with genuine centered-floor observations.

Put `F(m,d)=floor(m/d)` on `1,…,n` and `D=diag(1,…,n)`. Both `F` and `E` are
integral triangular matrices with diagonal one. At positive dimension let `S`
subtract the last column from all preceding columns; its last diagonal entry
remains one. Thus `det S=1`. The last column of `B` is `-m`, by the Euclidean
floor bound `m<n+1`. If `σ` is the forward cyclic column rotation, and `q_j`
is `-1` at the last column and `1` elsewhere, direct column inspection gives

`B*S = F*D*W`, where `W=(1.submatrix id σ)*diag(q)`.

The signed permutation matrix `W` is unimodular. Therefore the explicit integer
matrices `U=F⁻¹` and `V=E*S*W⁻¹` satisfy `U*R_Z*V=D`. The zero dimension uses
empty matrices. Determinants are units at every dimension; all inverses are taken
inside integer matrices, not over the rationals.

For arbitrary integer observations `y`, invertibility of `U,V` gives the exact
solvability criterion `R_Z*x=y` iff `k | (U*y)_k` for every `1≤k≤n`. When these
conditions hold, `x=V*((U*y)_k/k)` is a solution, and it is unique since all
nonzero diagonal entries act injectively on the integers. At dimension `n+2`,
`y=F*e_last` violates the last divisibility condition: `n+2` does not divide `1`.
Thus real interpolation does not imply integral interpolation, with an explicit
positive survivor rather than a bare obstruction: all congruence conditions and
an exact reconstruction map are known.

Existing general cokernel transport gives `coker(R_Z) ≃ ∏_{k=1}^n ℤ/(k)`.
The same unimodular identities survive every base change to a commutative ring.
For any positive modulus `m`, the modular kernel is therefore in bijection with
`∏_{k=1}^n {x : ZMod m | k*x=0}`. The existing cyclic-group multiplication-kernel
cardinality theorem gives the exact count `∏_{k=1}^n gcd(m,k)`.

At a prime `p`, diagonal rank is the number of nonzero residues among `1,…,n`.
The existing exact multiples-count theorem therefore gives rank `n-floor(n/p)`.
More strongly, for every `a≥0`, the actual modular kernel counts satisfy

`|ker R mod p^(a+1)| = p^floor(n/p^(a+1)) * |ker R mod p^a|`.

To see this without numerical evidence, the factor `gcd(p^(a+1),k)` equals
`p*gcd(p^a,k)` precisely when `p^(a+1)|k`, and otherwise equals `gcd(p^a,k)`.
For the latter branch, any divisor of a prime power is a power of that prime;
if the larger gcd had exponent `a+1`, the excluded divisibility would hold.
Multiply these identities and apply the exact multiples count. This states a
precise invariant of the actual operator at every prime-power layer, not just a
count attached to a surrogate diagonal. The canonical lcm Smith-chain display
remains an uncounted presentation refinement; do not claim it formalized merely
from this paper discussion, or count it later as another contribution by itself.

The classification uses ordered Euclidean floor responses and their terminal
column; it is not obtained from multiplicative convolution alone. It makes no
signed cancellation, uniform conditioning, or analytic source-bound claim.

## Current audit evidence

- Fresh integral-primitive deep search: 20 candidates and 20 source arguments,
  every statement inspected; partial, generation 1449527 pending, reranking deadline.
  It recovered the exact primitive floor theorem and no competing integral-prefix
  classification. Existing primitive and Möbius identities remain dependencies.
- Modular-kernel deep search: all 20 candidates and 20 source arguments inspected;
  partial, generation 1449544 pending, semantic timeout. It recovered
  `RHTower.squareResidue_mul_kernel_card`, confirming scalar kernel counting is
  prior work. The generic cyclic-group kernel formula can avoid reproving it.
- Exact rank/count lexical search returned 13 entries, all inspected. Direct installed
  sources supply `Matrix.rank_diagonal`, rank invariance under unit-determinant
  multiplication, and `Nat.card_multiples`. A broad first lexical query was noisy;
  its 20 returned entries were inspected before narrowing the query.
- All scratch drafts use the owned temporary prefix `/tmp/bvi6-*`.
  The completed snapshot and import-closure verification are recorded below.

## Toolchain checkpoint

- Core paper proof closed; no production Lean source yet. Verified total remains
  5 / 250. No count for partial formalization or the canonical display refinement.
- Current root/formal AGENTS, formal README/overview, and all 300 field README lines
  were read. User no-full-build and field-location rules govern. No subagents.
- APFS copy 90477 ended on concurrent artifact deletion. Guarded fill 17210 exited
  0 with all 9,359 project dependencies present. `/tmp/bvi6-formal` uses the complete
  `/tmp/bvi6-olean-cache` snapshot. External Lake build 37778 must remain untouched.
- API check 40257 ended on a missing noncomputable annotation and a nonexistent
  helper name; both fixed. Matrix prototypes 83126, 47173, 45428 ended on local
  elaboration issues, subsequently fixed. In 45428 the complete integer column
  reduction and arithmetic proofs checked except one conditional-entry equality;
  that was fixed in the next run. No mathematical statement was weakened.
- Prototype 59120 reached only missing `Matrix` notation scope and cast-normalization
  errors; both corrected. Prototype 72998 is terminal and its output is empty, but
  its exit-status response was lost during compaction. Do not substitute this for
  the final named-source check. Full scratch Lake PID 40597 and Lean PID 40746
  have now exited. Its output `/tmp/bvi6-proof-check.txt` records only namespace,
  coercion, product-notation, and a diagonal-vector rewrite error. The actual
  integral column reduction, generic kernel transport, and prime-power arithmetic
  were accepted. The reconstruction rewrite was already corrected in the draft.
- Proof segments: `/tmp/bvi6-integer-matrices-body.lean`,
  `/tmp/bvi6-arithmetic-body.lean`, `/tmp/bvi6-kernel-body.lean`,
  `/tmp/bvi6-integral-bridge-body.lean`, `/tmp/bvi6-consequences-body.lean`.
  `/tmp/bvi6-assemble.py` builds the mathlib-only prototype by default, or the full
  project scratch file `/tmp/bvi6-proof.lean` with argument `full`.
- Full bridge and consequence drafts are now written and being checked: actual
  integer primitive/real casts, incidence identity, explicit transforms, exact
  solvability and reconstruction, an integral obstruction with real solution,
  cokernel cyclic factors and cardinality, generic modular kernel equivalence,
  prime-power counts/increments, and prime rank.
- Intended production module: `IntegralPrefixLatticeAndPrimePowerObstructions.lean`
  under the field directory. After focused validation of the local coercion and
  notation fixes, use the final named-source check to validate the corrected whole
  module; avoid a redundant import-heavy full scratch pass. No credit before that
  check, axiom audit, and integration are complete.
- Source inventory: 26 public theorems, 12 public definitions, 19 private theorems,
  and 3 private definitions. `/tmp/bvi6-audit-source.py` constructed the exact
  source manifest and all 38 public axiom probes after promotion.
- The first full scratch pass spent most of its runtime initializing imported
  environment extensions under heavy memory pressure. Focused mathlib-only check
  `43364` now verifies corrected cast bridges and the parenthesized factorial
  product. Output/status: `/tmp/bvi6-bridge-fixes-check.txt` and
  `/tmp/bvi6-bridge-fixes-status.txt`. No mathematical statement was weakened.
- Focused check 43364 isolated one denominator-normalization issue; corrected
  recheck 25541 exited 0 with no diagnostics. All local cast and factorial fixes
  are verified. The production module now exists with 628 lines and no probes.
- Named original-source audit 53487 exited 1 on a single coordinate-rewrite order:
  `Matrix.mulVec_diagonal` is pointwise and must follow `ext i`. Every other
  declaration checked. That local order is corrected; no statement changed.
- Corrected named original-source audit is session `81250`, running in `/tmp/bvi6-formal`
  with `lake --old env lean -j 1 --root=/Users/michael/Documents/code/hgt/formal`
  and explicit `-o` output. Log/status: `/tmp/bvi6-named-check.txt` and
  `/tmp/bvi6-named-status.txt`. Verified contribution count remains 5 / 250.
- Current source SHA-256:
  `325e220a02d88fe3b6cf09574694bc7e0584be403f749c7789016cd809fe3b95`.
  Source manifest and 38 public axiom probes were regenerated after the one-line
  edit. All next-frontier searches are terminal; their findings and the unproved
  translated-window candidate are in
  `docs/drafts/pipeline/0-backlog/bvi-translated-prefix-observability-and-maximal-zero-runs-2026-10-18.md`.
- Final named-source check requires `--root=/Users/michael/Documents/code/hgt/formal`;
  axioms remain in /tmp. Wire, index, lint, audit every declaration, install the
  checked artifact, and clean all owned `/tmp/bvi6-*` paths before counting once.

Exhaustive source-text cross-search for Ramanujan with Smith/unimodular/cokernel/rank
and prefix with Smith/unimodular/cokernel returned three lines, all inspected. They
concern generic prefix descriptions or existing non-integral Ramanujan material,
not an exact competing integral-prefix lattice classification. Search coverage
limitations remain as recorded; no novelty claim beyond the local corpus.
