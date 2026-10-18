# Integral prefix lattice and prime-power obstructions

- **ID:** bvi-integral-prefix-lattice
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Contribution:** 006; one connected contribution. Verified total: **6 / 250**.
- **Source:** The exact initial-prefix observation matrix and determinant theorem,
  contribution 005, together with existing integral cokernel transport.
- **Statement:** The actual integer Ramanujan prefix matrix is explicitly
  unimodularly equivalent to `diag(1,...,n)` at every dimension.

## Mathematical result and scope

The reduction gives every congruence obstruction to integer interpolation, a
canonical reconstruction whenever the congruences hold, and uniqueness. An explicit
integer datum has a real solution but no integer solution at every dimension at
least two. The positive result completely classifies the obstruction.

The cokernel is `∏_{k=1}^n ZMod k`, of cardinality `n!`. Base change preserves the
reduction over every commutative ring. For every positive modulus `m`, the kernel
has cardinality `∏_{k=1}^n gcd(m,k)`. For every prime `p` and exponent `a≥0`, this is
`p^(Σ_{r=1}^a floor(n/p^r))`; the rank modulo `p` is `n-floor(n/p)`.

These are unconditional finite statements, including empty dimensions and modulus
one. The diagonal entries are not asserted to form a Smith divisibility chain.
The lattice concerns integer Ramanujan amplitudes, equivalently integer normalized
weights `c(d)/d` on the nonconstant tail, rather than unrestricted integer raw weights.

## Dependency-closed paper proof

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

## Prior-work and novelty audit

- The initial deep integral-equivalence query and the fresh primitive-floor query
  each returned 20 candidate lemmas and 20 source arguments; every returned
  statement was inspected. Retrieval was partial, with pending coverage and
  semantic/reranking deadlines. No exact competing integral-prefix classification
  was returned. The actual primitive floor formula and earlier field bridges are
  reused dependencies.
- The focused lexical Smith search returned 41 declarations, all inspected across
  three pages. Existing general Smith/DVR results are not new contributions.
- `HTGeometry.ConstraintRelativity.nonempty_coker_equiv_pi_of_smith` in
  `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/SimpleHorizonTransmutation.lean`
  was checked in source and reused for cokernel transport.
- The modular-kernel deep search returned 20 candidates and 20 source arguments,
  all inspected; it was partial, with pending coverage and semantic timeout.
  Scalar multiplication-kernel counting is prior work. The proof reuses
  `IsAddCyclic.card_nsmulAddMonoidHom_ker`.
- The exact rank/multiples lexical search returned 13 entries, all inspected.
  Installed sources and scratch probes verified the actual toolchain APIs.
- The exhaustive source-text cross-search for Ramanujan/prefix with
  Smith/unimodular/cokernel/rank returned three unrelated lines; their local source
  statements were checked. Search limitations do not establish novelty outside
  the local Lean corpus. No external research or numerical experiments were used.

## Verification

- Source:
  `formal/GaloisForLFunctions/BezoutValuationIncidence/IntegralPrefixLatticeAndPrimePowerObstructions.lean`.
  It has 628 lines: 26 public theorems, 12 public definitions, 19 private theorem
  helpers, and 3 private definitions. All 60 declarations form one contribution.
- Final named original-source audit:
  `lake --old env lean -j 1 --root=/Users/michael/Documents/code/hgt/formal -o ... <original-source>`;
  exit 0, no warnings or diagnostics. No full-project or umbrella build.
- All 38 public declarations were audited with `#print axioms` in `/tmp`.
  All 26 public theorems depend on exactly `propext`, `Classical.choice`,
  and `Quot.sound`; definitions use subsets of those axioms. No unexpected output.
  Raw audit: `logs/bvi-root-2026-10-18-integral-prefix-axioms.txt`.
- Source SHA-256:
  `325e220a02d88fe3b6cf09574694bc7e0584be403f749c7789016cd809fe3b95`.
- The checked artifact was installed atomically, is newer than the unchanged
  source, and has SHA-256
  `eb5fd38addb820656b5525cfd45b1a6cbc524fcaa419c0e9fe7ee2f1e3c1ad2c`.
- Guarded `scripts/formal_tools.py index` exited 0. Three focused lexical pages
  returned exactly 60 declarations; every name, visibility/kind, line, module,
  and source path matched the source manifest. This module is imported once.
- At the inventory check, 12 of 13 field modules were wired. A concurrent foreign
  `PrimeTailCalibrationAndMobiusDefect` module was not yet wired; it was untouched.
- Guarded `scripts/formal_tools.py lint` exited 1 solely on two unrelated missing
  umbrella imports: `BiScaleUncertainty.StationaryResolventMarkovPositivityAndNodalDefectProducer`
  and `BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect`.
  No finding names this module and no proof-debt error was reported. Global lint
  is not passing; this is a scoped formalization result.
- Another agent was rebuilding shared compiled imports. Checks used a complete
  isolated snapshot of all 9,359 inherited project dependencies, while checking
  the original named source with the installed toolchain. No foreign process or
  dependency source was changed.
- All owned processes reached terminal status. Guarded cleanup exited 0, removed
  all 56 owned temporary paths, and reverified source and installed artifact hashes.
  The raw axiom audit was preserved. Whitespace check passed. No commits or pushes.

## Uncounted refinements and next question

The proposed canonical Smith display
`s_j=lcm(1,...,floor(n/(n-j)))`, for `0≤j<n`, remains an unformalized presentation
refinement. Its earlier deep search returned 20 candidates and 20 source arguments,
all inspected, with partial coverage. Do not count a future display of that chain,
a general Smith theorem, or a direct restatement of the present classification as
another significant contribution.

The common-return continuation is now formalized as contribution 007:
`docs/drafts/pipeline/3-formalized/bvi-translated-prefix-observability-and-maximal-zero-runs-2026-10-18.md`.
The remaining arbitrary-phase conjecture is isolated at
`docs/drafts/pipeline/0-backlog/bvi-arbitrary-phase-observation-horizon-2026-10-18.md`.
No credit is assigned to that open extension; its lower-bound family is part of 007.

## Gates

- [x] Well-posed statement and local corpus audit.
- [x] Dependency-closed paper proof, including the positive obstruction classification.
- [x] Exact Lean formalization, named-source/axiom audits, wiring, index, and scoped verification.
- [ ] Publication-ready standalone exposition and external novelty review.
