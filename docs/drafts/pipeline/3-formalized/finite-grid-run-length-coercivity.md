# Finite divisor grids and longest-run Dirichlet coercivity

- **ID:** finite-grid-run-length-coercivity
- **Stage:** 3-formalized
- **Type:** PROVED
- **Statement:** The longest consecutive active run determines the exact joint
  trace-extension constants for any finite nonempty family of divisor grids.

Dependency-closed proof: `docs/reports/BiScaleUncertainty/FiniteGridRunLengthCoercivity.md`.
The masked successor is an actual contraction, nilpotent at the longest run;
the existing sine theorem supplies sharp factors. Finite sine packets attain
both, and unit-cell synthesis supplies infinite convergence and every trace.
All eight direct leaf checks and all 124 public-declaration axiom audits pass.
Count this connected package once: current certified count is 13/100.

Trap 10 constraint: this package must construct the actual interpolant and prove
its error/energy bounds, not introduce a receiver with an unproved analytic
input. The unit-cell construction and unconditional mismatch identity meet
that paper obligation. No floor summation or Chebyshev receiver is used.

Use actual spacings `{d+2} ∪ {e+2 : e∈D}`, with d:ℕ and D:Finset ℕ, so neither
nonemptiness nor spacing at least two is an additional admission hypothesis.
Let U be their positive divisible nodes and L their least common multiple.
Construct r as the maximum length of a consecutive active run in one period.
The nodes congruent to 1 modulo L are inactive, and the paper proof gives 1≤r<L.

For actual ℓ² union data v, with every off-union integer trace fixed to zero,
construct the infinite physical L² tent extension E_U and prove

    (2−2 cos(π/(r+1))) Σv² ≤ ‖E_U(v)‖²
      ≤ (2+2 cos(π/(r+1))) Σv².

Both constants are attained on a run of length r, by the first path sine
mode and its alternating-sign counterpart. Prove exact adjacent energy,
closed range, all integer/logarithmic traces, and exact minimum-energy defect.
Recover the two-grid cases r=1,2,3 as arithmetic specializations, not as separate
contributions. All statements are Lean-certified as one package.

Mechanism to audit: integer hats have diagonal Gram entry 2, adjacent entry −1,
and zero otherwise. Disjoint active runs give finite path blocks. An arbitrary
number of grids can defeat a naive sum of pairwise angle estimates, while the
successor path still has degree at most two. Prove the actual block decomposition
and trigonometric extrema; do not assume a spectral gap or summability interface.

Corpus check: `finite divisor grid consecutive interpolation stiffness --any`,
60-second hybrid request. All 20 candidate lemmas and 14 source arguments were
inspected. Results include the new two-grid construction and unrelated signed
correlation bounds, no finite-grid longest-run theorem. Partial=true with
interrupted text/source retrieval, older coverage snapshot, semantic coverage
unmeasured and background refresh incomplete. Recheck corpus and primary path
spectral theory before proof or Lean. Search limitations do not establish novelty.

Dependencies: actual unit-cell Hilbert synthesis and the existing finite scalar
sine certificate/nilpotent-contraction bound. Their APIs and the concrete
nilpotence/contraction instantiation check in this toolchain. No numerical
experiment or computational proof shortcut is used.

## Formalization gates

- [x] `FiniteGridRunLength.lean`: positive bounded maximum, attained in one period.
- [x] `SuccessorSequenceHilbert.lean`: actual isometric right shift, successor
  adjoint, contractive coordinate mask. Direct check clean.
- [x] `IntegerHatTraceExtension.lean`: actual infinite interpolation, all positive
  integer/log traces, adjacent energy, unconditional mismatch and unique minimum.
- [x] `FiniteGridTraceData.lean`: constructed closed union-data domain, every
  nonnegative integer trace, exact energy and minimum-energy wrapper. Direct check clean.
- [x] `FiniteGridTraceStability.lean`: actual masked-shift nilpotence, sine bounds,
  injectivity and closed range. Direct check clean, including a theorem on
  arbitrary ambient ℓ² input through constructed coordinate masking.
- [x] `FinitePathSinePackets.lean`: actual finite interval data, exact norm and
  adjacent pairing, sine recurrence identity and alternating-sign counterpart.
- [x] `FiniteGridTraceSharpness.lean`: actual nonzero longest-run packets attain
  both factors. Direct check clean.
- [x] `FiniteGridTwoSpacingRuns.lean`: unconditional two-grid run classifier and
  recovered constants. Direct check clean; forced alternation avoids exhaustive
  case splitting within the existing heartbeat limit.
- [x] Final serial leaf checks, exact 124-declaration axiom audit, eighteen
  principal signatures and 35 mathlib probes; only standard Lean axioms.
- [x] Eight unique umbrella imports and 123 supported API rows at exact locations.
- [x] Formal lint run; fourteen unrelated concurrent unreachable modules and
  generated-file drift remain global limitations. No package/proof-debt error.
  Index refreshed afterward; own entries reverified.
- [x] Scoped whitespace, source/output freshness and exact stage transition.

Normal-output build logs: `/tmp/finite-grid-run-build.log`,
`/tmp/successor-sequence-build.log`, `/tmp/integer-hat-build.log`,
`/tmp/finite-grid-data-build.log`, `/tmp/finite-grid-stability-build.log`.
Final audit: `/tmp/finite_grid_axioms.lean`, `/tmp/finite-grid-axioms.log`,
`/tmp/finite-grid-audit-names.json`; exact source-name coverage verified.
Other leaf logs: `/tmp/finite-path-sine-build.log`,
`/tmp/finite-grid-sharpness-build.log`, `/tmp/finite-grid-two-spacing-build.log`.
Index/lint evidence: `/tmp/finite-grid-index-post-lint.log`,
`/tmp/finite-grid-api-entries.txt`, `/tmp/finite-grid-lint-final.log`.
The root goal remains active at 13/100. This turn is progress.

Next unproved candidate: `../0-backlog/infinite-divisor-run-gap-classification.md`.
