# CHMD finite-divisor realization in the literal jump graph

Status: formalized and audited. RH remains unproved; the overall CHMD goal remains active.

## Structural target

Realize every admissible finite Xi-divisor quotient with polynomial numerator of degree at most the divisor-list length as real and imaginary vectors in the actual full CHMD source graph. Preserve its exact Fourier-factorization identity and obtain approximation by genuine compact smooth tests. No extra graph-domain assumption may remain.

## Prior corpus

- `ThetaZeroDivisionRealization`: explicit `listComb thetaListDivision L e`, theta domination, all exponential moments, exact transform times `listDivisor L` equals `XiC * e(z^2)`.
- `CHMDFullJumpMoment`: finite full prime measure.
- `CHMDFullJumpCoreDensity`: maximal literal graph equals compact-test completion.
- `CHMDCriticalBandReduction`: infinite critical radical and its orthogonal complement; positivity on the complement remains open.

Corpus searches: critical-complement spectral synthesis; theta zero-division graph domain. Both completed with full reported request coverage, stale snapshot/semantic-index warnings; candidates must be checked in Lean.

## Dependency-closed paper argument

Write Phi for the full positive theta source. For real f with |f| <= M Phi, f Lipschitz with constant A, and Phi Lipschitz with constant B, put v=f/Phi. Then |v| <= M and

Phi(x) Phi(y) |v(x)-v(y)|^2
<= 2 M |Phi(y) f(x)-Phi(x) f(y)|
<= 2 M (A+M B) Phi(y) |x-y|.

The archimedean integral is finite because integral_0^infinity t omega(t) dt and integral Phi are finite. The full prime integral is finite because v is bounded and the complete prime edge measure is finite. The mass integral is finite because the full theta-cosh mass measure is finite. Thus v is in the literal full graph.

For any exponential-moment source f, the derivative of `joinedDivision alpha f` on x>=0 is bounded. Each sine/cosine factor at x grows by exp(|Im alpha| x); its tail integral is bounded after multiplication by that factor by integral exp(2 |Im alpha| |t|) |f(t)| dt. The derivative bound is twice |alpha|^2 times this moment. Compose the half-line Lipschitz function with absolute value to obtain globally Lipschitz `zeroDivision alpha f`, including a possible seam at zero. Consequently every theta-list division is Lipschitz. Finite polynomial partial-fraction combinations retain this property. Their real and imaginary parts satisfy the graph criterion above. The existing full-core theorem supplies compact smooth graph approximation, and the existing exact Fourier identity supplies finite-divisor realization without any new analytic premise.

This is a domain bridge for actual divisor sources, not a sign estimate or an RH equivalence. It does not identify their signed pairings with the divisor form or prove positivity of the reduced complement.

## Formalization

1. Done: `ThetaZeroDivisionLipschitz` proves global regularity for every exponential-moment zero division, every finite theta-list division, and every polynomial partial-fraction combination.
2. Done: `CHMDThetaRelativeGraph` admits theta-dominated Lipschitz sources, proves their full signed graph-energy identity, and places them in the closure of genuine compact smooth tests.
3. Done: `CHMDFiniteDivisorGraph` packages real/imaginary representatives and the exact divisor identity for their literal ungauged source. It also gives `exists_exact_zero_division_graph`, an unconditional nonzero instance using an existing positive real Xi zero, with Fourier mass `XiC 0` retained.
4. Done: leaf builds, direct Lean audits, declaration axioms, index/lint, umbrella wiring, scratch cleanup.

## Frontier exposed

Finite divisor sources now have the correct domain for CHMD. The existing strip-multiplier selectors with auxiliary rational poles are a different source class; this result makes no assertion that those selectors have theta-relative graph representatives. The next missing bridge is the exact signed arithmetic pairing on these newly admitted sources, followed by analysis of the nondegenerate complement of the critical radical. No primitive sign claim follows from domain admission alone.

Concurrent, unwired work discovered during lint includes `ThetaBVArithmeticAdmission`, `ThetaBVWeilForm`, and `ThetaQuantileArithmeticForm`. Headers and declaration inventories were inspected: these concern BV profiles, a continuous Weil-form extension with polar moments, and a quantile pullback. They were not built or audited here. Check their finished status before extending the pairing bridge. `CHMDKleinGordonBoundarySingularity` is another concurrent, unwired light-cone leaf; do not infer its completion from its header.

## Audit

- All three new leaves built with `lake --old build <leaf>`; no umbrella/full build.
- Final plain `lake env lean <leaf>` passed for all three leaves with empty output.
- All 23 new declarations audited in a temporary file: only `propext`, `Classical.choice`, `Quot.sound`.
- 95 temporary `have := @Name` probes passed against this toolchain.
- Umbrella imports added for all three leaves.
- `scripts/formal_tools.py index`: exit 0; 13 changed modules, 0 removed.
- `scripts/formal_tools.py lint`: exit 1 solely for six unwired leaves outside this change: `RHTower.CHMDKleinGordonBoundarySingularity`, `RHTower.PaperThetaConfluentArithmeticWork`, `RHTower.ThetaBVArithmeticAdmission`, `RHTower.ThetaBVWeilForm`, `RHTower.ThetaQuantileArithmeticForm`, `HTGeometry.BoundedVariationTranslationIntegral`. Existing large-file warnings remain. No error names a new leaf.
- All 18 owned scratch files removed; absence verified. All owned process handles terminal.
- No web search, numerical experiment, heartbeat increase, extra axiom, commit, or push.

Audited SHA-256:

- `ThetaZeroDivisionLipschitz.lean`: `87e6cec40c5d89591666b805476b60fef2ce2a71119f541b110fa7b156e6f0ed`
- `CHMDThetaRelativeGraph.lean`: `2bb71169fc081e12ebf970c6371ea99bb26df259b034be5dc1c7e9fedf8a6418`
- `CHMDFiniteDivisorGraph.lean`: `65bc8413129559bc8c6a59b53c4fd18b5e68b5cb0433c28317fcc63b03cb4902`
