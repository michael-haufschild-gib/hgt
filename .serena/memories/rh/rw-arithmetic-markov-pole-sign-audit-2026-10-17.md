# RW arithmetic Markov/pole sign audit — 2026-10-17

RW remains open; NO qualifying contribution credited. Own card: docs/drafts/pipeline/1-in-progress/rw-arithmetic-markov-pole-sign-2026-10-17.md. Do not count a new capacity receiver, better bound, ground-state restatement, or existing positive decomposition as progress satisfying the cross-route goal.

Evidence restricted to local Lean and documented research search; no external search, historical research Markdown, numerical experiments, or repository Lean edits.

Ten mechanisms inspected:
1. Exact Weil split is M_N + C^2/2 - S^2/2. Positive jump measures leave a signed creation term. On even tests Q=M+C^2/2 already equals W; matrix inverse capacity needs an unproved positive background.
2. Modulus lowers M but raises the pole term; no full-form ground selection follows.
3. Theta harmonic cancellation already exists. Even Doob transform retains negative cosh mass.
4. Odd theta profile has positive sinh source and absorbed archimedean kernel, but reflected prime terms are singular to positive jumps. Strictly positive scalar gauges cannot absorb the first-prime negative measure.
5. Positive survivor is already formalized: collar diagonal minus reflected difference equals positive prime-crossing energy; complete divisor-cut expansion is strictly positive for nonzero compact odd tests. Full source still subtracts cosh mass.
6. Nonnegative/unimodal cone results do not select actual grounds. Concurrent untracked CHMDOddBoundStateSignObstructionAndParityQuarterBound.lean was inspected read-only: its orthogonality law excludes one-signed odd supercritical bound states, without proving positivity preservation. Do not treat that concurrent file as this turn's work.
7. First-contact null vectors are exact operator-kernel vectors in the completion, but not strict smooth interior vectors. Positive dense approximants need not rule out null limits.
8. Real-rooted full grounds already exist at every aperture. Downstream strip-growth, moment, mass-overlap, convergence assumptions remain substantive. Polar multiplicity equals parity crossing.
9. Strict constrained aperture decrease already proved by translation independence and compactness. Positive survivor is unique-zero classification; strict decrease does not exclude crossing.
10. Clock commutator identity retains signed cumulative source. Finite-prime torque retains signed even/odd overlap; free cosh/sinh positivity is not actual-ground positivity.

Key source modules: WeilMarkovPoleCapacity; WeilMarkovOneBoundState; CHMDThetaHarmonicIdentity; WeilPhiDoobGroundStateCancellationAndShortSupportNoGo; CHMDOddHarmonicIdentityAndPolarDoobAbsorption; CHMDPrimeDivisorCuts; CHMDReflectedPrimeSingularPart; CCMRestrictedWeilFullFormRealRootedGround; CCMRestrictedWeilGroundParityCrossing; CCMRestrictedWeilPolarStrictDomain; CCMFirstContactSourceKernel; CCMRestrictedWeilFullTranslationSaturation; CCMGuinandWeilClockCommutator; SuzukiWeilPrimeCommutatorTorque.

Actual-head L2 admission and cancellation are already closed in CCMRestrictedWeilActualHeadCompletedErrorProducer. CCMActualHeadSignedCompletedErrorGammaProducer identifies the signed producer with source minus scalar Gamma and proves canonical-head convergence; the scalar-shifted threshold is the remaining ground sign. Unsigned reciprocal-Gamma chi-square envelope diverges.

Searches: three deep searches, budget 300 seconds each. First and third partial=false/no errors (73,150 / 73,152 files); second partial=true due malformed local-model judge JSON (73,152 files). Candidate lemmas, source arguments, ingredient sets inspected. Proposed sets retain unknown sign hypotheses. Compiler index mostly pending/stale; actual local source used. Background index refresh incomplete; no service restart.

Verification: `lake --old env lean /tmp/hgt_rw_audit.lean` exited 0. All 20 axiom reports use only propext, Classical.choice, Quot.sound; no errors/warnings. Import/name/axiom audit only, not a source rebuild or new proof. All 10 directly imported .olean files were no older than source. No repository Lean changes; no new umbrella/index work. Audit process exited. All five owned search/audit scratch files removed and absence verified. Goal remains active/incomplete; RW audited, not retired.
