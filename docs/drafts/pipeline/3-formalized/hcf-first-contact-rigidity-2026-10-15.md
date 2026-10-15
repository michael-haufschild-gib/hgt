# HCF first-contact rigidity

Status: formalized; all new leaf builds, final direct Lean audits, and axiom
audits pass. Global lint has unrelated concurrent-work blockers listed below.

Objective: prove one unconditional structural advance beyond the completed
single-transition theorem. A bound, RH equivalence, conditional receiver, or
reformulation of the remaining sign problem does not qualify.

Plan:
1. Search current Lean corpus for the exact remaining HCF obstacles and useful
   mechanisms elsewhere in the corpus.
2. Conjecture, attack, record failure and its positive mathematical survivor;
   continue until a dependency-closed structural contribution is proved.
3. Formalize the successful theorem without added assumptions or axioms.
4. Run focused foreground builds, final direct Lean audits, wire umbrellas,
   regenerate index, run lint, and remove owned scratch artifacts.

Starting point: `XiGaussianHeatWindowExactTransition` now proves a unique
possible heat-window transition. `CCMRestrictedWeilEvenStrictDomain` supplies
strict decrease of the actual even polar ground. Neither excludes a finite
transition or determines its critical window. This task must go beyond those
completed results.

Constraints: corpus evidence only; no web, old research markdown, external
novelty audit, or numerical experiments. No full/umbrella builds, no heartbeat
increases, no commits. Preserve concurrent work.

Conjecture ledger:
1. Ground simplicity from the existing polynomial generator classification.
   NOT PROVED: the classification explicitly permits derivative chains and
   multiplicity. Pole-source nonvanishing is nonvanishing on the whole constrained
   sector, not on each ground. It cannot justify injectivity of ground forcing.
2. Scalar threshold transfer or compact completion might resolve the source sign.
   REJECTED AS THE OBJECTIVE: corpus already contains these receivers/equivalences;
   their sign premise remains the arithmetic obstacle.
3. Singular Hankel sections admit an exact look-ahead block factorization.
   PAPER MECHANISM FOUND: first nonzero coupling of a monic orthogonal polynomial
   produces a nondegenerate anti-triangular block. General all-time Frobenius
   factorization would remove generic-pivot assumptions, but is not yet proved.
4. The actual heat flow forbids a degenerate lower head at first contact.
   PAPER PROOF AND LEAN FORMALIZATION COMPLETE. If the size-N section is positive
   definite for 0<t<T, take a nonzero polynomial p of degree at most N-2.
   Set f(t)=H_t(p,p). The heat derivative chain gives f'=-H_t(p,Xp)
   and f''=H_t(Xp,Xp). Positivity on span(p,Xp) gives f f''-(f')²>=0.
   Thus f'/f increases. A fixed interior tangent gives an exponential barrier
   preventing f(T)=0. Therefore the size-(N-1) head is positive definite at T.
   The singular size-N section consequently has a unique terminal-normalized
   null polynomial. Existing finite moment quadrature then gives distinct real
   nodes with positive weights, exactly matching the visible moments.
   This is a producer of regularity for actual first contacts, not an assumed
   minimal-face hypothesis. The source orientation at that null line remains
   a separate unresolved question. The formalization also constructs first
   contacts from initial HCF positivity and any later failure, without an RH
   premise, and proves strict ordering of successive contact times.

Search audit: first deep query completed with full file inventory but unmeasured
semantic coverage; spectral query was partial (semantic deadline/model JSON
failure). Used available Lean hits and followed with lexical queries/source
reads. No search suggestion is treated as a proof certificate.

Formalization checkpoint:
- `HTGeometry/LogCurvatureEndpointRigidity.lean` compiled in scratch and in a
  focused `lake --old build +...:olean` (2,130 dependency jobs, new leaf 10s).
- Actual HCF moment derivative chain, finite-section Cauchy--Schwarz, and endpoint
  head rigidity passed `lake env lean /tmp/hcf2_heat_core.lean`. The finished
  source is `RHTower/XiGaussianHeatEndpointRigidity.lean`; its focused `--old`
  build passed after narrowing the generic moment import (229s for the leaf).
- Full first-contact construction, canonical null line, strict successor order,
  and positive quadrature passed `lake env lean /tmp/hcf2_contact.lean` with no
  warnings. Finished source: `RHTower/XiGaussianHeatFirstContact.lean`.
  Its focused `--old` build passed (39s for the leaf); both new route leaves and the generic
  endpoint lemma are wired into their umbrellas without umbrella builds.
  The final `hcf_first_contact_resolution` statement has no RH, source sign,
  determinant nonvanishing, or contact-existence premise: every rank either
  remains positive at all positive times or produces the full contact package.

The theorem does not assert transversal contact or a favorable arithmetic
orientation. It removes multi-dimensional and lower-head degeneracy at actual
first contacts, rather than assuming those away in a source-sign receiver.

Exact new structural statement: for every rank `n+1`, either the actual heat
section is positive definite for all positive times, or it has a first contact
whose head of size `n` is positive definite, whose entire kernel is one line,
and whose terminal-normalized null polynomial has exactly `n` simple real roots.
Positive quadrature on those roots reproduces the moments through degree `2n`.
The first contact of rank `n+2` exists and occurs strictly earlier. The theorem
constructs these objects without RH, a source sign, or a genericity premise.

Why this advances the route: existing generic finite boundary quadrature needed
head positivity; existing heat-ladder sign counting avoided singular pivots by
choosing generic times. The heat derivative chain now proves regularity at
every first contact, including the singular times relevant to positivity loss.
This excludes simultaneous first contacts and higher-dimensional first kernels.
It does not prove simplicity of the infinite restricted Weil ground or orient
the completed prime--Gamma source at the remaining one-dimensional contact.

Final audit:
- Focused foreground `lake --old build +<module>:olean` passed for all three
  new leaves. No full or umbrella build was run.
- Final `lake env lean` passed on the actual tree files
  `HTGeometry/LogCurvatureEndpointRigidity.lean`,
  `RHTower/XiGaussianHeatEndpointRigidity.lean`, and
  `RHTower/XiGaussianHeatFirstContact.lean`, with no output or warnings.
- A separate `/tmp` audit printed axioms for the generic endpoint lemma, the
  actual head-rigidity theorem, the first-contact structure theorem, strict
  successor order, positive quadrature, and the unconditional resolution.
  All six use only `propext`, `Classical.choice`, and `Quot.sound`.
- No added axioms, unproved declarations, numerical experiments, heartbeat
  increases, or recursion-limit changes. Scoped whitespace audit passes.
- Each new leaf has exactly one import in its theorem-area umbrella.
- Formal index regeneration passed. `formal_tools.py lint --check-generated`
  failed on two unrelated unimported concurrent modules:
  `CHMDKleinGordonSeparationLawAndApproximateRealisation` and
  `CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion`. It also detected
  concurrent drift of `formal/LEAN_API.md` after regeneration. No new HCF
  module was reported. Generated files were refreshed successfully once more
  after recording this audit. Other workers' unfinished modules were preserved.

Main entry: `RHTower.hcf_first_contact_resolution` in
`formal/GaloisForLFunctions/RHTower/XiGaussianHeatFirstContact.lean`.
Core new mechanism: `RHTower.heatMoment_head_posDef_at_endpoint` in
`formal/GaloisForLFunctions/RHTower/XiGaussianHeatEndpointRigidity.lean`.
Owned temporary proof, search, build-log, and audit files are removed after
these results are recorded. No commits or pushes were made.
