# HC75 — HB pre-divisor optical-cancellation meromorphic removability

Formalized module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPreDivisorOpticalCancellationMeromorphicRemovability.lean`.

Core results:
- `continuousAt_d4PreDivisorOpticalCancellationSusceptibility_re`: exact HC74 rational profile pulled back by `Complex.re` is continuous at every open-strip point; proof uses strict positivity/nonvanishing of both horizon shifts.
- `analyticOnNhd_of_meromorphicOn_eq_d4PreDivisorOpticalCancellationSusceptibility_re`: any `MeromorphicOn` scalar function agreeing with the finite profile at every strip point is analytic throughout; local exact equality transfers continuity, then corpus theorem `MeromorphicAt.analyticAt` removes each singularity.
- `not_exists_meromorphic_preDivisorOpticalCancellationSusceptibility`: HC74 holomorphic obstruction then excludes the candidate.

Interpretation: merely declaring the source-global HB cancellation coefficient meromorphic does not escape HC74 when finite values are prescribed everywhere. Survivors must retain genuine undefined/blow-up points, branch/nonisolated singularity, antiholomorphic dependence, support discontinuity, or operator-valued structure. Discrete Xi interpolation remains outside scope.

Audit: direct Lean passed; target-only build passed 12139/12139; all 3 theorem axiom prints report only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint has no finding in HC75 and remains nonzero only for unrelated shared-worktree unreachable modules. Card: `docs/drafts/pipeline/3-formalized/hb-predivisor-optical-cancellation-meromorphic-removability.md`.