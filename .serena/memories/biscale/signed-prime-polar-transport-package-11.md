# Balanced factorial sources: jump-energy cost (package 11, uncounted)

Active lane: unconditional signed prime–polar transport and Chebyshev coupling, independent BiScaleUncertainty. Overall goal remains 100 substantial packages; only 10 verified so far. README is read-only. No RH work, hgtl7, numerical experiments, full/umbrella builds, heartbeat changes, commits, or pushes. One owned foreground Lean process at a time.

Authoritative checkpoint: `docs/drafts/pipeline/1-in-progress/signed-prime-polar-factorial-archimedean-cost-2026-10-17.md`. Dependency-closed paper proof: `docs/reports/BiScaleUncertainty/SignedPrimePolarFactorialArchimedeanCost.md`.

Package target: actual balanced sources P_N,M_N have finite literal jump integrals; explicit lower and upper growth of order sqrt(N) log N; exact E(P)-E(M)=-2 integral H_N w; absolute difference bounded by 2[6log(4N+1)+7+2log(10^6 N^5)]/sqrt(N); normalized logarithmic lower bound. Factor is TWO. No source interfaces, Chebyshev hypotheses, grid blindness or pre-floor divisor counterterms.

Six new leaves have passed direct `lake --old env lean <leaf> -o <olean>` checks: CompactProfileLipschitz, SignedPrimePolarTentRegularity, CompactLipschitzLevyEnergy, SignedPrimePolarRampRegularity, SignedPrimePolarSourceJumpDomain, SignedPrimePolarTentJumpLower. Hashes: `/tmp/spp11-verified-support-manifest.json`. The tent regularity log contains an informational ring suggestion; other listed final logs are empty. SourceJumpUpper passed with unused-tactic warnings; cleaned source awaits recheck. CausalJumpBounds and SourceArchimedeanCertificate are implemented but unverified. Do not count package 11 yet.

Key verified result: actual source admissions and energy sum/difference laws; E(G_N)>=6 exp(-1/2) N log N. Remaining numerical signed bound and normalized assembly must pass, then axiom audit `/tmp/spp11_final_axioms.lean`, import wiring, formal lint, index, ledger/card updates and scratch cleanup.

Lean pitfalls: annotate reciprocal interval integrability with `volume`; minus-source compact-map coercion needs explicit pointwise function equality; avoid rewriting N by sqrt(N)^2 globally (it also rewrites inside sqrt). `abs_ofNat` is unavailable; `abs_sub_le` has three arguments (triangle through an intermediate point); `add_le_add_right` adds on the left in this toolchain. API probes in `/tmp/spp11*_api.lean` have passed.
