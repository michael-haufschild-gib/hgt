# HC76 — HB optical cancellation on meromorphic regular locus

Formalized module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPreDivisorOpticalCancellationRegularLocusMeromorphicNoGo.lean`.

Novel general package:
- `meromorphicAnalyticLocusRegularization f p z`: retains `f z` where `f` is analytic, inserts continuous profile `p z` elsewhere.
- `meromorphicAnalyticLocusRegularization_eq_profile`: if `f=p` at every analytic point in open set `U`, regularization equals `p` everywhere in `U`.
- `analyticOnNhd_meromorphicAnalyticLocusRegularization`: for meromorphic `f` and continuous `p` on open `U`, regularization is analytic throughout. Proof uses `MeromorphicAt.eventually_analyticAt` to show punctured-germ equality with `f`, `MeromorphicAt.congr`, local profile equality for continuity, then `MeromorphicAt.analyticAt`.
- `not_exists_meromorphic_regularLocus_preDivisorOpticalCancellationSusceptibility`: no meromorphic scalar response can equal HC74 optical cancellation profile merely on its analytic locus; pole values are fully unconstrained.

Interpretation: genuine isolated Green/QNM poles do not save source-global scalar optical cancellation. Survivors must lose meromorphy (branch/nonisolated singularity), lose regular-locus equality, change support, use antiholomorphic dependence, or be operator-valued. Does not derive full augmented Einstein coefficient or exclude divisorwise interpolation.

Audit: direct Lean passed; target-only build 12140/12140; all 3 theorem axiom prints report only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired; no module lint finding. Card: `docs/drafts/pipeline/3-formalized/hb-predivisor-optical-cancellation-regular-locus-meromorphic-no-go.md`.