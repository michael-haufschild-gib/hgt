# HC77 — HB local analytic-branch optical cancellation no-go

Formalized module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPreDivisorOpticalCancellationLocalAnalyticBranchNoGo.lean`.

Results:
- Exact complex rational continuation `d4PreDivisorOpticalCancellationHolomorphicContinuation`, built coefficient-for-coefficient from complexified horizon shifts/cross numerator/AIME denominator.
- Literal specialization theorem on `Complex.ofReal`.
- Holomorphicity throughout `0 < Re z < 1`, with all denominator roots excluded by strip geometry.
- Unconditional no-go `not_exists_localAnalyticBranch_preDivisorOpticalCancellationSusceptibility`: no scalar function analytic on any nonempty open subset of strip equals exact horizontal cancellation profile there. Domain need not be connected.

Proof mechanism: choose a ball in local branch. Vertical sequence with fixed real part forces local branch constant by analytic identity theorem. Horizontal sequence inside same ball transfers constancy to rational continuation along accumulating real points. Full-strip identity theorem makes continuation constant, contradicting exact quarter/half separation from HC74.

Interpretation: branch cuts/nonisolated singular sets do not rescue scalar pointwise cancellation if any open analytic branch obeys cancellation. Survivors must abandon scalar pointwise cancellation on every analytic branch, change support, depend antiholomorphically, become distributional/operator-valued, or derive different complete augmented-source law.

Audit: direct Lean passed; target-only build 12141/12141; all 3 exported theorem axiom prints report only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired; no module lint finding. Card: `docs/drafts/pipeline/3-formalized/hb-predivisor-optical-cancellation-local-analytic-branch-no-go.md`.