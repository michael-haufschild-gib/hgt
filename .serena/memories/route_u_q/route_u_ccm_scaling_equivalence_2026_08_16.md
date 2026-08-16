# Route U exact CCM scaling equivalence (2026-08-16)

New formal module: `formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgeCCMScalingBridge.lean`.

Key result: normalized `2*pi` dilation is a continuous linear equivalence from `SuzukiHlogFormDomain a` onto `CCMArchimedeanFormDomain (2*pi*a)`. Prime translations, Gamma/archimedean block, and polar block all scale by factor two, giving `ccmRestrictedWeilSourceQuadratic (2*pi*a) (D f) = 2 * routeUClosedSourceQuadratic a f`. The Route-U source is also exactly its literal hard-edge density integral plus polar carrier.

Capstones: `routeUCCMFormEquiv`, `routeUClosedSourceQuadratic_eq_density`, `ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector`, `routeUClosedSourceQuadratic_nonnegative_everywhere_iff_ccm`, `routeUClosedSourceQuadratic_negative_exists_iff_ccm`.

Research consequence: unrestricted incoming Route-U PSD is exactly full CCM restricted-Weil positivity, not a smaller benign subspace. Pivot to structure of actual hard-edge root-quotient sequence: source-specific strictness/pre-wall exclusion, not generic PSD.

Direct Lean, exact leaf build, and axiom audit passed; standard axioms only. Wired into `RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/route-u-exact-ccm-scaling-equivalence.md`.