# Canonical Krein–Cayley cascade no-go (2026-08-23)

Created `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingKreinCayleyCascadeNoGo.lean`, wired in `RHTower.lean`, documented under current route state in `docs/reports/endpoints.md` without changing positive endpoint counts.

Strong result: quadratic delayed source-to-terminal onset does not require hand-inserted `lambda^m`. Cascade two primitive real-slice bosonic SU(1,1) Krein–Cayley cells. Each local cell has pair coefficient `p(lambda)=2lambda/(1-lambda^2)` and `p'(0)=2`; cascade terminal amplitude is `p(lambda)^2=4lambda^2/(1-lambda^2)^2`, has zero first jet, is nonzero for every nonzero disk coupling, preserves three-mode signature (+,-,+), and supports exact Hawking KMS detailed balance. Main theorem: `canonicalKreinCayleyCascade_lossless_KMS_mixing_not_force_firstOrder`.

Interpretation: canonical completion + source-linear local cells + Krein conservation + KMS + finite-coupling connectivity cannot force first-order tilted-sector mixing. Exact RH-bearing survivor is theta-specific direct one-step observability/source adjacency of every noncentral tilted sector. Generic connectedness, Markovity, bicausality, total positivity, KMS cocycles, or finite-mass mirror backreaction do not derive it.

Verification: direct Lean check passed; targeted module build passed; axiom audit of explicit terminal formula and main no-go uses only `[propext, Classical.choice, Quot.sound]`. Formal lint reports only unrelated unreachable modules `CayleyChebyshevSource` and `CesaroSignRecurrence`. Temp files removed. No git used.

Related memories: `mem:research/hawking_full_mirror_krein_cayley_endpoint_2026_08_23`, `mem:research/hawking_full_mirror_weak_coupling_order_endpoint_2026_08_23`, `mem:research/hawking_markov_coupling_order_no_go`.