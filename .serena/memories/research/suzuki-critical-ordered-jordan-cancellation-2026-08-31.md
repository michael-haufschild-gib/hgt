# Suzuki critical ordered/Jordan cancellation route kill (2026-08-31)

Formalized module: `formal/GaloisForLFunctions/RHTower/SuzukiCriticalOrderedJordanCancellation.lean`.
Card: `docs/drafts/pipeline/3-formalized/suzuki-critical-ordered-jordan-cancellation.md`.
Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`.

For source-valid Suzuki cells with endpoint (k=n+3), define
(d_n=k^{-1/2}(I_k-k^{-1/2})). Proved
(|d_n|\le (5/3)k^{-3/2}), hence summability, and the exact identity
(k^{-1/2}c_{k-1}=d_n+1/k-\Lambda(k)/k).
Therefore the natural-order critical prefix converges to
(sum_n d_n+2\gamma-3/2+(\log 2)/2).
Nevertheless the signed critical curvature family, its positive sector, and its negative sector are all non-summable. Capstone:
`suzukiCheckpointCriticalOrderedJordanCancellation`.

Route consequence: scalar natural-order critical checkpoint convergence is unconditional and therefore cannot carry RH. The surviving CCM-FU obligation is the uniform affine/floor-selected checkpoint cancellation before scalarization:
exact cells -> floor-selected affine current -> bounded CCM-FU checkpoint mixture -> `riemannHypothesis_of_ccmFUSuzukiCheckpointAffineMixtureBound` -> RH.

Validation: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.SuzukiCriticalOrderedJordanCancellation` passed; axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. Frontier map remained read-only. No computations or full builds. Repo-wide lint failure was only unrelated concurrently unwired modules. Novelty remains labeled candidate pending external peer review.