# LI-CAB9 coefficient-recovering regularization no-go (2026-08-29)

Formalized route kill in `formal/GaloisForLFunctions/RHTower/LiEvenCrossCompletedAbelCoefficientRecoveringRegularizationNoGo.lean`; wired into `formal/GaloisForLFunctions/RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/li-even-cross-coefficient-recovering-prefix-regularization-no-go.md`.

Killed exact chain: coefficient-recovering adaptive finite critical prefix + `o(n)` residual -> interior completed-Abel current nonnegative -> LI-CAB5 -> LI-CAB3 -> RH.

Main result: arbitrary mode-dependent weights `w m i -> 1` (no positivity, early boundedness, uniform rate, or frequency-independence assumption) leave a nonempty finite genuine critical packet with cofinal linear excursions of both signs. Hence any all-mode nonnegative repair has cofinally linear positive countercurrent; no sublinear residual works. Capstone: `not_exists_nonempty_finiteCriticalPacket_coefficientRecoveringRegularization_sublinearRepair_all_nonnegative`. Sharp survivor: cancellation must remain genuinely infinite before the Li-mode limit, or contribute cofinally linear countercurrent.

Verification: direct `lake env lean` passed; targeted build passed; all exported proof theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. Repository lint reports 23 unrelated pre-existing unreachable modules, but no issue for LI-CAB9. External novelty remains `NOVELTY UNVERIFIED` after bounded primary-literature audit.

Do not claim full LI route killed. Frontier map is user-declared read-only and was not edited.