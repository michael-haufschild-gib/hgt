# PW-B exact joint-source Schwarz covariance

- **Route:** PW-B
- **Status:** formalized Lean premise
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceSchwarz`

`timeReducedCoefficient_conj` proves, unconditionally, that conjugation of the
literal original-time residual source is the same source at conjugated spectral
rate and amplitude. Its proof unfolds the actual reduced polynomial and
coefficient, retaining the positive-radius complex-power branch, both radial
derivative polynomials, and the differentiated causal onset.

**Proof-chain consequence:** one source leg is Schwarz covariant. Remaining
PW-B work is physical-rate transport into the two-event density, ordered
product-measure integration, then the already-reduced critical-fibre
cancellation; no PW magnitude identity is claimed.

**Verification:** `lake env lean
GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMJointSourceSchwarz.lean` passed.
The module is wired into `RHTower.lean`. Its targeted `lake build` was stopped
after it replayed over 12,000 unrelated modules; no umbrella build was run.
