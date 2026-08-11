# Amplified Generative Response Mechanics Lean core (2026-08-11)

Paper card: `docs/drafts/pipeline/2-fully-proven/universal-law-field/amplified-generative-response-mechanics/amplified-admission-depth-escape-and-reduction-pencil-law.md`.

Lean module: `formal/GaloisForLFunctions/HTGeometry/AmplifiedGenerativeAdmission.lean`, wired into `HTGeometry/UniversalLawField.lean`.

Certified exact laws:
- `rankOneAdmissionPencil_posSemidef_iff`: normalized `c I - r |z><z|` is PSD iff `r <= c` for `r>0`.
- `reductionChoiPencil_posSemidef_iff`: reduction Choi rank-one threshold is `c >= n`.
- `reductionAmplifiedThreshold_false_promotion`: exact profile `min(n,k)` has uniform bound at each fixed depth but no uniform bound on diagonal/cofinal complete depth.

Verification: direct module Lean pass; module build 8657 jobs; UniversalLawField build 11619 jobs; axiom audit only propext/Classical.choice/Quot.sound. New file has no sorry/admit/axiom/opaque/unsafe. Existing global warnings unrelated.

Formal boundary: full intermediate `k`-positive reduction-map theorem remains paper-only. Needs Schmidt/SVD or rank-sensitive trace inequality infrastructure. Do not claim Stage3 credit for intermediate `k` positivity.

Field consequence: GRM selection gate strengthened to coefficient-faithful, completely order-reflecting, uniformly product-admitted transport over routes × apertures × amplification depth. Separate fixed-degree bounds cannot suffice.