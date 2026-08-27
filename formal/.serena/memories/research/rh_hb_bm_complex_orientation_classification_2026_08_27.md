# HB BM complex-orientation classification (2026-08-27)

New formalized module:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicComplexOrientationClassification.lean`
- Card: `docs/drafts/pipeline/3-formalized/bm-second-harmonic-complex-orientation-classification.md`
- Umbrella `formal/GaloisForLFunctions/RHTower.lean` imports module.
- Frontier map is user-designated READ ONLY and was not modified.

Corpus-derived exact classification:
- Define `λ_n(q)` as BM complementary exponent and current `J_n(q)=-λ_n(q)`.
- `Im λ_n(q)=Im q`, `Im λ_n(Jq)=-Im λ_n(q)≠0`; both exponent real parts are positive.
- Ordered complex cancellation `aJ(q)+bJ(Jq)=0` iff `b=a r_n(q)`, where `r_n(q)=-λ_n(q)/λ_n(Jq)`.
- `Im r_n(q)≠0`: ratio is genuinely complex on every Xi fibre.
- Consequently all signed real weights cancel only at `a=b=0`.
- Complex cancellation exists with weights `(1,r_n(q))`.
- Reflection reverses ratio: `r_n(Jq)=r_n(q)⁻¹`.
- One fixed ordered complex weight pair cancelling both q and Jq is trivial.

HB consequence:
Hermitian/nonnegative, signed-real, and fixed bioriented incidence classes are exhausted. Surviving augmented Peierls incidence must be divisor-dependent, reflection-covariant, and genuinely complex.

Verification:
- direct `lake env lean` passed
- targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicComplexOrientationClassification` passed (11883/11883)
- all 9 exported theorems: only `propext`, `Classical.choice`, `Quot.sound`
- axiom scratch deleted
- external primary-source searches found no exact analogue; priority remains provisional.

Next research:
Use exact ratio as target law for actual augmented Einstein–Teukolsky/Peierls source incidence. Need derive or refute whether source pairing coefficients transform with `r_n(q)`; scalar/fixed real laws cannot.