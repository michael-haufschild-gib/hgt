# Route O actual-head Γ-wall outgoing producer (2026-08-18)

Created `formal/GaloisForLFunctions/RHTower/CCMActualHeadGammaWallOutgoingProducer.lean`, wired into `RHTower.lean`.

New exact laws:
- `ccmGammaTranslationDensity = exp(-h/2) + ccmGammaHigherBinetModeDensity`, with higher density exactly Binet tail n>=1.
- first Γ scalar kernel is real Suzuki Cauchy-wall phase Gram at separation h; scalar bridge only, no operator identification.
- for aperture head f, E_f(h)=2||f||² for h>2a.
- first Γ energy = compact decaying polar energy + `2 exp(-a) E_f(2a)`.
- polar debt = outgoing growing energy + compact first-mode energy.
- endpoint coefficient collapse: `criticalMellinCompletedError(2a)+2exp(-a)=2exp(a)-criticalMellinPrimeMass(2a)`.
- defined `ccmRestrictedWeilActualHeadGammaWallOutgoingProducer`:
  higher Γ + outgoing arithmetic endpoint + reflected prime wall chord energy - growing polar continuum, plus scalar Gamma term.
- proved producer = prior wall-Gram producer = source quadratic; canonical ground+tail identity; reverse-prime iff producer nonnegative.

Paper/frontier record appended to `docs/drafts/pipeline/1-in-progress/ccm-canonical-head-completed-error-producer.md`. Route map untouched.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadGammaWallOutgoingProducer.lean` passed.
- targeted `lake build GaloisForLFunctions.RHTower.CCMActualHeadGammaWallOutgoingProducer` passed.
- axiom audit: only propext, Classical.choice, Quot.sound.
- no stale Lean processes.
- `formal_tools.py lint --check-generated` still fails on unrelated pre-existing unreachable modules and concurrent stale generated indexes.

Exact remaining RH-bearing frontier: prove nonnegativity of outgoing producer on canonical Γ-Slepian heads, i.e. signed control of one growing polar continuum against higher Γ modes, reflected prime-wall chords, and outgoing endpoint coefficient. Generic lag metric/subadditivity route was hostile-killed because it would imply universal restricted-Weil positivity; canonical ground equation must enter.