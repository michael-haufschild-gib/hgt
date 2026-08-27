# HB finite-source radical and unit-carrier reflection obstruction — 2026-08-27

Two exact HB deltas were completed.

1. `GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicFiniteSourceGreenRadical.lean`
   - Defines finite normalizable source moment and explicit gain `-4 lambda/(A_R A_C)`.
   - Main theorem `d4BMPlusPlusFiniteIngoing_eq_outgoing_iff_normalizableSourceMoment_eq_zero`: physical finite ingoing/outgoing responses agree as functions iff the unique normalizable-mode source moment vanishes.
   - This is `[REDISCOVERED] [BRIDGE]`: rank-one resolvent mechanism is classical, BM coefficient specialization corpus-specific.
   - Positive survivor: actual augmented Einstein incidence reduces to one literal source-moment evaluation; point-source noncollapse cannot imply arbitrary-source noncollapse.

2. `GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicCarrierNormalizedReflectionObstruction.lean`
   - Explicit nonzero seed normalizes the self-dual Einstein carrier to one.
   - FE reflection preserves orthogonal-helicity mixing coefficient because angular eigenvalue is even and centered spectral point negates.
   - Main identity `d4BMXiSecondHarmonicUnitCarrierPeierlsPolarizedCut_reflection_add`:
     `P0(n,q,z)+P0(n,reflect q,z) = -2*normSq(mixing(q))*(8*n+5)`.
   - Pointwise zero iff critical line; universal vanishing theorem is exactly RH.
   - `[NEW] [BRIDGE]` after internal and primary-source search; priority provisional.

Cards:
- `docs/drafts/pipeline/3-formalized/hb-bm-finite-source-green-radical.md`
- `docs/drafts/pipeline/3-formalized/hb-bm-carrier-normalized-reflection-obstruction.md`

Verification for both: direct `lake env lean`, targeted `lake build <module>`, `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`, `scripts/formal_tools.py lint` passed; modules wired into `GaloisForLFunctions/RHTower.lean`.

Sharpened HB open core:
1. derive literal augmented `++/--` Peierls incidence from one time-oriented skew propagator with conjugate-frequency endpoint/counterterm and left-QNM sewing;
2. prove carrier-normalized physical causal cut is FE-reflection odd before Xi-copy specialization.
The new `8*n+5` obstruction makes clause 2 incompatible with every off-wall copy. No further radial receiver work advances either clause.