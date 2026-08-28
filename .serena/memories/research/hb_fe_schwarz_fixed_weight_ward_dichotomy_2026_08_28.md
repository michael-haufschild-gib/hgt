# HB FE–Schwarz fixed-weight Ward dichotomy (HC17, 2026-08-28)

Formalized `ThetaCuspHawkingBMFESchwarzFixedWeightWardDichotomy.lean` and wired it into `GaloisForLFunctions.RHTower`.

Key classification:
`HBXiPeierlsFESchwarzFixedWeightWardIdentity n a b ↔ a + b = 0 ∨ RiemannHypothesis`.
For `a+b ≠ 0`, universal fixed-weight orbit stationarity is equivalent to RH; equal positive weights give the canonical endpoint. Zero-total weights satisfy the Ward identity unconditionally but are RH-blind.

Main theorems:
- `hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff`
- `hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff_rh_of_sum_ne_zero`
- `hbXiPeierlsFESchwarzPositiveWeightWardIdentity_iff_rh`
- `hbXiPeierlsFESchwarzZeroTotalWardIdentity`

Verification: direct Lean passed; target `lake build` passed (11897 jobs); axiom audit only `[propext, Classical.choice, Quot.sound]`; forbidden tokens and diff check clean. Global lint reports unrelated pre-existing unreachable modules only.

Cards:
- `docs/drafts/pipeline/3-formalized/hb-fe-schwarz-fixed-weight-ward-dichotomy.md`
- `docs/drafts/pipeline/5-failed/hb-fixed-weight-orbit-ward-symmetry-no-go.md`

Positive survivor: derive one nonzero-total Ward identity from an actual gauge-fixed Einstein–Teukolsky action, boundary current, or optical conservation law; any such derivation proves RH. Frontier map remains read-only.