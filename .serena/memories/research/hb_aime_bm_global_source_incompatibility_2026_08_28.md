# HB AIME/BM global source incompatibility (2026-08-28)

Formalized source-side HB no-go and exact surviving repair law.

Module:
- `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility`

Theorems:
- `forall_normalizedAIMEResidue_eq_unitBMTarget_iff`: for any overtone n and complex normalization c/absorbed seed a, all-Xi equality `c * AIMEResidue(a,q) = BMTarget(n,1,q)` iff `(c=0 or a=0) and RH`.
- `not_exists_nonzero_normalizedAIMEResidue_global_unitBMTarget`: no nonzero normalization of nonzero AIME channel globally realizes BM incidence.
- `d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_samePoleSource`: exact remaining-source law `Remainder(q)=JostDerivative(q)*BMTarget(q)-AIMENumerator(q)`.
- Critical-line specialization forces `Remainder(q)=-AIMENumerator(q)`, nonzero for nonzero absorbed seed.

Insight: AIME is genuine literal nonlinear gravitational support but its global zero geometry is incompatible with BM Peierls incidence. Remaining HB producer must contain a genuinely new same-pole third-order `++-` source; scalar normalization/horizon phase/AIME alone cannot work.

Verification: direct Lean and target-specific Lake build passed. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired. Global lint only unrelated pre-existing unreachable modules.

Cards:
- `docs/drafts/pipeline/3-formalized/hb-aime-bm-global-source-incompatibility.md`
- `docs/drafts/pipeline/5-failed/hb-nonzero-aime-only-global-bm-incidence-no-go.md`

Frontier map remains read-only per user.