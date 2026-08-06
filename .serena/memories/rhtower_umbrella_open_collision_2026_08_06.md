# RHTower umbrella: one open name collision (2026-08-06 ~22:45)

`lake build GaloisForLFunctions.RHTower` currently fails with

    import GaloisForLFunctions.RHTower.DeningerFineLifting failed, environment already contains
    'RHTower.deningerExtendByZero' from GaloisForLFunctions.RHTower.DeningerExtendByZero

Two distinct declarations share the full name:

- `DeningerExtendByZero.lean:31` — `noncomputable def deningerExtendByZero (U : Set X) (ρ f : X → ℝ)`
  (committed 1 Aug; canonical owner, the module is named after it, has a family of `_eq_of_mem`,
  `_eq_zero`, `_continuous` lemmas).
- `DeningerFineLifting.lean:64` — `theorem deningerExtendByZero (A : DeningerFineAction F) (ρ : C(X,ℝ))`
  (untracked, written 22:20). Referenced once, at `DeningerFineSurjective.lean:91`.

Suggested fix (2 edits, behaviour preserving): rename the **theorem** to
`deningerFineAction_extendByZero` in `DeningerFineLifting.lean` and update the single call site in
`DeningerFineSurjective.lean`. The def keeps the canonical name.

I did NOT apply it: both files were untracked and being actively rewritten by another session
(`DeningerFineSheaf.lean` modified, `DeningerSheafGluing.lean` untracked at the same time). A partial
clobber would leave the pair inconsistent and break their proof. Whoever owns the Deninger sheaf work
should do the rename.

An earlier collision in the same umbrella run was fixed here, on committed files only:
`RHTower.setIntegral_Ioi_comp_add_right` was declared both in `ComplementaryPacketCofinalIsometry`
(real-valued) and in the new `EulerHedenmalmMobiusStokesInverse` (complex-valued). The committed
real-valued one is now `setIntegral_Ioi_zero_comp_add_right` (it is the `L = 0` case of the existing
`setIntegral_Ioi_comp_add_right'`), with its two call sites updated in
`ComplementaryPacketCofinalIsometry` and `ComplementaryPacketTwoPointDistance`. Those two plus
`ComplementaryPacketAffineFlux` and `ComplementaryPacketLocalZetaTwo` all rebuild green.

## Detector discipline

A namespace-blind regex scan for duplicate top-level names over `RHTower/` reports ~135 hits, almost
all false positives from per-file namespaces and structure fields (`mk`, `add`, `Hom.comp`,
`eigenvalue_re_eq_half`, …). Only the area umbrella build identifies real collisions. Use
`lake build GaloisForLFunctions.RHTower` as the detector; do not act on a scan.
