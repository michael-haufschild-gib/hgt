# Theorem A assembled on a scheme (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **20**.
Continues [[research/local_noetherian_normal_dvr_2026_08_06]].

## `SchemeEigenvolumeHorizon.lean`

`abbrev CodimOnePoint X := {z : X // coheight z = 1}` — **must be `abbrev`**, not `def`, or
`Subtype.val_injective` and subtype elaboration stop working.

| Theorem A item | declaration |
|---|---|
| point below along the self-morphism | `pointBelow` |
| order of a rational function there | `ordAt` |
| **finiteness of the divisorial support** | `finite_ordAt_support` |
| **(8),(9) the shifted local order law** | `schemeEigenvolume_shiftLaw` |
| **(2),(5) horizon is a reduced divisor** | `schemeEigenvolume_ordAt_eq_neg_one` |
| **(3) total invariance** | `schemeEigenvolume_ordAt_ne_zero_iff` |
| **(4) unramified off the horizon** | `schemeEigenvolume_ramificationIndex_eq_one_off_horizon` |
| pullback law at every codim-1 point | `ord_functionFieldMap_pointwise` |

`schemeEigenvolume_shiftLaw` is assembled from `Scheme.ord_mul` + the pullback law + the Jacobian
order + the eigenvolume condition — it is **not** a hypothesis at scheme level either.

Conclusions (2)–(5) of Theorem A now hold for an **actual scheme and self-morphism**, not just the
ring model.

## Lean traps

- `variable (h : ∀ z, …)` where `z`'s type is only inferable from a *later* variable fails with
  "Invalid projection: Type of z is not known".  **Always annotate** `∀ z : CodimOnePoint X`.
- A theorem inside a section that does not use a later `variable [Inst]` triggers the
  unused-section-variable warning, and `omit … in` cannot be combined with `include … in`.
  Fix: **move the theorem above the `variable [Inst]` line**.
- `hdvr (pointBelow f hwd z)` does not synthesize `IsDiscreteValuationRing (stalk (f.base z.1))`
  because `pointBelow` is a `def` and `.1` will not unfold.  Use
  `haveI : IsDiscreteValuationRing (X.presheaf.stalk (f.base z.1)) := hdvr ⟨f.base z.1, hwd z⟩`.

## Card lineage (20 modules, all axiom-clean)

Ring model: `RamificationPoleFixedPoint`, `EigenvolumeRamificationSystem`,
`TameEisensteinDifferentExponent`, `TopExteriorPowerDeterminant`, `LocalRamificationOrderLaw`,
`RingOrdRamification`, `DivisorSupportFinite`, `PrimeDivisorLyingOver`,
`LocalizationAtPrimeDivisorDVR`, `PrimeDivisorOrder`, `PrimeDivisorPullbackOrder`,
`EigenvolumeHorizonCapstone`, `EigenvolumePullbackLaw`, `EigenvolumeUnitInvariance`.
Scheme layer: `SchemeOrderSupportFinite`, `SchemeOrderPullbackLaw`,
`SchemeMorphismOrderPullback`, `LocalNoetherianNormalDVR`, `SchemeNormalStalkDVR`,
`SchemeEigenvolumeHorizon`.

## Remaining

1. **Different exponent `e − 1`** beyond the Eisenstein presentation — the last algebraic gap;
   mathlib cannot supply it (see [[research/coframe_scheme_layer_opened_2026_08_06]]).
2. Step 1 at scheme level: identify the eigenvolume condition with `f*Ω = det(A)·Ω` for a
   coframe — needs Kähler differentials / the top exterior power of `Ω¹`.
3. Step 4's `e > 1`: needs `N¹` and int-amplification.
4. Corollary B: MMP.
