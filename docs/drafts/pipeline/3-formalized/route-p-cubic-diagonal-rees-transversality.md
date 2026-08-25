# Cubic Xi diagonal-Rees transversality

- **ID:** route-p-cubic-diagonal-rees-transversality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** irregular-RH Route P cubic landing audit
- **Statement:** Every coefficient-generated cubic Xi landing at complete threshold contraction moves strictly above the Xi target after unit Rees activation; consequently no fixed charge lands at both scales.

## Goal

Decide whether the threshold-neutral Rees-rigid survivor from cubic microlocal Witt-signature
classification can exist in canonical coefficient-generated Stokes data.  This is an application
to the completed-Xi cubic residual, not construction of general irregular-RH foundations.

## Gates

- [x] 0 → 1 in-progress: exact source target and canonical coefficient-generated Stokes carrier
- [x] 1 → 2 fully-proven: dependency-closed proof below; no open input
- [x] 2 → 3 formalized: targeted module check passed; five new declarations have only `propext`, `Classical.choice`, `Quot.sound`
- [ ] 3 → 4 publication-ready: independent priority review pending

## Internal and external frontier

- `[CORPUS]` `PositivePendantCutFamily.pendant_coordinate_sum` proves every canonical pendant cut
  isolates one branch coefficient.
- `[CORPUS]` `routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero` proves every
  cubic Xi landing has nonzero charge.
- `[CORPUS]` the Rees decomposition and existing two-scale rigidity theorem show equal contracted
  and unit values annihilate all threshold channels, but do not yet use pendant faithfulness.
- `[LITERATURE]` generalized irregular Riemann--Hilbert existence
  ([Bolibruch--Malek--Mitschi](https://arxiv.org/abs/math/0410483)), irregular holonomic
  correspondence ([Kashiwara](https://arxiv.org/abs/1512.07723)), connection-map deformations
  ([Xu](https://arxiv.org/abs/1507.07149)), and irregular Hurwitz-space constructions
  ([Shramchenko](https://arxiv.org/abs/0707.0696)) do not supply a completed-Xi
  pendant-faithfulness/transversality theorem.  Absence is audit evidence, not a priority claim.

## Paper proof

Let `x` be a cubic Xi landing charge at zero Rees parameter.

1. The cubic residual is strictly negative while the zero charge has Witt value zero, so the
   existing landing theorem gives `x ≠ 0`.
2. Some marked-point orbit-charge vector `x_a` is nonzero.
3. Surjectivity of branch-to-orbit map implies pulled-back branch charge `liftCharge(x_a)` is
   nonzero: if every pullback coordinate vanished, choose a branch over each orbit to recover
   `x_a = 0`.
4. Canonical rooted cut system contains positive pendant singleton cut for every branch.  Its
   pendant-coordinate theorem therefore gives strictly positive block coarea for `x_a`.
5. Every other local block energy is nonnegative, so total global block coarea is strictly positive.
6. Subtracting global Rees decompositions at parameters zero and one cancels terminal and unique
   physical-rank channels.  Difference is exactly total block coarea, hence unit value is strictly
   greater than contracted value, which is cubic Xi residual.
7. A fixed charge therefore cannot land at cubic Xi residual at both scales.  The Rees-rigid landing
   fiber and its raw-Euler refinement are empty.

## No-go closure

- **Exact killing theorem/mechanism:** pendant singleton cuts make canonical threshold coarea
  faithful; annihilating all threshold charges annihilates full orbit charge.
- **Strongest positive survivor:** every contracted cubic Xi landing has strictly positive unit-Rees
  drift, exactly measured by total canonical block coarea.
- **New insight:** coefficient-generated cubic Xi crossing is necessarily Rees-transverse.  A viable
  irregular-RH producer cannot preserve one fixed charge across contracted and unit scales; it must
  change charge/carrier or break canonical Rees covariance.
- **Status:** `[LEAN-PROVED]` in
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicDiagonalReesTransversality.lean`.
  Scientific novelty unverified.

## Lean certificate

Capstone:

- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber`

Supporting declarations:

- `routePPrimitiveGammaJuliaStokesCubicContractedLanding_totalBlockEnergy_pos`
- `routePPrimitiveGammaJuliaStokesCubicContractedLanding_unit_sub_target_eq_totalBlockEnergy`
- `routePPrimitiveGammaJuliaStokesCubicContractedLanding_unit_gt_target`
- `not_nonempty_routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber`

## Log

- 2026-08-25 — pendant-faithfulness killed Rees-rigid survivor; strict transversality paper proof closed
- 2026-08-25 — exact transversality and both emptiness corollaries formalized in Lean
