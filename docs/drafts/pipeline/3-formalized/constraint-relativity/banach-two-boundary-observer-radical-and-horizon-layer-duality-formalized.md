# Banach two-boundary observer radical and horizon-layer duality — formalized

- **ID:** `banach-two-boundary-observer-radical-and-horizon-layer-duality-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `banach-two-boundary-observer-radical-and-horizon-layer-duality.md`
- **Status:** `[LEAN COMPLETE] [NO SORRY] [NO PROJECT AXIOMS]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/BanachTwoBoundaryDuality.lean`,
namespace `HTGeometry.ConstraintRelativity`. It is wired into
`GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `ker_twoBoundaryQuotient` and `twoTermConeMinusOneEquiv` prove `(BHR.2)` and `(BHR.4)` for
   literal Banach quotient maps.
2. `ker_continuousRestrict`, `continuousRestrict_surjective`,
   `ker_twoBoundaryObserverRestriction`, and `topologicalDescentRadicalEquivKernel` prove the
   Hahn--Banach exact sequence `(BHR.7)`.
3. `weakStarClosure_sup_annihilator` proves `(BHR.8)` as equality of weak-star closed submodules;
   the separation proof identifies every weak-dual separator with evaluation at an ambient vector.
4. `boundaryObserver_vanishes_on_common` and `exists_detecting_nondescending_observer` formalize
   the locality no-go without a complement assumption.
5. `nestedCut_ker` proves `(BHR.12)` for every nested pair of cuts.
6. `normalLayerRestriction`, `ker_normalLayerRestriction`, and
   `normalAnnihilatorQuotientEquivLayerPredual` prove the exact algebraic quotient/range and
   representative pairing in `(BHR.14)`--`(BHR.15)` for an arbitrary selected normal-predual copy.
7. `predualAnnihilator_weakStarCut` proves Hahn--Banach double-annihilator recovery for every
   closed predual subspace. `quotientNorm_transport` and `quotientIsometryTransport` prove norm
   preservation for quotients under a denominator-identifying linear isometry. Consequently
   `weakStarNormalObserverQuotientIsometry` proves the isometric statement in `(BHR.14)`: the
   normal-observer quotient recovered from weak-star annihilator cuts is linearly isometric to the
   literal relative predual layer.
8. `transportObserver_mem_annihilator` and `transportObserver_pairing` prove `(BHR.17)`--`(BHR.18)`
   for every continuous linear equivalence, hence for every modular transport satisfying the
   paper card's HSMI input.
9. `thermofield_boundary_intersection`, `thermofieldModularFlow_basis`, and
   `thermofieldBasis_erased` prove `(BHR.23)`--`(BHR.24)` and the finite type-I countermodel.

## Scope

Mathlib has no bundled von Neumann-algebra predual object. The formal statement therefore uses the
equivalent Banach dual-pair presentation: closed subspaces `A,B` of a predual `P`, with weak-star
cuts `A⊥,B⊥` inside `P*`. Hahn--Banach recovers `A,B` exactly, and the induced quotient isometry
is a literal `LinearIsometryEquiv`, not only an algebraic equivalence or selected range. No
continuous complement, HSMI existence theorem, gravity structure, or wormhole conclusion is
introduced.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/BanachTwoBoundaryDuality.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.BanachTwoBoundaryDuality
```

`#print axioms` for the principal declarations returns only `propext`, `Classical.choice`, and
`Quot.sound`.
