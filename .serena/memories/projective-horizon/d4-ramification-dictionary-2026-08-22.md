# `(D4)` of the full-symmetric-monodromy card: the ramification dictionary

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/projective-horizon-full-symmetric-monodromy.md`
Ledger: `.../new_scientific_knowledge/_FORMALIZATION-LEDGER.md`

## The single open statement

`criticalSchur_collisionSupport_ncard_le_two_of_fibre` reduces the card's `(D)` to

    forall sigma, ncard {tau | criticalGeometricSheetToSchurReducedFibre tau = ... sigma} <= 2

## The route (fixed after exhausting the alternatives)

1. `Stab_I(sigma)` is `W.inertiaSubgroup (sigma F_src)` — restriction of scalars, definitional.
2. `Nat.card (W.inertiaSubgroup F) = ramificationIdxIn p T` — **NEW**,
   `HTGeometry/ValuationInertiaRamificationIndex.lean`, uniform in the base field/ring.
3. `Ideal.ramificationIdx_tower` (no Galois hypothesis on the middle!) gives orbit = e(Q_sigma / m_A).
4. `sigma^{-1}(W) = criticalSchurSourceValuationSubring` for sigma in the collision fibre: the Schur
   coordinate ring is a POLYNOMIAL ring, so every height-one localization is a DVR, and the
   valuation ring is determined by the residues of the coordinates — which two colliding sheets share.
5. `criticalSchur_source_ramificationIdx_eq_two` gives: every orbit has size at most 2.
6. `CyclicCollisionOrderBound.natCard_le_two_of_isCyclic` (+ `TameInertiaCyclic.isCyclic_of_tame`,
   `criticalSchurInertiaAction_injective`) gives `|I| <= 2`, hence `e(w/O_src) = 1`.
7. `RootCongruenceValuationCount.card_congruent_roots_le_addVal_eval_derivative`
   + monogenicity + `criticalSchur_differentIdeal_not_le_sq` gives `|F| <= 2`.

## Dead ends — do not repeat

* The different is **uninformative** about `t = e(w/Q0)`: the tame identity `w(D_{W/A}) = 2t - 1`
  holds for every `t`.
* Pure orbit combinatorics of a faithful cyclic action with `sum orbit <= 1 + t` does **not** force
  `t = 1`: `t = 20`, orbits `{8,10}`, `|I| = 40`, `|F| = 18 <= 21` passes every count.
* Corank one bounds the *embedding dimension* of the collision class, never its *length*.
* `Ideal.ramificationIdxIn_mul_ramificationIdxIn` needs `IsGaloisGroup` for the middle extension —
  unusable, since `F_src/E` is the non-normal step.  Use `Ideal.ramificationIdx_tower`.

## Lean traps recorded

* The `Gal(L/F)`-action on an integral closure must be introduced with `letI`, not `haveI`, or
  `algebraMap_galRestrict_apply` will not apply.
* `Module.Flat R T` needs `Module.IsTorsionFree R T` first.
* `ValuationSubring.eq_of_le_of_ne_top` takes the smaller ring **explicitly** first.
* Membership in `IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime` destructures as
  `<a, s, hs, rfl>` with the element equal to `a * s^{-1}`, not `a / s`.

## Also still open on this card

`(P)` preprimitivity: `E3`, `E4`, `E6`, `E7` (the block system and the Kummer valuation).  `E1`,
`E5` (`SCE_k`, affine space is algebraically simply connected) and Jordan's criterion are done.

## Modules landed 2026-08-22 (all axiom-clean)

* `HTGeometry/TameInertiaOrderBound.lean` — `|Γ| ≤ addVal W x` for a Γ-fixed nonzero nonunit.
* `HTGeometry/ValuationSubringInertiaDictionary.lean` — `mem_iff_exists_div`, `inertia_eq_map`,
  `natCard_inertia_eq_natCard_inertiaSubgroup`.
* `HTGeometry/ValuationInertiaRamificationIndex.lean` —
  `integralClosure_mem_of_base_mem`, `mem_of_isIntegral`, `liesOver_centerPrime`,
  `natCard_inertiaSubgroup_eq_ramificationIdxIn` (Dedekind base, arbitrary base field, abstract
  integral closure `T`), `ramificationIdxIn_tower`.
* `HTGeometry/ValuationInertiaIntermediateField.lean` — `mem_inertiaSubgroup_iff`,
  `decompositionRestrict`, `natCard_inertiaSubgroup_intermediate`.

Together: **orbit_σ = e(Q_σ / 𝔪_A)**, unconditionally.  Remaining for `(D4)`: instantiation on the
horizon's objects (`B_σ` Dedekind, `IsIntegralClosure C B_σ L`, the two `hcent` conditions),
`σ⁻¹(W) = criticalSchurSourceValuationSubring` for a colliding sheet, then
`criticalSchur_source_ramificationIdx_eq_two`, `natCard_le_two_of_isCyclic`, and the derivative count.

## Modules landed 2026-08-22, second batch

* `HTGeometry/CyclicOrbitOrderBound.lean` — `natCard_le_two_of_isCyclic_of_orbit`.
* `HTGeometry/CriticalSheetStabilizerInertia.lean` — `natCard_sheetStabilizer_eq_natCard_inertiaSubgroup`.
* `HTGeometry/ValuationInertiaRamificationIndex.lean` (extended) —
  `natCard_inertiaSubgroup_eq_ramificationIdx_mul` (the orbit formula).
* `HTGeometry/CriticalSchurInertiaRamificationIndex.lean` —
  `natCard_criticalSchurInertiaGroup_eq_ramificationIdxIn` (the bottom instantiation; the corpus had
  only `e ≤ |I|` before).

Next: `IsIntegralClosure T B_σ L` for `B_σ = integralClosure A (AlgHom.fieldRange σ)`, the contracted
prime `Q_σ`, then the middle instantiation, then `σ⁻¹(W) = criticalSchurSourceValuationSubring`.

Elaboration budget: the critical field stack needs `synthInstance.maxHeartbeats 3000000`,
`maxHeartbeats 4000000`, `maxSynthPendingDepth 3`, and `rw` must be replaced by `exact`/`Eq.trans`
wherever a motive over these types would be computed.

## Third batch — the orbit formula is DONE

* `HTGeometry/ValuationInertiaIntermediateBase.lean` — `natCard_inertiaSubgroup_eq_intermediate_mul`.
* `HTGeometry/CriticalSheetOrbitRamification.lean` — `natCard_criticalSchurInertiaGroup_eq_sheet_mul`:
  `|I| = e(Q_σ/𝔪_A) · |Stab_I(σ)|` for every geometric sheet.

Nine modules total on 2026-08-22, all axiom-clean.  Steps (1)–(3) of the route are closed; what
remains is (d) `e = 2` on a colliding sheet, (e) the cyclic bound, (f) the derivative count.

For (d): two sheets with the same reduced fibre label give the same centre on the Schur COORDINATE
ring (a polynomial ring), because both send a coordinate polynomial to the same residue; a
height-one localization of a polynomial ring is a DVR, and `ValuationSubring.eq_of_le_of_ne_top`
then forces the two valuation rings to coincide.  `criticalSchurCoordinateValuationSubring_isDiscreteValuationRing`
and `criticalNormalClosureSchurValuationSubring_comap_source` are the two corpus inputs.

Lean-side gotchas found in this batch:
* auto-included section variables must be cut with `omit [...] in` or a later declaration in the
  same section cannot use the earlier one (the horizon supplies `FiniteDimensional`/`IsGalois` only
  as `haveI`s, never as global instances);
* build `CharZero` of a residue field through an abstract lemma taking a ring hom from a char-zero
  field — the four-step composite inside the horizon's types exhausts the elaborator.
