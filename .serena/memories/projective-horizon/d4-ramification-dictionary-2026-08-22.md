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

## Fourth batch — `(D4)` rests on ONE statement

Landed (all axiom-clean): `CyclicRepStabilizerBound`, `CriticalSchurInertiaCyclic`,
`CriticalSchurInertiaOrderBound`, `CriticalSheetUnramifiedOutsideCollision`.

Proved: the orbit formula, `isCyclic_criticalSchurInertiaGroup`, faithfulness, and
`natCard_criticalSchurInertiaGroup_le_two_of_ramification` — **every sheet over a place of
ramification index ≤ 2 implies |I| ≤ 2**.  Also: a sheet outside the collision support is fixed by
inertia, hence unramified.

**The one open statement is `∀ σ, e(Q_σ / 𝔪_A) ≤ 2`.**  Route, with the corpus inputs identified:

1. the fibre coordinates of every sheet lie in `W` and their residues *are* the reduced fibre label
   (`criticalGeometricSheetToSchurFibre`, `criticalGeometricSheetToSchurReducedFibre`);
2. the marked coefficient has nonzero residue
   (`reduced_criticalNormalClosureSchurRawTailIntegral_coeff_marked_ne_zero`), so the normalising
   scale is a unit of `W` and the **Schur** coordinates
   (`criticalSourceSchurCoordinates`, in the source valuation subring by
   `criticalSourceSchurCoordinates_mem_sourceValuationSubring`) also land in `W` with residues
   determined by the reduced fibre label;
3. the Schur coordinates are algebraically independent
   (`algebraicIndependent_criticalSourceSchurCoordinates`), so `criticalSchurSourceRing` is a
   POLYNOMIAL ring and its height-one localization is a DVR
   (`criticalSchurCoordinateValuationSubring_isDiscreteValuationRing`);
4. hence two sheets with the same reduced label have the same centre there, and
   `ValuationSubring.eq_of_le_of_ne_top` gives `σ⁻¹(W) = criticalSchurSourceValuationSubring`
   (which is `criticalNormalClosureSchurValuationSubring_comap_source` for the canonical sheet);
5. `criticalSchur_source_ramificationIdx_eq_two` then gives `e = 2`, and sheets outside the
   collision support are already known unramified.

## ELABORATION DISCIPLINE for this card (cost a dozen rebuilds)

On the horizon's sheet/permutation/valuation types:
* `rw` must compute a motive over those types and **times out at 20M heartbeats**; use `Eq.trans`,
  `Eq.trans_le`, `congrArg` instead;
* `MulAction.orbit` / `MulAction.stabilizer` in a *statement* are fatal; state the group theory
  abstractly with a `Nat.card` inequality over a plain subtype and instantiate;
* `show` / `change` on `criticalSchurInertiaAction` applications are fatal;
* `Nat.card_pos` on a subgroup of the inertia group triggers a fatal instance search — derive
  positivity from an equation instead;
* raise `synthInstance.maxHeartbeats 3000000`, `maxHeartbeats 8000000`, `maxSynthPendingDepth 3`;
* restate a corpus theorem under the *folded* name (`criticalSchurInertiaGroup`) by `exact`, once,
  and work with the folded form thereafter.

## Fifth batch — `RamificationIdxTransport`, and step (3) of the last chain

`HTGeometry/RamificationIdxTransport.lean`: `ramificationIdx'_algEquiv` — the ramification index is
invariant along an algebra equivalence (mathlib has only `ramificationIdx_smul`, one fixed ring).
Proof is one line on the `sSup` definition of `ramificationIdx'`.

**Key find for the last open statement.**  The normalisation by the scale is legitimate for *every*
sheet without any integrality argument: `TruncatedCompatibilityFibre` proves
`A.coeff 0 * B.coeff 0 = 1` for a point of the critical fibre **over an arbitrary commutative ring**,
so applying it to the REDUCED fibre point shows the residue of the scale is a unit, hence the scale
is a unit of `W`.  The Schur coordinates (raw coefficients over the scale, reversed reciprocal
squares) therefore lie in `W` with residues fixed by the reduced fibre label — which is what makes
the polynomial-ring/DVR argument run.

Fifteen modules landed for this card on 2026-08-22.

## Sixth batch — steps (3) and (4) of the last chain are CLOSED

Landed: `CriticalSheetJetUnit`, `CriticalSheetScaleUnit`, `SubringPolynomialCoefficients`,
`RamificationIdxTransport`.  Eighteen modules total on 2026-08-22, all axiom-clean.

* `isUnit_criticalSheetScale` — σ(scale) is a UNIT of W for every sheet.  Comes from the fibre
  equation `A.coeff 0 * B.coeff 0 = 1`, which the corpus proves only over a *field* and only as
  `≠ 0`; the identity itself needs no field, so it holds in the valuation ring where the sheet's
  fibre point lives.  **No integrality over the observation DVR is needed — and none exists.**
* `finiteReciprocalSquarePositive_mem` — the Schur coordinates of a family lying in a `Subring` lie
  in that subring.  Works because `truncatedReciprocalKernel N U = ∑_{j<N} (−(U−1))^j` has **no
  division**.  The corpus's `PolynomialCoefficientsIn` is for an `IntermediateField` only.
* `ramificationIdx'_algEquiv` — the ramification index travels along an algebra equivalence.

### Exactly what remains, at the level of individual corpus lemmas

(a) `σ(criticalSourceRaw j) ∈ W` for every sheet and every `j : Fin (m+n)`:
    * `j < m`: it is a low coefficient — `criticalGeometricSheetToSchurFieldFibre_coefficients_mem`;
    * `j ≥ m`: `criticalSourceRaw j = algebraMap E→F_src (criticalObservationRaw ⟨j−m⟩)`
      (the computation is spelled out in `CriticalGeometricSheetFibre.lean` around line 429), so σ
      fixes it and it lies in the observation Schur DVR — `criticalSchurObservationRawTailIntegral`.
(b) hence `σ(criticalSourceNormalizedPositive j) ∈ W` (divide by the unit scale), hence every Schur
    coordinate lands in the subring `W.comap σ` of `F_src` by `finiteReciprocalSquarePositive_mem`.
(c) two sheets with the same reduced fibre label give the same residues on all raw coordinates,
    hence on all Schur coordinates, hence the same centre on the Schur coordinate ring.
(d) `criticalSourceSchurFieldEquiv_symm_coordinate` identifies that ring with the polynomial ring
    `criticalSchurSourceRing`; its localization at the centre is
    `criticalSchurSourceValuationSubring`, a DVR, so `ValuationSubring.eq_of_le_of_ne_top` gives
    `σ⁻¹(W) = criticalSchurSourceValuationSubring` — for the canonical sheet this is
    `criticalNormalClosureSchurValuationSubring_comap_source`.
(e) `criticalSchur_source_ramificationIdx_eq_two` + `ramificationIdx'_algEquiv` + `ramificationIdx'_eq_ramificationIdx`.

Note: `σ⁻¹(W) ⊇ criticalSchurSourceValuationSubring` is **false** for a general sheet (different
sheets induce different places over the same base), so (c) genuinely needs the residue comparison —
do not try to shortcut it.

## SEVENTH BATCH — `(R)` CLOSED.  `|I| = 2` is unconditional

`natCard_criticalSchurInertiaGroup_le_two_of_ramification`'s hypothesis `hram` is DISCHARGED.
Six modules (all axiom-clean, wired):

* `CriticalSheetResidueCongruence` — `coe_criticalSheetJetCoeff`, `criticalSheetToUpper`,
  `criticalSheetResidue`, `criticalSheetRaw_residue_congr`, `criticalSheetScale_residue_congr`.
* `CriticalSheetSchurCoordinateResidue` — `criticalSourceNormalizedPositive_mul_scale`,
  `criticalSheetSchurCoordinate_succ_lift`, `criticalSheetSchurCoordinates_residue_congr`.
* `CriticalSheetCoordRingResidue` — `coe_algebraMap_criticalSchurSourceValuationSubring`,
  `criticalSheetAevalHom`, `criticalSheetCoordResidue`, `criticalSheetCoordResidue_congr`.
* `CriticalSheetSchurPlacePullback` — `criticalSheetPullbackValuation(_canonical/_ne_top/_eq)`,
  `isUnit_criticalSheetAeval`, `criticalSchurSourceValuationSubring_le_sheet`.
* `CriticalSheetPlaceRamificationIndex` — `isUnit_valuationSubring_iff`, `criticalSheetFieldEquiv`,
  `criticalSheetIntegralClosureEquiv`, `criticalSheetIntermediateCentre_comap`,
  `criticalSheetRamificationIdx_eq_two`.
* `CriticalSchurInertiaOrderTwo` — `criticalSourceNormalClosureEmbedding_mem_collisionSupport`,
  `criticalSheetRamificationIdx_le_two`, `natCard_criticalSchurInertiaGroup_le_two`,
  `natCard_criticalSchurInertiaGroup_eq_two`.

**Why it is not circular.**  `e(Q_σ)` = orbit size by the orbit formula, but it is computed from the
PLACE, not the orbit: same label ⟹ same residues on the coordinate ring ⟹ the sheet's pullback
contains the (DVR) source Schur valuation ring ⟹ equals it ⟹ its ramification index is
`criticalSchur_source_ramificationIdx_eq_two` = 2.  The canonical embedding cuts out that place, so
it collides; every collision shares its label; everything else is unramified.

## Remaining for `(D)` = `hdeg`: the label fibre has at most two sheets

`|I| = 2` gives `t = e(w / w_std) = 1`.  Two routes, each one step from done:
* (A) derivative count: θ integral over A with `E(θ) = F_src` (a valuation ring is integrally
  closed, so every sheet sends it into W); `card_congruent_roots_le_addVal_eval_derivative` bounds
  the fibre by `1 + w(p'(θ_σ))`; with `t = 1` that is `1 + v_{w_std}(p'(θ))`.  MISSING: local
  monogenicity `V = A_p[θ]`, which makes `v(p'(θ))` the different exponent `= e − 1 = 1`
  (`DifferentIdealMonogenic` + `DifferentExponentTame.differentIdeal_eq_span_pow`).
* (B) residue degree: fibre `= e = 2` once `f(w_std/p) = 1`, which is §3's birationality
  (`criticalFibre_eq_of_shared_coprime_tangent`, already Lean).  MISSING: "#sheets over a place
  = e·f".

## Lean traps added this batch

* `(by omega : 0 < m)` inside a MULTIPLICATION or a `residue` argument elaborates as "No goals to be
  solved"; use the pure term `Nat.zero_lt_of_lt hm` everywhere on this card.
* `rw` inside a dependent `⟨x, proof⟩` literal fails on the motive; state the equation as a separate
  `have` about the bare elements and close with `Subtype.ext`.
* `AlgEquiv.restrictScalars` needs `(S := …)` given explicitly or it unifies `S` with `R`.
* `IsIntegral.map` on the horizon needs the *field-level* AlgHom (over the observation field), not
  the A-level one: `IsScalarTower A A ↥M` is not found, `IsScalarTower A F ↥M` is.
* `Ideal.map_comap_of_surjective` must be given the coercion `(ψ : _ →+* _)` explicitly.
* `Finite.one_lt_card`, not `Nat.one_lt_card` (the `Nat`-namespace one is about `ENat.card`).
* `Module.isTorsionFree_iff_algebraMap_injective`, not `NoZeroSMulDivisors.of_algebraMap_injective`.

## `(D)` — the exact remaining statement (sharpened after closing `(R)`)

collisionSupport = {sheets over the source Schur place} = ONE label fibre, of size `e·f = 2·f₁`.
So `(D) ⟺ f(w_std / p) = 1 ⟺ the label fibre is a single inertia orbit`.  Route (A) of the previous
section reduces to the same thing: every tame-different theorem in the corpus assumes a trivial
residue extension.

The Lean route is the decomposition dictionary at valuation-subring level — two general theorems,
neither in mathlib:
* (i) transitivity of `Gal(L/M)` on valuation subrings of `L` with a fixed restriction to `M`
  (mathlib has `Ideal.exists_smul_eq_of_isGaloisGroup`; bridge = `valuationSubringAtPrime_eq`);
* (ii) `|D_W over M| = |I_W over M| · f` (mathlib: `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`)
  plus `Nat.card (Aut (k_W / k_w)) ≤ f`.
Then: τ with the canonical label ⟹ τ = g∘σ₀ with g ∈ D_W; ḡ fixes k_{w_std}; `t = 1` makes
`D_{W/σ₀F} → Aut(k_W/k_{w_std})` injective between sets of size `f(W/w_std)`, hence surjective;
correct g into I.  Label fibre = I-orbit of σ₀, size 2 = `(D)`.

## Eighth batch — brick (i) landed

`HTGeometry/ValuationSubringGaloisTransport.lean`:
`smul_valuationSubring_eq_of_smul_centerPrime` — `g • centre W₁ = centre W₂ ⟹ g • W₁ = W₂`.
Proof is the fraction description on both sides.  With `Ideal.exists_smul_eq_of_isGaloisGroup` this
is transitivity of the Galois action on valuation subrings over a fixed one.

Still to build for `(D)`: brick (ii) — transport of
`Ideal.card_stabilizer_eq_card_inertia_mul_finrank` to valuation subrings — and the assembly
"label fibre = inertia orbit".  Note mathlib also has `Ideal.IsFractionRing.normal`, so the residue
extension being Galois is available.
