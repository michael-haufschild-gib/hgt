# Gauge collapse and stratified observation-density reconstruction law — Lean certificate

- **ID:** `cmr-gauge-collapse-stratified-observation-density-reconstruction-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `gauge-collapse-stratified-observation-density-reconstruction-law.md`
  (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean module

`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/GaugeCollapseObservationDensity.lean`,
namespace `HTGeometry.ConstraintMotiveRelativity`, imported by `GaloisForLFunctions.HTGeometry`.

## Formal statement chain

### §2 — gauge collapse

1. **`isEquivalence_of_gauge`** — Theorem 2.1: if the doctrine change `F(u)` fits into a
   single-carrier presentation, i.e. there are equivalences `φ_d : C ≌ F_d`, `φ_e : C ≌ F_e` and a
   pseudonaturality iso `η : φ_d ⋙ F(u) ≅ φ_e`, then `F(u)` is an equivalence.  The proof transports
   equivalence along `η` and cancels the left factor.
2. **`objIsoOfGauge`** — Theorem 2.1 (2): a gauge reflects object isomorphism, so a transition
   identifying two nonisomorphic objects cannot be a gauge.
3. **`isIso_of_gauge`** — Theorem 2.1 (3): a gauge reflects invertibility, so a transition sending a
   noninvertible morphism to an isomorphism cannot be a gauge.
4. **`no_gauge_of_not_isEquivalence`** — Theorem 2.1 (1): a transition that is not an equivalence
   rules out single-carrier gauge unification.
5. **`localizationIdentifies`** — Corollary 2.2, `(GOD.7)`: in any localization inverting the
   doctrine-change arrows, the images of two objects whose changes agree become isomorphic.  Forcing
   a lossy change to be a gauge erases the exhibited distinction instead of repairing it.

### §4 — the observation nerve

6. **`isDense_iff_nerve_fullyFaithful`** — Theorem 4.1: the probe nerve reconstructs every object
   **iff** the probe functor is dense, i.e. iff its restricted Yoneda embedding is fully faithful.
   Density in this sense is exactly the statement that the canonical comparison `(GOD.11)` from the
   colimit over the category of elements is an isomorphism, which is the pointwise left Kan
   extension condition.
7. **`faithful_of_nerve_descends`** — Theorem 4.2: a complete source nerve cannot descend through a
   realization that identifies two parallel morphisms.
8. **`isIso_of_nerve_descends`** — Theorem 4.2: it reflects isomorphisms.
9. **`objIsoOfNerveDescends`** — Theorem 4.2, `(GOD.13c)`: it reflects object isomorphism.
10. **`nerveDescendsSerial`** — Theorem 4.2, `(GOD.13d)`: descent through a serial realization
    implies descent through its first leg, so a later observer cannot repair source-nerve
    information already lost by an earlier exit.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/GaugeCollapseObservationDensity.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.GaugeCollapseObservationDensity
```

Green with no warnings.  `#print axioms` on `isEquivalence_of_gauge`, `objIsoOfGauge`,
`isIso_of_gauge`, `no_gauge_of_not_isEquivalence`, `localizationIdentifies`,
`isDense_iff_nerve_fullyFaithful`, `faithful_of_nerve_descends`, `isIso_of_nerve_descends`,
`objIsoOfNerveDescends` and `nerveDescendsSerial` reports only `propext`, `Classical.choice`,
`Quot.sound`.

## Scope notes

The card's pseudofunctor `F : D ⥤ Cat` and its Grothendieck construction are the ambient
bookkeeping; every theorem it proves is a statement about a *single* doctrine change `F(u)` (§2) or
about a *single* realization functor out of the total category (§4).  The module therefore states
each theorem for the arrow or functor it is about, with the presentation data `φ_d`, `φ_e`, `η` as
explicit hypotheses — which is exactly `(GOD.2)`–`(GOD.3)`.  No generality is lost: the pseudofunctor
supplies these data and nothing else enters the proofs.

Theorem 4.1's three equivalent conditions are one statement in mathlib's formulation: `J.IsDense`
*is* the assertion that `𝟭` is the pointwise left Kan extension of `J` along `J`, i.e. that every
comparison `(GOD.11)` is an isomorphism, and `(GOD.12)` is the coend presentation of the same
weighted colimit.  `isDense_iff_nerve_fullyFaithful` records the equivalence with full faithfulness
of the nerve.

§§5–10 are programme interpretation, corpus calibration, the bold field conjecture, hostile loops
and no-go bookkeeping; they claim no further theorem.
