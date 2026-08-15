# Digamma--Gamma `HypertranscendentalNear` connector

- **ID:** digamma-gamma-hypertranscendental-near-connector
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean) · STRUCTURAL CONNECTOR
- **Status:** `[PROVED HERE] [LEAN-CERTIFIED] [NOT A NOVEL MATHEMATICAL CLAIM]`
- **Statement:** `z ↦ digamma (Gamma z)` is `HypertranscendentalNear` every point of
  `digammaGammaRegularSet`; in particular it is `HypertranscendentalNear` at `1`.

## Prior-corpus audit

`MeromorphicPoleJetCertificate.lean` defines `DifferentiallyAlgebraicNear` using an eventual ADE on
the punctured-neighbourhood filter and characterizes its negation by Laurent-row independence and
finite nonzero minors.  It only contained the direction
`HypertranscendentalNear f a → Hypertranscendental f`.

`DigammaGammaLocalHypertranscendence.lean` independently defines `DifferentiallyAlgebraicOn` and
proves `no_local_differential_relation_digamma_comp_Gamma`: no ADE exists on any nonempty open set
inside `digammaGammaRegularSet`.  It also proves that this regular set is open.  No theorem connected
the open-set and punctured-germ interfaces, so the substantive local theorem did not produce
`HypertranscendentalNear`.

No failed-route card asserts this connector is impossible.  The existing formalized pole-jet card
already identifies punctured germs as the correct interface.

## Paper proof

Fix `a ∈ digammaGammaRegularSet` and suppose an ADE is eventually zero in `nhdsWithin a {a}ᶜ`.
Openness of the regular set makes regular-set membership eventual in the same filter.  Intersect
these two eventual properties.  The existing topological lemma
`exists_isOpen_of_eventually_nhdsNE` supplies an open set `W` belonging to the punctured-neighbourhood
filter on which both properties hold pointwise.  That filter is nontrivial over `ℂ`, hence `W` is
nonempty.  Thus the same nonzero differential polynomial is a `DifferentiallyAlgebraicOn` witness on
a nonempty open subset of the regular set, contradicting
`no_local_differential_relation_digamma_comp_Gamma`.

Finally, `1` is regular: `Gamma 1 = 1`, whereas every excluded value is `-m` for `m : ℕ`.

## Hostile review

- **Could the extracted open set be empty?** No. It belongs to `nhdsWithin a {a}ᶜ`, whose
  `NeBot` instance is supplied by the normed-field topology on `ℂ`.
- **Could it leave the regular locus?** No. Regular membership is conjoined before applying the
  open-set extraction lemma.
- **Do the two ADE evaluators differ?** No. Both use the same `Fin.cons` jet ordering encoded by
  `jetVector`; elaboration confirms the witness is definitionally accepted.
- **Does this infer local HT from global HT?** No. It uses the stronger already-proved open-patch
  no-relation theorem, avoiding the generally invalid converse of the existing global bridge.
- **Does the proof assume the target interface?** No. The only hypotheses in the universal theorem
  are explicit regular-point membership; the point-`1` corollary has no proposition premise.

## Novelty classification

This is a missing interface connector between two existing formalizations of local differential
algebraicity.  It is valuable and nontrivial in the corpus, but not a new mathematical result, so no
external novelty claim is made.

## Gate

- [x] exact statement selected after corpus and failed-route audit
- [x] paper proof dependency-closed
- [x] hostile review passed
- [x] scratch Lean proof green
- [x] permanent module direct check
- [x] final umbrella build

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.DigammaGammaHypertranscendentalNear`, wired into the
`GaloisForLFunctions.HTGeometry` umbrella.

| Card statement | Lean declaration |
|---|---|
| connector at every regular point | `hypertranscendentalNear_digamma_comp_Gamma` |
| regularity of `1` | `one_mem_digammaGammaRegularSet` |
| connector at `1` | `hypertranscendentalNear_digamma_comp_Gamma_one` |

Every listed declaration reports exactly `propext`, `Classical.choice`, `Quot.sound`.
