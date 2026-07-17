# Wick-contracted intrinsic face reading

- **ID:** WCDMF-INTRINSIC
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `wick-contracted-relative-reading.md` (its recorded open core) ·
  `quantum-matroid-pro-observable-field.md` (Q1 semantics)
- **Statement:** Differential independence survives adjoining differentially algebraic elements
  to the base (one at a time, hence any finite packet), and consequently the Wick contraction of
  the differential-transcendence matroid has a basis-free reading: contracted independence of a
  signal set equals relative differential independence over the face field of every finite base
  stage.

## Goal

The relative-reading card interprets `M ／ G` through a chosen transcendence basis `J` of `G`;
its recorded gap was the upgrade from the basis field `F⟨J⟩` to face fields with the base's own
generators.  This card closes the finite-stage form of that gap with a differential
Kolchin-style insensitivity theorem, giving the intrinsic (basis-free) semantics the physics
requires: the interaction matroid of the WCDMF programme measures relative differential
independence over the actual finite Gaussian/Wick face fields, with no auxiliary choice.

`[BRIDGE]`: the mechanism is differential-algebraic transitivity (corpus) plus the directed
persistence law; the statement family is classical in spirit (Kolchin's dtrdeg calculus).  No
novelty is claimed.

## Exact statements

Fix a characteristic-zero differential field extension throughout.

**A (one-step base insensitivity).**  If `g` is differentially algebraic over `k` and `I` is
differentially independent over `k`, then `I` is differentially independent over `k⟨g⟩`.

**B (finite base extension).**  If every element of a finite packet `G₀` is differentially
algebraic over `F⟨S⟩` and `I` is differentially independent over `F⟨S⟩`, then `I` is
differentially independent over `F⟨S ∪ G₀⟩`.

**C (basis-free finite-stage intrinsic reading).**  In the differential matroid `M` of `E/F`,
for every base `G` and signal `I`:

```text
(M ／ G).Indep I  ↔  Disjoint G I  ∧  ∀ finite G₀ ⊆ G,  DiffIndepOn F⟨G₀⟩ I.
```

## Paper proof `[PROVED HERE]`

**A.**  By finitarity it suffices to treat finite `t ⊆ I`, by induction.  `t = ∅` is trivial.
For `insert a t'` with `a ∉ t'`, the insert criterion over `k⟨g⟩` requires (i) independence of
`t'` — the induction hypothesis — and (ii) that `a` is not differentially algebraic over
`k⟨g⟩⟨t'⟩`.  Suppose it were.  The adjoin tower collapses: `k⟨g⟩⟨t'⟩ = k⟨{g} ∪ t'⟩ =
k⟨t'⟩⟨g⟩`.  The element `g` is differentially algebraic over `k`, hence over the larger
derivation-closed field `k⟨t'⟩` (tower monotonicity).  Single-element differential-algebraic
transitivity over the base `k⟨t'⟩` then makes `a` differentially algebraic over `k⟨t'⟩` —
contradicting the insert criterion for `insert a t' ⊆ I` over `k`.  ∎

**B.**  Induction on the finite packet.  The step adjoins one `g` to the base `F⟨S ∪ G₀'⟩`:
`g` is differentially algebraic there by derivation-closed enlargement of `F⟨S⟩`, so Theorem A
applies, and `(F⟨S ∪ G₀'⟩)⟨g⟩ = F⟨S ∪ G₀' ∪ {g}⟩` collapses the tower.  ∎

**C.**  (⇒)  Independence in `M ／ G` forces disjointness from `G` (ground-set membership).
For finite `G₀ ⊆ G`, monotone destruction gives independence in `M ／ G₀`.  Choose a basis'
`J₀` of `G₀`; the relative reading yields differential independence over `F⟨J₀⟩`.  Every
`g ∈ G₀` lies in the matroid closure of `J₀` (a basis' has the closure of its span), which on
independent sets is the differential-algebraic closure; hence every `g ∈ G₀` is differentially
algebraic over `F⟨J₀⟩`, and Theorem B upgrades independence to `F⟨J₀ ∪ G₀⟩ = F⟨G₀⟩`.

(⇐)  The finite subsets of `G` form a nonempty directed family with union `G`, so by the
directed persistence law it suffices to verify independence in `M ／ G₀` for each finite
`G₀ ⊆ G`.  Choose a basis' `J₀` of `G₀`.  The hypothesis at `G₀` restricts down along
`F⟨J₀⟩ ≤ F⟨G₀⟩` (independence descends to subfields), and the relative reading (backward)
applies with disjointness inherited from `Disjoint G I`.  ∎

### Hypothesis audit

- Characteristic zero enters only through the corpus transitivity theorem.
- In A, differential algebraicity of `g` is essential: adjoining a differentially
  transcendental `g` can kill independence (`g := a′` for `a ∈ I`).
- C is stated with finite stages on purpose: the single-limit-field form
  `DiffIndepOn F⟨G⟩ I` for infinite `G` needs a directed-union coefficient lemma for algebraic
  independence over nested subfields; that remains the exact `[OPEN CORE]` of the semantics
  thread.  For physics the finite-stage form is the operational one: face data is tested at
  finite resolution.

## Gates

- [x] 0 → 1  in-progress: exact statements, mechanism identified, hypothesis audit done
- [x] 1 → 2  fully-proven: complete paper proof above, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems appended to
      `HTGeometry/WickContractedMatroidPersistence.lean`
      (`diffIndepOn_differentialAdjoin_singleton_of_differentialAlgebraicOver`,
      `diffIndepOn_differentialAdjoin_union_finite_of_differentialAlgebraicOver`,
      `differentialMatroid_contract_indep_iff_forall_finite_stage`, plus the two nested-iff
      bridges), targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready

## What this opens

With intrinsic finite-stage semantics in hand, the decorated question (O2) becomes: the circuit
ideal of `I_w` over `F⟨G₀⟩` is now canonical per stage — do these ideals form a directed system
under stage refinement with a persistence law, or does enrichment break compactness?  And the
directed-union coefficient lemma is the last purely field-theoretic gap between the finite-stage
and limit-field readings.

## Log

- 2026-07-17 — created with complete paper proof (A: insert-induction against transitivity;
  B: packet induction; C: chaining monotone destruction, relative reading, closure
  identification, and directed persistence); classified `[BRIDGE]`.
- 2026-07-17 — formalized and verified same day: single-module rebuild green, axiom audit PASS
  (`[propext, Classical.choice, Quot.sound]` only); moved to 3-formalized.
