# Wick-contracted directed persistence law

- **ID:** WCDMF-PERSIST
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `quantum-matroid-pro-observable-field.md` (open core Q1/O1) ·
  `wick-contracted-differential-matroid-field.md` (persistence criterion)
- **Statement:** For a finitary matroid `M` and a nonempty `⊆`-directed base family `(C_i)`, a
  signal set is independent in the face-complete contraction `M ／ ⋃ᵢ C_i` exactly when it is
  independent in every finite-stage contraction `M ／ C_i`; hence the WCDMF persistence criterion
  is a theorem, not a definition, at the undecorated skeleton level.

## Goal

The WCDMF card postulates: *"A physical interaction law is a circuit, nonloop, or free flat that
survives every cofinal admissible refinement"* — labeled `[CONJECTURE]` because it was not known
whether stage-wise survival captures the face-complete limit.  This card proves the equivalence
for the undecorated skeleton: the face-complete contracted matroid's independent sets are exactly
the persistently independent sets.  Consequences:

1. the directed system of base refinements is coherent at the independence level (the O1
   coherence half for the skeleton);
2. intrinsic hypertranscendence of a vertical jet fibre over the face-complete base is exactly
   stage-persistent freeness — freedom cannot be destroyed "only in the limit";
3. dually, collapse is finite-stage detectable: if the face-complete base explains a signal
   packet, some single stage already explains it.

This is `[BRIDGE]` infrastructure: the mechanism (finite character of dependence in a finitary
matroid) is parent mathematics, and an infinite-matroid specialist could derive it routinely.
No novelty is claimed.  Its value is that the pro-matroid object of the WCDMF programme becomes
well-defined with its limit law proved, unconditionally, over any ambient matroid — including
`differentialMatroid F E`, which is finitary by construction.

## Exact statement

Let `M` be a matroid on ground type `α` satisfying the finitarity axiom: a set is independent as
soon as all its finite subsets are.  Let `ι` be nonempty, `C : ι → Set α` directed under `⊆`, and
`U = ⋃ᵢ C i`.  Then for every `I : Set α`:

```text
(M ／ U).Indep I  ↔  ∀ i, (M ／ C i).Indep I.
```

Corollaries.

1. (Monotone destruction / quotient direction.)  `C ⊆ C'` implies
   `(M ／ C').Indep I → (M ／ C).Indep I`: refinement can destroy, never create, independence.
2. (Nonloop persistence.)  With `I = {e}`: `e` is a nonloop of the face-complete contraction iff
   it is a nonloop at every stage.
3. (Signal-window form.)  For the Wick interaction matroid `(M ／ base) ↾ signal` the same
   equivalence holds stage-wise on any signal window.
4. (Differential instantiation.)  `M = differentialMatroid F E` is finitary, so the interaction
   skeleton of a differential field extension satisfies the persistence law for every directed
   family of face bases.

## Paper proof `[PROVED HERE]`

Write `N ／ C` for matroid contraction, `N ↾ S` for restriction.  We use three parent facts from
finite/infinite matroid theory, all available for arbitrary `Matroid α` in the
Bruhn–Diestel–Kriesell–Pendavingh–Wollan axiomatization:

- (F1) `contract-contract`: `(M ／ C₁) ／ C₂ = M ／ (C₁ ∪ C₂)`.
- (F2) contraction independence via a basis: if `J` is a basis' of `X` in `M`, then
  `(M ／ X).Indep I ↔ M.Indep (I ∪ J) ∧ Disjoint X I`; every set has a basis'; every independent
  subset of `X` extends to a basis' of `X`.
- (F3) independence in a contraction implies independence upstairs:
  `(M ／ C).Indep I → M.Indep I`.

**(⇒)** Fix `i`.  Since `C i ⊆ U`, `C i ∪ U = U`, so by (F1)
`M ／ U = M ／ (C i ∪ U) = (M ／ C i) ／ U`.  If `I` is independent in `M ／ U`, it is independent
in `(M ／ C i) ／ U`, hence by (F3) independent in `M ／ C i`.  (Neither finitarity nor
directedness is used.)

**(⇐)** Assume `(M ／ C i).Indep I` for every `i`.

*Disjointness.*  For each `i`, independence in `M ／ C i` puts `I` inside the contracted ground
set `M.E \ C i`, so `I` is disjoint from every `C i`, hence from `U`.

*Independence.*  Choose a basis' `J` of `U` in `M` (F2).  By (F2) it suffices to prove
`M.Indep (I ∪ J)`.  By finitarity it suffices to prove `M.Indep K` for every finite
`K ⊆ I ∪ J`.  Split `K = (K ∩ I) ∪ (K ∩ J)`.  The finite set `K ∩ J` lies in `J ⊆ U`; since the
family is nonempty and directed, a finite subset of the directed union lies in a single member:
there is `i₀` with `K ∩ J ⊆ C i₀`.  Now `K ∩ J` is independent (a subset of the independent
`J`) and contained in `C i₀`, so by (F2) it extends to a basis' `J₀` of `C i₀`.  Applying (F2)
with the basis' `J₀` to the stage hypothesis `(M ／ C i₀).Indep I` yields `M.Indep (I ∪ J₀)`.
Finally `K = (K ∩ I) ∪ (K ∩ J) ⊆ I ∪ J₀`, so `K` is independent as a subset of an independent
set.  ∎

**Corollary 1.**  `C ⊆ C'` gives `C ∪ (C' \ C) = C'`, so by (F1)
`M ／ C' = (M ／ C) ／ (C' \ C)` and (F3) applies.  ∎

**Corollaries 2–4** are direct instantiations (singleton `I`; conjunction with the restriction
membership `I ⊆ signal`, using nonemptiness of `ι` to pull the constant conjunct out of the
universal quantifier; the finitarity instance of `differentialMatroid`).  ∎

### Hypothesis audit

- *Finitarity* is load-bearing in (⇐): without finite character, dependence of `I ∪ J` need not
  descend to a finite witness, and the limit contraction of a non-finitary matroid can acquire
  new dependencies not seen at any stage.
- *Directedness* is load-bearing.  Counterexample without it: in a rank-2 linear matroid take
  independent `a, b` and `x = a + b`, with `C₁ = {a}`, `C₂ = {b}`.  Then `{x}` is independent in
  `M ／ C₁` and in `M ／ C₂` (`x ∉ span{a}`, `x ∉ span{b}`), but `x ∈ span{a, b}` is a loop of
  `M ／ (C₁ ∪ C₂)`.
- *Nonemptiness* is load-bearing: for the empty family the right side is vacuous while the left
  side is independence in `M ／ ∅ = M`.

## Gates

- [x] 0 → 1  in-progress: exact statement, parent facts identified, hypothesis audit done
- [x] 1 → 2  fully-proven: complete paper proof above, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in `HTGeometry/WickContractedMatroidPersistence.lean`,
      targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready

## What this opens

The skeleton persistence law splits the WCDMF persistence criterion cleanly: the undecorated
layer is now a theorem, so the *decorated* persistence question is isolated — do circuit
equations, valuations, and phase/period data also pass to directed limits, or does enrichment
break compactness?  That is the exact next representation question for O2.  A second opening:
the relative reading `(differentialMatroid F E ／ G).Indep I ↔ DiffIndepOn` over the
`G`-generated differential field requires insensitivity of differential independence to
differential-algebraic base extensions — a named, self-contained next lemma.

## Log

- 2026-07-17 — created in 1-in-progress with complete paper proof; hostile audit recorded
  (finitarity/directedness/nonemptiness all load-bearing, with counterexample); classified
  `[BRIDGE]`, novelty not claimed.
