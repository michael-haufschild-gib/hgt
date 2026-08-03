# Hostile referee report

## Recommendation

**Conditional accept for a renowned broad mathematical journal in the
Mathematika / Mathematische Zeitschrift / Proceedings of the AMS band,
provided an independent operator-range expert confirms priority.**

Paper clears mathematical-correctness, proof-completeness, presentation, and
significance bars for that band. It does **not** currently clear Annals / JAMS
/ Inventiones / Acta tier. An Advances in Mathematics submission would be
high-risk without wider application or evidence that countable
common-avoidance theorem resolves a recognized open problem.

This is not an unconditional priority certificate. Search and internal review
cannot replace MathSciNet/zbMATH coverage plus an expert referee.

## What is genuinely new-looking

Elementary observer--annihilator equivalence is not novelty. Neither is fact
that countably many proper operator ranges cannot cover a Banach space: Baire
category already gives that.

New-looking core is stronger:

> A countable family of noncoercive injective dense-range Hilbert observers
> admits one closed infinite-dimensional common normal subspace disjoint from
> every adjoint range, even when algebraic span of those ranges is whole
> source. Every closed subspace of that common normal generates a simultaneous
> dense-image defect.

Equivalently, paper upgrades a Baire noncoverage vector to a closed
infinite-dimensional spaceable complement without a nonclosedness hypothesis
on combined span. Construction is simultaneous, hereditary, and requires no
commutation, spectral model, compactness, or joint lower bound.

Arbitrary-family coverage--rigidity law identifies invariant of which
countable theorem is a consequence:

    global closed dense-image rigidity
      iff pointwise coverage by adjoint ranges.

For countable injective dense-range families, weaving theorem proves coverage
is possible exactly when one observer is coercive.

## Hostile attempts to reduce result

### 1. Reduction to Baire category

Fails. Baire category produces a vector outside a countable union of proper
operator ranges. It does not produce a closed infinite-dimensional subspace
disjoint from union, much less hereditary lattice.

### 2. Reduction to Kitson--Timoney

Fails in intended regime. Their theorem gives spaceability of complement of
algebraic span of countably many ranges when that span is nonclosed. Here span
may be all of Hilbert space.

### 3. Reduction to Araújo--Barbosa--Baganha Raposo--Ribeiro

No direct reduction was located. Their general criterion assumes structural
conditions on union, including cases where union is itself a subspace of
infinite codimension. Observer ranges here need not form a chain or a
subspace under union.

### 4. Reduction to 2025 Ribeiro preprint

Fails. Its proved theorem retains hypothesis that span of ranges is
nonclosed. Arbitrary-family reduction in Remark 4.1 uses complement inclusion
in wrong direction near its final step: from Y0 contained in Y, avoidance of
Y0 does not imply avoidance of Y.

### 5. Reduction to one-range Hilbert operator-range theory

Fails for simultaneous statement. Fillmore--Williams, Dixmier/von
Neumann-type results, and later spaceability results handle one range or a
combined range under additional hypotheses. They do not, in sources checked,
supply a single common closed normal for an unrelated countable family whose
span may already be source.

### 6. Hidden spectral or stability assumption

None. Proof uses only finite-codimensional persistence of nonclosed range,
recursive orthonormal small vectors, square-summable observer weights, and
coefficient estimates.

## Correctness audit

### Paper proof

- Observer--annihilator equivalence: correct.
- Coverage--rigidity equivalence: correct; nonemptiness of index set handles
  zero vector in converse.
- Finite-codimensional persistence: correct.
- Countable orthonormal schedule: dependency closed.
- Woven coefficient space: closed and contains a countable linearly
  independent family.
- Adjoint-range avoidance estimate: division is only by positive weights;
  limit argument forces every base coefficient to vanish.
- Coercive branch: closed image plus density gives surjectivity; injectivity
  forces full source.
- Two-marginal relation criterion and pre-quasi graph application: logically
  downstream of same observer law.

No mathematical gap was found.

### Lean proof

Every numbered theorem, lemma, corollary, and model assertion is mapped in
CLAIM_TRACE_AUDIT.md to a compiled declaration. Headline declarations include:

- dense_images_iff_orthogonal_avoids_adjointRanges;
- closed_common_avoidance_rigid_iff_adjointRanges_cover;
- closed_common_dense_image_rigid_iff_adjointRanges_cover;
- hilbertRangeSingular_domRestrict_orthogonal;
- exists_countable_singular_orthonormalArray;
- countable_observer_coercivity_wildness_law;
- twoSidedSingular_iff_hasProperClosedBiDenseSubspace;
- preQuasi_graph_le_canonical_graph;
- preQuasi_quasi_iff_eq_canonicalNegative;
- exists_hilbertPreQuasiPair_not_quasi;
- not_every_hilbertPreQuasiPair_is_quasi.

Audit results:

- direct lake env lean elaboration: PASS;
- targeted lake build of
  GaloisForLFunctions.RHTower.PythagoreanObserverBlindness: PASS;
- global formal lint: PASS;
- umbrella import: PASS;
- no sorry, admit, user axiom, opaque, or unsafe declaration;
- axiom report: only propext, Classical.choice, Quot.sound.

Thus all retained mathematical claims are unconditionally proved in Lean in
normal mathlib foundational sense.

## Significance audit

### Positive

1. Exact universal invariant: pointwise adjoint-range coverage.
2. Span-free countable spaceability theorem.
3. Hereditary closed-subspace lattice, not one witness.
4. Explicit constructive Hilbert proof rather than existence-only Baire
   argument.
5. Direct relation-chart and rigged-Hilbert interpretation.
6. Complete Lean formalization provides unusually strong verification.

### Limitations

1. Countable family only; uncountable common avoidance remains open.
2. Hilbertian; no Banach analogue is proved.
3. Universal coverage law itself is elementary once observer duality is seen.
4. Rigged-Hilbert application is abstract, not a concrete PDE trace theorem.
5. Bibliographic priority remains externally unverified.

## Presentation audit

Seven-page manuscript is concise, mathematically self-contained, and visually
clean. It now explicitly separates:

- known Baire noncoverage;
- known span-nonclosed spaceability;
- new-looking span-free common closed avoidance;
- independently unverified priority.

No overclaim remains. Formal declaration list is excluded from manuscript and
retained only in private audit ledger.

## Final hostile verdict

**Mathematical quality: PASS.**

**Unconditional Lean coverage of all mathematical claims: PASS.**

**Novelty against sources checked: PASS, provisional.**

**Significance for a renowned broad journal: PASS for
Mathematika / Mathematische Zeitschrift / Proceedings of the AMS tier.**

**Flagship-general significance: FAIL on current evidence.**

**External priority certification: OPEN.**

Paper is submission-ready only with venue claim calibrated as above. No
honest internal process can turn remaining external-priority condition into
certainty.
