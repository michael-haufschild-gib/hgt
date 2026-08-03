# Hostile referee report

Manuscript: **Two-Sided Singular Defects in Rigged Hilbert Spaces: Classification and Failure of
Automatic Quasi Compatibility**

Standard applied: skeptical referee for a renowned general mathematical journal in the strong
short-paper tier (Proceedings of the AMS / Bulletin of the LMS), not a specialist house report.

Date: 3 August 2026.

## Final recommendation

**Accept after minor editorial revision, subject to independent priority verification.**

Mathematical and expository quality meets publication standard for a renowned general journal’s
short-paper category. Manuscript is not Annals/JAMS/Inventiones scale: mechanism is clean and
decisive but concentrated. At Proceedings AMS / Bulletin LMS tier, resolving two explicit recent
published conjectures, classifying all defects in a natural Hilbert model, and proving sharp
positive replacement theorem is sufficient significance.

Priority caveat is real. Current primary-source, exact-phrase, citation-descendant, and
operator-range searches found no collision, and March 2026 arXiv revision of source paper still
ends with conjectures. Search cannot certify novelty. Author should obtain MathSciNet/zbMATH and
independent expert check before submission. This caveat does not identify mathematical or writing
defect.

## Executive hostile assessment

Initial posture: likely elementary restriction trick dressed as new theory. That attack failed.

Arbitrary restriction would generally lose closedness or one of two density conditions. Paper
proves exact classification, exact necessary-and-sufficient existence criterion, and universal
codimension-one realization. Counterexample is smallest corollary of structural theorem, not
evidence substituted for theorem. Published conjectures predict these conditions force
saturation; explicit model proves otherwise inside standard separable Hilbert space with positive
self-adjoint diagonal operators.

The actual new delta is:

```text
pairing compatibility
    = closed bi-dense subgraphs of canonical inverse-adjoint graph,

proper defect exists
    iff neither graph coordinate controls graph norm
    iff canonical operator is unbounded and not bounded below.
```

This is exact knowledge. Process artifacts, formalization, and terminology are not needed to make
result novel; they only improve verification.

## Round-one objections and disposition

### 1. Definition mismatch could invalidate conjecture refutation

**Attack.** Perhaps manuscript weakens published pre-quasi definition, ignores complete dual pair,
or attacks an obsolete arXiv version.

**Finding.** Published Definition 4.1 was checked. Taking all three spaces equal to one complex
Hilbert space with standard complete anti-dual pairing supplies complete dual pair. Both embeddings
are proved closed, densely defined, injective, and densely ranged. Pairing identity is exact.
Failure is exact `ran C != dom A*`. Published Springer text still states Conjectures 6.7 and 6.8 in
these terms. No mismatch.

**Disposition.** Resolved.

### 2. Canonical partner may be ill-defined

**Attack.** `(A*)^{-1}` is an operator only if `A*` injective; its domain/range density also need
proof.

**Finding.** Dense range of `A` gives `ker A* = 0`. Injectivity of `A` gives dense `ran A*`.
Closed, dense definition of `A` gives closed, densely defined adjoint. Manuscript proves all
claims and pairing identity directly.

**Disposition.** Resolved.

### 3. Classification may be tautological

**Attack.** Saying restrictions correspond to subgraphs is formal repackaging, not result.

**Finding.** Inclusion `C subset (A*)^{-1}` is forced by pairing and is proved. Sufficiency requires
closedness plus density of both graph projections, after which every pre-quasi axiom follows.
Quasi equality is proved equivalent to graph saturation using injectivity. More importantly,
Theorem 4.4 completely solves nontrivial bi-density problem. Classification is load-bearing, not
ornamental.

**Disposition.** Resolved.

### 4. Sharp criterion could hide one-direction gap

**Attack.** Two failed lower bounds need not provide one hyperplane dense under both maps.

**Finding.** Adjoint-surjectivity lemma converts each failure into proper adjoint range. Elementary
two-subspace argument produces one vector outside union of ranges. Orthogonal-complement proof
then shows both hyperplane images dense. Converse uses closed range of restriction under one lower
estimate, followed by density and injectivity. Both directions complete.

**Disposition.** Resolved.

### 5. “Unbounded and not bounded below” equivalence may misuse domain terminology

**Attack.** Graph coordinate lower bound and ordinary operator boundedness are not identical for a
proper domain without closedness.

**Finding.** Paper uses closed, densely defined `B`. Domain-coordinate estimate bounds `B` on its
dense domain; bounded extension plus closed graph forces domain all of `H`. Range-coordinate
estimate is algebraically equivalent to standard lower bound. Exact assumptions are present.

**Disposition.** Resolved.

### 6. Explicit defect graph may not be closed

**Attack.** Image of closed hyperplane under bounded map need not be closed.

**Finding.** Manuscript does not make that invalid inference. Graph parameter map `R=(P,Q)` has
explicit bounded left inverse `S`; convergence of `Rm_n` forces convergence of `m_n`. Hence `R(M)`
closed. This is independently formalized by expressing graph as intersection of continuous
kernels.

**Disposition.** Resolved.

### 7. Dense domain/range could be asserted from dense coordinate ranges incorrectly

**Attack.** Dense `ran P` does not imply dense `P(M)` for proper `M`.

**Finding.** Normal vector `v` is shown outside `ran P*` and `ran Q*`. Hyperplane-image lemma then
proves density by annihilator calculation. In diagonal model, exclusion is explicit: missing
preimages would be constant non-square-summable channels.

**Disposition.** Resolved.

### 8. Self-adjointness/domain claims may be under-specified

**Attack.** Reciprocal diagonal with weights tending both to zero and infinity requires maximal
domains; informal coordinate formula is insufficient.

**Finding.** Revised manuscript displays exact maximal weighted-square-summability domains for
`A` and `B` and invokes standard maximal real diagonal theorem. Lean formalization proves both
self-adjointness statements for exact domains.

**Disposition.** Resolved in revision.

### 9. Strong conjecture does not follow from weak counterexample

**Attack.** Logical relationship may be reversed.

**Finding.** Strong conjecture quantifies over all pre-quasi triples, including Hilbert triples.
One Hilbert counterexample falsifies both. Correct.

**Disposition.** Resolved.

### 10. PDE consequence is overclaimed

**Attack.** Abstract counterexample does not show weak/strong trace spaces differ for Maxwell or
another PDE.

**Finding.** Manuscript explicitly denies that inference. It proves only abstract axioms cannot
force equality. PDE-specific coercivity may place graph on one-sided regular branch; existing
Lipschitz equality remains compatible.

**Disposition.** Resolved.

### 11. “Operator relations” may be terminological inflation

**Attack.** No multivalued singular relation is studied.

**Finding.** Paper says so explicitly. Relation-theoretic content is order interval of closed
single-valued subrelations inside canonical inverse-adjoint graph. It distinguishes graph defect
from multivalued singular part. Title uses “defects,” not “singular linear relations.”

**Disposition.** Resolved.

### 12. Formalization could be theatre

**Attack.** Lean code may prove simplified finite-dimensional statement or assume key density.

**Finding.** Exact infinite-dimensional `ell2(Bool x N)` model is formalized. Both density
statements, closed graph, pairing, non-quasi conclusion, abstract classification, and sharp iff
criterion are unconditional declarations. Direct elaboration and targeted module build pass.
Axiom audit reports only standard Lean logical axioms. No `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe` occurs in module.

**Disposition.** Resolved. Formalization supports result; significance does not depend on it.

## Proof correctness audit

### Proposition 2.2

- Adjoint kernel: correct from dense range.
- Adjoint range density: correct from injectivity.
- Inverse graph closed: coordinate swap of closed adjoint graph.
- Pairing: correct under declared first-variable linear convention.
- Compatibility inclusion: exact adjoint-domain characterization.

No gap found.

### Theorem 3.1

- Necessity: graph inclusion, closedness, both density projections checked.
- Sufficiency: first projection injective on graph, so subspace remains graph of operator.
- Negative injectivity inherited from canonical partner.
- Quasi iff full graph: uses equality of ranges plus canonical injectivity; correct.

No gap found.

### Lemmas 4.1--4.2 and Theorem 4.4

- Open mapping use in surjective-adjoint direction: valid Hilbert/Banach spaces.
- Lower bound closes range; dense range makes operator onto.
- Adjoint order in `T*(T^{-1})* = I`: correct.
- Hyperplane annihilator calculation: complete.
- One vector outside union of two proper linear subspaces: explicit three-case proof, valid over
  complex field.
- Converse: closed subspace completeness used; injectivity then forces saturation.

No gap found.

### Corollary 4.5

- Domain projection estimate iff closed operator is everywhere bounded: proof includes dense-domain
  extension and closedness.
- Range projection estimate iff standard lower bound: direct graph-norm algebra.

No gap found.

### Theorem 5.1

- `P,Q`: bounded positive self-adjoint contractions, injective, dense range.
- `R`: bounded below through explicit recovery map.
- `A,B`: exact maximal positive self-adjoint diagonals and inverses.
- `v`: square summable but outside both adjoint ranges.
- `M=v-perp`: proper; both images dense.
- `C`: closed, injective, dense-domain, dense-range.
- Pairing: follows from commuting self-adjoint diagonals.
- Non-quasi: `ran C=Q(M)` proper in `ran Q=dom A*`.

No gap found.

## Novelty audit under adversarial standard

The basic lemmas are classical or one-line consequences of classical results. Manuscript does not
claim otherwise. Novelty rests on exact assembly and consequences:

- published automaticity conjectures are answered negatively;
- all compatible standard-Hilbert defects are classified;
- failure boundary is necessary and sufficient, not example-specific;
- strongest positive survivor is stated;
- defect can always have graph codimension one;
- example is positive self-adjoint and separable.

Searches found parent mechanisms, not theorem. No current collision detected. Because no
independent database access or expert testimony was available, priority remains provisional.

## Significance audit

### Reasons to publish in renowned general short-paper venue

1. Resolves two explicit published conjectures from recent operator/rigged-space literature.
2. Gives conceptual mechanism and full sharp boundary, preventing counterexample from being an
   isolated trick.
3. Positive replacement theorem tells applications exactly what extra estimate suffices.
4. Construction uses familiar objects and proof is accessible beyond narrow specialty.
5. Paper is self-contained, concise, and machine-audited without depending on machine search.

### Reasons not to claim elite top-general significance

1. Core Hilbert geometry is elementary once canonical graph is isolated.
2. Classification is proved in standard Hilbert anti-dual model, not full Banach framework.
3. No concrete PDE trace counterexample or new PDE theorem is supplied.
4. Broader consequences are diagnostic rather than a new large theory.

These limits calibrate venue; they do not undermine strong short-paper publishability.

## Presentation and artifact audit

- Manuscript is 10 pages after compilation, appropriate for short theorem paper.
- Abstract names exact conjecture outcome, structural theorem, criterion, example, and Lean status.
- Definitions precede use; scalar convention declared.
- Every main theorem has complete proof.
- Scope restrictions and PDE non-implication are explicit.
- References point to primary sources.
- PDF visually inspected page by page; no clipping, overlap, unreadable symbols, or broken citation
  tokens after revision.
- Initial literal `qquad` artifacts and long-code overflow were found by visual audit and fixed.

## Publication-level verdict

**Confirmed at Proceedings AMS / Bulletin LMS short-paper quality, conditional only on independent
priority verification and ordinary copy-editing.**

This is strong, novel-looking, and significant enough for a renowned general mathematical journal
at that tier. It should not be marketed as top-tier general-mathematics breakthrough or as a PDE
counterexample. Those stronger claims would not survive review.
