# Formation exchange, joint repair, and ordered-history law

- **ID:** ULF-LSM-3
- **Stage:** 3-formalized
- **Paper source:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/law-saturation-mechanics/formation-exchange-joint-repair-and-ordered-history-law.md`
- **Status:** [LEAN-PROVED] [NO PROJECT AXIOMS] [ROUTE-INDEPENDENT MECHANISM]

## Certified theorem

A constitutive formation on a powerset is an extensive, monotone, idempotent transformation. For
every family of such formations and every source distinction set, Lean certifies a canonical joint
repair characterized by three laws:

1. it contains the source distinctions;
2. every declared formation fixes it;
3. it is contained in every common fixed point above the source.

Every finite word of declared formations remains below this joint repair. For two formations
(C,D), Lean further certifies the exact exchange criterion

\[
CD=DC
\quad\Longleftrightarrow\quad
DC(S)=J_{\{C,D\}}(S)=CD(S)\text{ for every }S.
\]

Thus commuting formations eliminate order memory in one two-step pass, while a failed exchange at
one source state produces two unequal ordered histories.

For three pairwise commuting formations, Lean certifies that all six one-pass schedules equal one
joint repair. Strict closure mechanics therefore cannot produce a genuine three-way coherence
defect.

## Exact scope

- The theorem concerns transformation laws, not a universal carrier object.
- Failed exchange is not declared curvature or cohomology.
- Any future three-way defect must leave the strict pairwise-commuting closure regime.
- Finite arrival at joint repair is not asserted; the separately certified alternating model shows
  that arrival may require stage (omega) while every finite reporter stabilizes.
- Positivity, topology, differential prolongation, and cost enter only through concrete formations;
  they are not inferred from closure axioms.

## Certification

See the companion formalization record. The module is part of the dedicated universal-law-field
umbrella.
- 2026-08-11 — Lean surface audited complete against the card; promoted to stage 3.
