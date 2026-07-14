# Graded Hodge supertrace compression

- **ID:** graded-hodge-supertrace-compression
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** [BRIDGE] supersymmetric/BRST grading, Witten supertrace, and Hodge compression
- **Statement:** For a finite graded complex with grading operator `Γ`, an odd differential `d`,
  Hodge relation `1-P=dh+hd`, and a resolvent commuting with `d`, the graded trace of the full
  resolvent equals the graded trace of its harmonic compression.

## Goal

Correct and strengthen the seam-compression algebra.  The current legacy lemma proves ordinary
trace cyclicity for the ordinary commutator `dX-Xd`; it does not encode a supertrace or the odd
supercommutator required by the Hodge relation.  Preserve that valid lemma for compatibility, then
add the genuine graded statement used in supersymmetric quantum mechanics and BRST cohomology.

## Gates

- [x] 0 → 1  in-progress: sign gap isolated, graded repair and direct consumer identified
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: targeted Lean check green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper and Lean certificate

## Physics relation

Let `Γ` be the boson/fermion grading and define `Str_Γ(A)=Tr(ΓA)`.  Oddness of `d` is

`Γd=-dΓ`.

Trace cyclicity then gives

`Str_Γ(dX+Xd)=0`.

If `1-P=dh+hd` and `d Res=Res d`, then

`(1-P)Res=d(h Res)+(h Res)d`,

so `Str_Γ(Res)=Str_Γ(P Res)`.  This is the finite algebra underlying Witten-index localization and
BRST/Hodge compression.  Physics sources include Witten's supersymmetric index formulation
(arXiv:hep-th/0006010), BRST Hodge decompositions (arXiv:hep-th/9808040 and
arXiv:hep-th/0004145), and Witten-Laplacian supersymmetry (arXiv:1607.08714).

## Corpus application

- Strengthen `RHTower/SeamSuspensionTrace.lean` with a real grading-aware trace.
- Consume the Hodge relation produced by `HTGeometry/BRSTHodgeConstraint.lean` once the seam's
  source-specific harmonic projection and Green operator exist.
- Discharge separate resolvent/differential commutation from two-sided inverse equations and
  commutation of the inverted generator with the differential.
- Remove the sign ambiguity between the legacy ordinary commutator theorem and the Hodge
  anticommutator used in the file's prose.

## Direct-application audit

This directly repairs the finite seam-compression theorem surface.  It does not provide the
infinite/renormalized cyclicity, the seam grading operator, or the source Green operator; those
remain the actual analytic open cores.  No RH conclusion follows from the finite identity alone.

The live `fermionic-fe-projector-lefschetz-rh.md` route previously cited the legacy ordinary-trace
lemma for its proposed `dH+Hd=1-P` contraction.  That dependency now points to the grading-correct
theorem.  The change removes a sign/interface error but leaves the route's source Green-homotopy
construction open.

## Verification boundary

Source-level formalization only.  Per user instruction, no Lean process, build, lint, numerical
experiment, or axiom audit is run during this phase.

## Log

- 2026-07-14 — legacy ordinary-trace/supertrace sign mismatch identified by applying the BRST
  Hodge relation to the live seam-compression consumer; graded repair isolated before Lean edits.
- 2026-07-14 — source-level `gradedMatrixTrace`, odd-anticommutator cancellation, and finite Hodge-compression declarations added beside the preserved legacy ordinary-trace lemmas.  No computation or build run.
- 2026-07-14 — source-level two-sided-inverse commutation discharge and resolvent-form graded compression added; no computation or build run.
