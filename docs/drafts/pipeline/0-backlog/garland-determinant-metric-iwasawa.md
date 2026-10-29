# Determinant metrics and the real loop Iwasawa coordinates

- **Stage:** 0-backlog
- **Type:** BRIDGE / known mathematics
- **Parent:** [Garland loop Eisenstein series](../1-in-progress/garland-loop-eisenstein-over-q.md)
- **Target:** An alternative determinant-norm construction for more general
  affine root data.

**Current role:** unstarted alternative proposal. For the concrete affine
A₁ target, the [compact–Borel normal-form argument](../3-formalized/garland-compact-borel-intersection.md)
is formalized and audited. No determinant implementation or
dependency-closed paper proof was started.
No determinant comparison or metric theorem has been assumed or retired.

## Evidence and current gap

The affine Bruhat theorem and positive Borel coordinates are formalized.
The two simple coefficient-field SL₂ embeddings are formalized and audited in
[their own card](../3-formalized/garland-simple-rank-one-subgroups.md). The
separate normal-form proof now gives the exact sign intersection in affine
A₁ without a determinant comparison.

Corpus searches for a loop Cartan involution and a relative determinant
construction found no such theorem. `DeterminantLine.lean` constructs the
actual finite-dimensional top exterior line and proves rank one and duality;
`RangeDeterminantFormation.lean` gives faithful exterior formation and gauge
covariance. Their statements were inspected, but their transitive audits
and applicability to the construction below remain unchecked.

Liu, *Eisenstein series on loop groups*, §§3.1–3.3,
<https://arxiv.org/abs/1103.4212>, constructs the determinant extension,
compares it with the tame extension, and describes the subgroup generated
by compact rank-one subgroups. This is known mathematics, not a novelty
claim. The argument below is a proposed concrete specialization to SL₂;
it is not yet a dependency-closed paper proof.

## Proposed determinant construction

Let L₀=F[[X]]² in F((X))². Every lattice gL₀ lies between XᴺL₀ and
X⁻ᴺL₀ for some N, by bounding the finitely many entries of g and g⁻¹.
Its quotient modulo XᴺL₀ is a finite-dimensional subspace of the actual
coefficient window with degrees [-N,N). Prove these bounds and finite
quotient identifications before constructing any determinant object.

For commensurable lattices L,M define

    det(L,M) = det(M/(L∩M)) ⊗ det(L/(L∩M))⁻¹.

Construct the canonical transition through any common sublattice and the
associative contraction det(L,M)⊗det(M,N)→det(L,N). The determinant
extension consists of pairs (g,nonzero element of det(L₀,gL₀)); its
multiplication uses g on the second line and this contraction.

Compare this actual extension to the existing inverse-tame Kubota model.
The standard SL₂ representation has index one, but this must be proved
in the concrete construction. Required intermediate checks: canonical
root splittings, the diagonal commutator with X, and the complete cocycle
comparison. Matching a single commutator alone is insufficient.

## Proposed real metric and compact subgroup

Give finite Laurent polynomial vectors the coefficientwise Euclidean inner
product. For a lattice bounded by XᴺL₀, the coefficient window gives a
Euclidean metric on its finite quotient. Increasing N appends an orthogonal
coordinate subspace of canonical volume one. Prove that the induced metric
on the relative determinant line is independent of N and is compatible
with exact-sequence contraction.

A Laurent polynomial matrix k is paraunitary when
k(X⁻¹)ᵀk(X)=1. Such matrices act isometrically on finite Laurent polynomial
vectors. Their lifts of determinant norm one should form a subgroup whose
central kernel is exactly {±1}. Prove this directly from the determinant
metric. Verify that the two actual simple SO₂ embeddings land in it.

If k is paraunitary and lies in the matrix Iwahori, k and k⁻¹ have only
nonnegative degrees. The reciprocal-transpose identity then forces k to be
constant; a constant upper triangular orthogonal matrix has diagonal signs.
Together with the determinant norm, this gives absolute value one for both
Borel torus coordinates in the intersection with the compact subgroup.
This is the precise uniqueness input for the positive Iwasawa coordinates.

## Relation to the completed existence theorem

The two-vertex proof of [real Iwasawa existence](../3-formalized/garland-real-iwasawa-existence.md)
is formalized and audited, including its finite real input. It uses neither
the proposed determinant extension nor its metric. The normal-form route
also completed the rank-one intersection and spherical-function work.

The determinant constructions above remain proposed obligations, with no
proved theorem or Lean implementation claimed. They are outside the paused
programme's current closure work. Arithmetic lattice, quotient measure,
Eisenstein convergence, and constant-term unfolding also remain open in
the parent programme.
