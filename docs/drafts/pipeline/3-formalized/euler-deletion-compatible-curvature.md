# Compatible attenuation curvature invariant

**Stage:** 3-formalized. **RH implication:** none. **Novelty:** not certified.

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionCompatibleCurvature.lean`.
Namespace: `RHTower.DeletionCompatibleCurvature`.

The module defines the actual coefficients `A_d(n)=1-(d/b(d))*[d|n]`, their
squared source mass `b(n)^2*n^(-alpha)`, and the original four curvature channels.
It proves their pointwise linearization, infinite divisibility reindexing, and
absolute summability before calculating their sum.

`curvature_eq` factors that sum into positive prefactors and `1-r^(2-alpha)`.
`curvature_neg`, `curvature_zero_at_two`, `curvature_pos`, and
`curvature_eq_zero_iff` give the complete sign and vanishing boundary for
pairwise coprime labels greater than one. These are general theorems with explicit
positivity, contractivity, multiplicativity, and convergence conditions; no
unproved arithmetic premise is supplied.

`normalized_curvature_invariant` proves exact equality with the original
normalized curvature whenever `b(p)=b(q)=1`.
`fifth_attenuation_normalized_curvature` instantiates every `0<c<=1` in the
actual coefficient family `c^(v_5(n))`. The premise-free
`fifth_attenuation_curvature_boundary` fixes `c=1/5` and proves multiplier 25,
negative curvature at `3/2`, zero at two, and positive curvature at three.

Validation: `lake env lean /tmp/hgt-compatible-curvature-Pe4gsu/Audit.lean`
passed. Eight axiom audits, covering the pointwise identity, infinite reindexing,
summability, factorization, zero boundary, two normalized invariants, and fixed
capstone, report only `propext`, `Classical.choice`, and `Quot.sound`.
Production matches the audited scratch body. The narrow final
`lake build GaloisForLFunctions.RHTower.EulerDeletionCompatibleCurvature` passed.
Its umbrella import is wired. No full or umbrella build ran; no computational
experiment or external proof certificate was used. Repository-wide
`scripts/formal_tools.py lint` passed; output is
`/tmp/hgt-compatible-curvature-Pe4gsu/lint.log`. All owned Lean, build, and lint
processes completed.

The [paper proof](../2-fully-proven/euler-deletion-compatible-curvature.md) gives
the source-admission and literature boundaries. The result closes the
[compatible attenuation repair](../5-failed/euler-deletion-compatible-attenuation-repair.md)
with an exact positive invariant. It supplies no identity forced by a zeta zero
and does not exclude off-line zeros.
