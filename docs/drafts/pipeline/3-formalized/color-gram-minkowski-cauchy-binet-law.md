# Colour Gram Cauchy--Binet law

- **ID:** `color-gram-minkowski-cauchy-binet-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVEN] [REDISCOVERED] [BRIDGE]`
- **Physical parent:** `../1-in-progress/color-blind-event-gram-spacetime-law.md`
- **Paper parent:** `../2-fully-proven/not_new_scientific_knowledge/color-gram-minkowski-orbit-theorem.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiCone.lean`

## Exact theorem

Let
\[
X\in M_{3,2}(\mathbb C),\qquad G_X=X^\dagger X.
\]
Write the two columns of \(X\) as \(u,v\in\mathbb C^3\), and define
\[
t=\frac{\lVert u\rVert^2+\lVert v\rVert^2}{2},\qquad
z=\frac{\lVert u\rVert^2-\lVert v\rVert^2}{2},\qquad
x+iy=\langle u,v\rangle.
\]
Then all of the following are unconditional:

1. \(G_X\) is positive semidefinite and Hermitian.
2. \(\operatorname{rank}(G_X)=\operatorname{rank}(X)\).
3. \(G_X\) is the Lorentz-Hermitian matrix of \((t,x,y,z)\).
4. For every \(U\) with \(U^\dagger U=I_3\),
   \[
   G_{UX}=G_X.
   \]
5. For every \(V\in M_2(\mathbb C)\),
   \[
   G_{XV^\dagger}=VG_XV^\dagger.
   \]
6. If
   \[
   \Delta_{ij}=u_i v_j-u_jv_i,
   \]
   then the exact \(3\times2\) Cauchy--Binet identity is
   \[
   t^2-x^2-y^2-z^2
   =|\Delta_{01}|^2+|\Delta_{02}|^2+|\Delta_{12}|^2.
   \]
7. Consequently
   \[
   t\ge0,\qquad t^2-x^2-y^2-z^2\ge0.
   \]
8. The Lorentz quadratic form vanishes exactly when all three maximal minors vanish, and it is
   strictly positive exactly when at least one maximal minor is nonzero.
9. Every event supported on one left row maps to the Lorentz-null boundary.

Thus forgetting the left three-frame maps every event into the closed Minkowski future cone, and
its null/timelike causal stratum is exactly its maximal-minor rank stratum.

## Lean realization

The central declarations are:

- `colorGramMatrix_eq_lorentzHermitianMatrix`;
- `colorGramLorentzMassSq_eq_minorEnergy`;
- `colorGramMatrix_posSemidef`;
- `colorGramMatrix_isHermitian`;
- `colorGramMatrix_rank`;
- `colorGramMatrix_left_invariant`;
- `colorGramMatrix_right_covariant`;
- `colorGramMatrix_left_right_covariant`;
- `colorGramMatrix_det`;
- `colorGramMatrix_det_eq_minorEnergy`;
- `colorGramTime_nonneg`;
- `colorGramLorentzMassSq_nonneg`;
- `colorGramLorentzMassSq_eq_zero_iff`;
- `colorGramLorentzMassSq_pos_iff`;
- `singleColorEvent_lorentz_null`.

Focused verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ColorGramMinkowskiCone.lean
lake build GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone
```

Both pass. `#print axioms` reports only Lean/mathlib foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

## Formal boundary

This card does **not** formalize:

- equality of Gram matrices iff equality of \(U(3)\)-orbits;
- surjectivity onto every positive-semidefinite Hermitian \(2\times2\) matrix;
- the quotient-space homeomorphism;
- any physical rule selecting the left orbit as observational equivalence;
- spacetime incidence, a tetrad, a connection, field equations, or a prediction.

Those first three statements remain dependency-closed on paper in the paper parent. The physical
claims remain conjectural in the physical parent.

## Novelty boundary

The theorem is standard finite-dimensional Gram/Cauchy--Binet and Pauli-cone mathematics. Its
formalization is new infrastructure for this corpus, not new scientific knowledge. Possible
scientific novelty begins only if exceptional event composition forces this quotient and its
connection simultaneously produces gravity and the Standard Model forces.

## Gates

- [x] exact theorem dependency-closed on paper
- [x] exact algebraic statement formalized unconditionally in Lean
- [x] focused source check, focused build, and axiom audit pass
- [x] mathematical novelty classified as rediscovered
- [ ] exceptional physical selection and descent proved
- [ ] quotient topology formalized before any manuscript uses it as a theorem

## Log

- 2026-07-29 — formalized the colour Gram matrix, Lorentz coordinates, exact
  Cauchy--Binet/minor identity, causal inequalities, null/timelike criterion, left invariance,
  right covariance, and rank preservation.
