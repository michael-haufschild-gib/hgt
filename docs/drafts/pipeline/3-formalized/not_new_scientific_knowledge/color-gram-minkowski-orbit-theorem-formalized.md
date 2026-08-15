# Colour Gram orbit and positive-cone quotient theorem

- **ID:** `color-gram-minkowski-orbit-theorem-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [REDISCOVERED] [BRIDGE]`
- **Paper parent:** `color-gram-minkowski-orbit-theorem.md`
- **Physical parent:** `../../1-in-progress/color-blind-event-gram-spacetime-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiOrbit.lean`

## Exact theorem

For \(X,Y\in M_{3,2}(\mathbb C)\), define
\[
\Gamma(X)=X^\dagger X.
\]
Then Lean proves unconditionally:

1. \(\Gamma(X)=\Gamma(Y)\) if and only if there exists
   \(U\in M_3(\mathbb C)\) with
   \[
   U^\dagger U=I_3,\qquad UX=Y.
   \]
2. Every positive-semidefinite \(H\in M_2(\mathbb C)\) is \(\Gamma(X)\) for some
   \(X\in M_{3,2}(\mathbb C)\).
3. The Gram map is continuous as a map into the nonnegative two-cone.
4. Embedding the positive square root of \(H\) in the first two rows gives a continuous right
   inverse of the Gram map.
5. The quotient by equality of Gram records is homeomorphic to the nonnegative two-cone:
   \[
   M_{3,2}(\mathbb C)/{\ker\Gamma}
   \cong_{\rm homeo}
   \{H\in M_2(\mathbb C):0\le H\}.
   \]
6. The kernel equivalence relation in part 5 is exactly left-unitary orbit equivalence by part 1.

Together with
`formal/GaloisForLFunctions/HTGeometry/ColorGramMinkowskiCone.lean`, this formalizes the complete
paper theorem identifying the left-unitary orbit space with the closed Minkowski future cone.
On the regular locus, unitary orbit existence is sharpened to special-unitary orbit existence in
`color-gram-special-unitary-orbit.md`.

## Proof architecture

Equal Gram matrices give equal kernels. They induce a well-defined linear equivalence between the
ranges of \(X\) and \(Y\). Equality of Gram inner products makes this range equivalence an
isometry. `LinearIsometry.extend` extends it to the ambient \(\mathbb C^3\); converting the ambient
isometry back to a matrix produces \(U\), and Lean proves both \(U^\dagger U=I_3\) and \(UX=Y\).

For surjectivity, positivity gives a factorization \(H=B^\dagger B\). Embedding \(B\) in the first
two rows produces an event with Gram record \(H\).

For quotient topology, the continuous functional calculus supplies a continuous positive square
root. Embedding that square root gives a continuous section. Mathlib's
`Function.RightInverse.homeomorph` then turns the right inverse into a homeomorphism from the
kernel quotient to the positive cone.

## Central declarations

- `color_toEuclideanLin_ker_eq_of_gram_eq`;
- `colorRangeEquiv`;
- `colorRangeIsometry`;
- `colorAmbientIsometry`;
- `colorOrbitUnitary`;
- `colorOrbitUnitary_conjTranspose_mul_self`;
- `colorOrbitUnitary_mul`;
- `colorGramMatrix_eq_iff_exists_left_unitary`;
- `colorEmbedSquare`;
- `exists_colorEventMatrix_gram_eq`;
- `PositiveTwoCone`;
- `colorGramRecordMap`;
- `colorGramSection`;
- `colorGramSection_rightInverse`;
- `colorGramQuotientHomeomorph`;
- `colorGramRecordMap_ker_iff_exists_left_unitary`.

## Verification

Focused commands:

```text
lake env lean GaloisForLFunctions/HTGeometry/ColorGramMinkowskiOrbit.lean
lake build GaloisForLFunctions.HTGeometry.ColorGramMinkowskiOrbit
```

The axiom audit is performed from a `/tmp` scratch import. Allowed output is Lean/mathlib
foundations only: `propext`, `Classical.choice`, and `Quot.sound`.

## Novelty boundary

This is standard finite-dimensional Gram-orbit, positive-square-root, and quotient topology.
Formalization is new infrastructure for the corpus, not new mathematical or physical knowledge.

It does **not** prove:

- left-unitary equivalence is nature's observational equivalence;
- positive records are physical causal futures;
- binary complex public alternatives are source-selected;
- local cones compose into spacetime;
- a connection, gravity equation, quantum dynamics, or prediction; or
- the exceptional Standard Model event is the unique physical realization.

Possible scientific novelty is isolated in
`../../1-in-progress/event-generated-identity-curvature-law.md`.

## Gates

- [x] exact paper theorem dependency-closed
- [x] orbit classification formalized unconditionally
- [x] positive-cone surjectivity formalized unconditionally
- [x] continuous section and quotient homeomorphism formalized unconditionally
- [x] mathematical novelty classified as rediscovered
- [ ] physical quotient selection derived
- [ ] event composition, continuum gravity, four-force dynamics, and prediction derived

## Log

- 2026-07-29 — formalized the complete left-unitary orbit classification, positive-cone
  surjectivity, continuous positive-square-root section, kernel/orbit identification, and quotient
  homeomorphism.
