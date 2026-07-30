# Independent null roots fuse to a timelike colour-Gram future

- **ID:** `color-gram-null-fusion`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[FULLY-LEAN-PROVED] [REDISCOVERED] [BRIDGE]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/balanced-causal-fracture-torsor-classification.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ColorGramNullFusion`
- **Statement:** Two one-row \(3\times2\) complex event roots have null Gram records. If their
  alternating determinant is nonzero, the sum of their Gram records is positive definite and
  hence future timelike.

## Exact theorem

For \(u,v\in\mathbb C^2\), put
\[
X(u,v)=
\begin{pmatrix}
u_0&u_1\\
v_0&v_1\\
0&0
\end{pmatrix}.
\]
Then
\[
X(u,v)^\dagger X(u,v)
=
X(u,0)^\dagger X(u,0)+X(v,0)^\dagger X(v,0).
\tag{1}
\]
Each summand is a null Gram record. If
\[
u_0v_1-v_0u_1\ne0,
\tag{2}
\]
then
\[
\det\!\bigl(X(u,v)^\dagger X(u,v)\bigr)
=
|u_0v_1-v_0u_1|^2>0,
\tag{3}
\]
so the sum in `(1)` is positive definite. Under Pauli coordinates, it is a future-timelike
Lorentz vector.

## Lean declarations

- `twoNullRootEvent`;
- `twoNullRootEvent_gram_eq_add`;
- `twoNullRootEvent_minor01`;
- `twoNullRootEvent_minor02`;
- `twoNullRootEvent_minor12`;
- `twoNullRootEvent_lorentzMassSq_pos`; and
- `independent_nullRoot_gram_add_posDef`.

The proof reuses the unconditional Gram positivity, \(3\times2\) Cauchy--Binet, and
rank/timelike infrastructure in `ColorGramMinkowskiCone.lean`. It uses no `sorry`, `admit`,
new axiom, opaque declaration, unsafe declaration, or computation.

## Boundary

This theorem formalizes the physically relevant rank-two null-fusion direction of strict
elementary future. It does not yet prove:

1. every nonzero boundary point of \(H_2(\mathbb C)_+\) has a one-root presentation used by this
   theorem;
2. the full arbitrary-boundary strict-convexity classification for \(H_q(\mathbb C)_+\);
3. the free/transitive \(SU(3)\)-torsor structure of regular Gram fibres;
4. the Cartan-family classification; or
5. any physical identification with spacetime or gravity.

The arbitrary-dimension primitive-root classification is now formalized separately in
`primitive-pair-interior-dimension.md`.

The full paper theorem therefore remains Stage 2 and Lean-open.

## Gates

- [x] paper identity dependency-closed
- [x] exact rank-two null-fusion statement formalized
- [x] direct `lake env lean` check passes
- [ ] full parent theorem formalized
- [ ] physical parent eligible for publication

## Log

- 2026-07-30 — formalized exact addition, minor, strict Lorentz-mass, and positive-definite
  null-fusion laws without computation.
