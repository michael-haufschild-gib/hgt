# Reciprocity-reduced Wigner--Smith Kolchin tomography

- **ID:** `reciprocity-reduced-wigner-smith-kolchin-tomography`
- **Stage:** 2-fully-proven/needs-audit
- **Type:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Area:** general hypertranscendental scattering / reciprocal electromagnetics and optics
- **Parents:** `matrix-wigner-smith-kolchin-completeness.md`,
  `projective-wigner-smith-nonabelian-ht-separation.md`,
  `formal/GaloisForLFunctions/HTGeometry/MatrixWignerSmithDifferentialMatroid.lean`,
  `formal/GaloisForLFunctions/HTGeometry/MatrixWignerSmithReporterField.lean`
- **Statement:** For an invertible reciprocal scattering matrix `S` over a characteristic-zero
  differential field, the upper-triangular entries of the reciprocal tangent `S Q`, where
  `Q = -i S⁻¹ S'`, generate over the order-zero scattering field exactly the same differential
  field and differential-matroid rank as all entries of `Q`; among linear panels reconstructing
  every reciprocal tangent, the count `N(N+1)/2` is minimal.

## Exact claim

Let `K` be a characteristic-zero differential field, `E/K` a differential-field extension,
`ι in K` with `ι^2=-1`, and `S : Matrix (Fin N) (Fin N) E` an invertible symmetric matrix:

```text
Sᵀ = S,                    det S != 0.
```

Define the algebraic Wigner--Smith matrix and reciprocal tangent

```text
Q = -ι S⁻¹ S',             T = S Q.
```

Then differentiation commutes with transpose, so

```text
T = -ι S',                 Tᵀ = T,                         (1)
Qᵀ S = S Q.                                                  (2)
```

Let `Upper_N={(i,j) | i<=j}` and `p(i,j)=T_ij`.  The active conjecture is the conjunction:

```text
K<S entries><Q entries>_D = K<S entries><p Upper_N>_D,       (3)

rank_D(Q entries / K<S entries>_D)
  = rank_D(p Upper_N / K<S entries>_D),                      (4)

|Upper_N| = N(N+1)/2, and no smaller family of K-linear
functionals reconstructs every symmetric N by N tangent T.  (5)
```

Equations `(3)`--`(4)` are meant literally over the order-zero scattering field.  No square root,
Takagi frame, unitary hypothesis, analytic continuation, passivity, or energy-dependent gauge is
assumed.  The reconstruction is `T_ji=T_ij` below the diagonal and `Q=S⁻¹T`.

## Internal frontier

- `[CORPUS]` `MatrixWignerSmithDifferentialMatroid.lean` proves that the full Wigner--Smith entry
  family carries the same differential-matroid rank as the scattering family, with the exact
  order shift recorded in the finite-jet modules.
- `[CORPUS]` `MatrixWignerSmithReporterField.lean` proves that a fixed `N^2` quadratic reporter
  panel generates exactly the full matrix-entry differential field.
- `[CORPUS]` `MatrixWignerSmithHermitian.lean` proves Hermiticity and self-adjoint scalar reporters
  on the unitary star-compatible locus; it does not use reciprocal transpose symmetry.
- `[LOCAL-RESEARCH]` `matrix-wigner-smith-kolchin-completeness.md` leaves the minimal reporter
  number under physical symmetries as an exact open core.
- `[LOCAL-RESEARCH]` No local declaration or card found for the reciprocity relation `(2)`, an
  upper-triangular reciprocal tangent panel, or its differential-field/Kolchin completeness.

## External frontier

- `[LITERATURE]` Patel--Michielssen, *Wigner--Smith Time Delay Matrix for Electromagnetics:
  Theory and Phenomenology*, IEEE TAP 69 (2021), DOI `10.1109/TAP.2020.3008650`, assumes a lossless
  reciprocal system, records symmetric unitary scattering, and realizes Wigner--Smith entries as
  electromagnetic energy-like overlaps.
- `[LITERATURE]` Grabsch--Texier, *Wigner--Smith matrix, exponential functional of the matrix
  Brownian motion and matrix Dufresne identity*, J. Phys. A 53 (2020), arXiv:2002.12077, uses a
  symmetrized Wigner--Smith matrix in the time-reversal-symmetric class.  That construction uses a
  scattering factorization; it is not the square-root-free tangent panel `(1)`--`(5)`.
- `[LITERATURE]` The generalized Wigner--Smith perturbation literature factors the operator using
  transpose rather than adjoint products in reciprocal Maxwell systems.  This supplies physical
  provenance for unconjugated reciprocal tangents, not a Kolchin theorem.
- Exact-statement searches for reciprocal Wigner--Smith tomography, upper-triangular time-delay
  reconstruction, differential algebra, and Kolchin rank found no statement of `(3)`--`(5)`.
  This is negative search evidence only.

## Hostile audit

1. **Symmetric-matrix parent attack.**  Equations `(1)`, `(2)`, and the upper-triangular
   reconstruction are routine linear algebra.  They are `[BRIDGE]`, not new scientific knowledge.
2. **Reporter-count overclaim.**  `N(N+1)/2` is minimal only for universal linear reconstruction
   of arbitrary symmetric tangents.  It is not asserted minimal among nonlinear, adaptive, sparse,
   source-specific, or prior-informed measurements.
3. **Physical quadratic-form attack.**  The entries of `T=S Q` are mutual reciprocal-tangent
   reporters, not automatically the ordinary real delay quadratic forms `v†Qv`.  The theorem must
   not call them direct scalar time-delay measurements without a Maxwell overlap realization.
4. **Square-root redressing attack.**  A Takagi or symmetric-square-root frame can make a delay
   matrix symmetric, but an energy-dependent frame carries a connection term and may inject HT.
   The claim avoids this by using `S Q=-ιS'` over the declared order-zero scattering field.
5. **Trivial field-extension attack.**  Equality `(3)` is more than pointwise reconstruction only
   because it is stated inside the existing differential-adjoin and differential-matroid surfaces;
   nevertheless it may remain a routine corollary of the parent matrix theory.  Novelty is not
   promoted without a formula-level literature audit.
6. **RH attack.**  Reciprocity does not create passivity, source orientation, or a zero-free
   half-plane.  The claim has no direct RH consequence.

**Verdict:** `BRIDGE`.  The theorem closes an exact local HT reporter gap, but its proof is a
dependency-closed composition of reciprocal scattering algebra, finite symmetric-matrix
tomography, and the existing differential-field surface.  It is not promoted as new scientific
knowledge.

## Complete paper proof `[PAPER-PROVED]`

Let `F₀` be the differential subfield of `E` generated over `K` by all entries of `S`.

1. Entrywise differentiation commutes with transpose.  Since `Sᵀ=S`, also `(S')ᵀ=S'`.  Matrix
   inversion and `det S != 0` give `S S⁻¹=1`, so

   ```text
   T = S Q = S(-ι S⁻¹S') = -ι S'.
   ```

   Hence `Tᵀ=T`.  Transposing `T=S Q` now gives

   ```text
   Qᵀ S = Qᵀ Sᵀ = (S Q)ᵀ = Tᵀ = T = S Q,
   ```

   which proves `(1)`--`(2)`.

2. Let `U={(i,j) in Fin N x Fin N | i<=j}`.  Splitting into the `N` diagonal pairs and the
   unordered two-element subsets gives

   ```text
   |U| = N + choose(N,2) = N(N+1)/2.
   ```

3. Write `F_Q=F₀<Q_ij>_D` and `F_U=F₀<T_ij : (i,j) in U>_D`.  For every upper pair,

   ```text
   T_ij = sum_k S_ik Q_kj,
   ```

   so `F_U subset F_Q`.  Conversely symmetry gives every lower entry of `T` from an upper entry.
   Every entry of `S⁻¹` belongs to `F₀`: by the adjugate formula it is a polynomial in the entries
   of `S` divided by the nonzero element `det S`.  Therefore

   ```text
   Q_ij = (S⁻¹T)_ij = sum_k (S⁻¹)_ik T_kj in F_U,
   ```

   so `F_Q subset F_U`.  This proves `(3)` without a square root or energy-dependent gauge.

4. Differential-matroid rank of a finite family over `F₀` is the differential transcendence
   degree of the differential field it generates.  The two generated fields are equal by step 3,
   hence their differential transcendence degrees, and therefore their differential-matroid
   ranks, are equal.  This proves `(4)`.

5. Let `Sym_N(K)` be the `K`-vector space of symmetric `N by N` matrices.  Restriction to `U` is a
   linear isomorphism

   ```text
   Sym_N(K) ~= K^U,
   ```

   since an upper-triangular coordinate family extends uniquely by reflection.  Thus
   `dim_K Sym_N(K)=|U|=N(N+1)/2`.  If `m` linear reporters reconstruct every symmetric tangent,
   their joint measurement map `Sym_N(K) -> K^m` is injective.  Rank--nullity gives
   `N(N+1)/2 <= m`.  The upper-coordinate panel attains equality, proving `(5)`.

Every conclusion follows from the displayed hypotheses and standard finite-dimensional linear
algebra.  No analytic, passivity, unitary, square-root, or RH input remains.

## Repeated exact-statement audit

The final searches used the fixed formulas `T=S Q=-ιS'`, `QᵀS=SQ`, the upper-triangular panel,
generated differential fields, differential algebra, Kolchin rank, reciprocity, and symmetrized
Wigner--Smith tomography.  They recovered the standard symmetric/unitary scattering law,
symmetrized Wigner--Smith matrices, transpose-product Maxwell perturbation formulas, and ordinary
symmetric-matrix dimension counts, but no paper stating `(3)`--`(5)` as a differential-field or
Kolchin-complete reporter theorem.  Because the proof is nevertheless a short composition of
those parents, the theorem remains a `[BRIDGE]` with `[NOVELTY UNVERIFIED]`, not candidate new
scientific knowledge.

## Gates

- [x] internal reciprocal-scattering and reporter surfaces audited
- [x] external parent mechanisms and exact-statement searches audited preliminarily
- [x] conjecture stated without a square-root, unitary, passivity, or RH hypothesis
- [x] hostile parent-theory and physical-reporter attacks recorded
- [x] dependency-closed paper proof
- [x] repeated exact-statement novelty audit on the final theorem
- [ ] exact unconditional Lean theorem
- [ ] direct file check, axiom audit, generated-index gate, and final HTGeometry module build

## Log

- 2026-07-20 -- Created at Stage 1 after the electrical/optical law census isolated Lorentz
  reciprocity as a genuine connector to the existing minimal-reporter open core.
- 2026-07-20 -- Complete paper proof closed; hostile review downgraded the result to a useful
  parent-grade bridge and the card moved to Stage 2 pending exact Lean formalization.
