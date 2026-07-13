# Prime--Gamma Stokes/Seifert Coxeter monodromy to RH

- **ID:** `prime-gamma-stokes-seifert-coxeter-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeGammaStokesCoxeterRH.lean`
- **Source bricks:** `SeamSuspensionTrace.lean`, `ArakelovW.lean`,
  `archimedean-wild-monodromy-tate-local.md`, `ht-c29-resurgence-stokes-nonclosure.md`

## Claim

Construct one real completed Stokes category directly from the prime--Gamma constraint, with an
invertible Seifert operator `S` and Coxeter monodromy

```text
C = -S^(-1) S^T.
```

Its symmetrization `A=S+S^T` must be positive on the closed reduced Stokes cohomology, and its
regularized Coxeter determinant must be the Arakelov transform of Xi:

```text
det_reg(1-w C) = nonvanishing factor * xi((1-w)^(-1)).       (1)
```

The algebraic identity

```text
C^T A C = A                                                   (2)
```

then makes `C` unitary for the positive `A`-norm.  Every spectral value `w` has `|w|=1`.
Equation (1) identifies the spectral values with

```text
w_rho = 1-rho^(-1)
```

for Xi zeros `rho`; `|w_rho|=1` is exactly `Re(rho)=1/2`.  Thus the construction proves RH.

The proposed category is static.  Stokes matrices are gluing constraints between sectorial
solutions; no deformation, spectral flow, or zero-height evolution is used.

## Two-ended chain

```text
completed Euler--Gamma / symmetric-EM source
  -> Borel/sectorial prime--Gamma Stokes category
       [OPEN CORE A: one source-defined global category]
  -> real integral Seifert operator S
       [OPEN CORE B: closed infinite Stokes pairing]
  -> positive symmetrization A=S+S^T
       [OPEN CORE C: source positivity / Hodge--Maxwell stress theorem]
  -> Coxeter operator C=-S^(-1)S^T preserves A
       [PROVED LEAN: coxeterTransform_preserves_symmetrization]
  -> every Coxeter eigenvalue has modulus one
       [PROVED LEAN: norm_eigenvalue_eq_one_of_norm_preserving]
  + regularized determinant comparison (1)
       [OPEN CORE D: divisor-exact comparison before reading zeros]
  -> |1-rho^(-1)|=1 for every Xi zero
  -> Re(rho)=1/2
       [PROVED LEAN: arakelovW_norm_one_iff_critical]
  -> RH
       [PROVED LEAN: riemannHypothesis_of_xiArakelovUnitarySpectralData].
```

## Unconditional algebraic floor

For every invertible finite Seifert matrix, Lean proves (2) exactly.  The computation uses only
matrix inversion and transpose; positivity is not smuggled into it.  Lean also proves that an
eigenvalue of any norm-preserving complex linear map has unit norm.

The finite unitary packet is equivalent to a unit-circle certificate.  Consequently the bare
assertion that every hypothetical right-half zero has such a packet is exactly RH:

```text
XiArakelovUnitarySpectralData <-> RiemannHypothesis.
```

This is a circularity audit, not the source construction.  A live proof must supply one global
operator and determinant identity from the Euler--Gamma Stokes category before its spectrum or
the Xi divisor is expanded.

## Why the detour is not empty

The preservation law is stronger than functional-equation reciprocity.  A general reciprocal or
symplectic operator may have eigenvalues in pairs `(w,w^(-1))` away from the circle.  A positive
Seifert symmetrization upgrades reciprocity to unitarity and pins every member of each reciprocal
pair to the circle.  This is precisely the missing orientation.

The candidate source is also structurally aligned with the corpus:

1. the Gamma factor has genuine irregular/Stokes data;
2. the seam supertrace already reconstructs the completed logarithmic derivative;
3. the completed source is a constraint glued from prime and archimedean sectors;
4. Coxeter monodromy is the canonical global automorphism extracted from a Seifert/Stokes form;
5. the Arakelov coordinate converts the FE reciprocal orbit into the natural Coxeter reciprocal
   spectral coordinate.

The new science would be the simultaneous source construction, positivity, and determinant
comparison.  The matrix algebra is classical substrate.

## Firewalls and positive residues

### Generic Stokes data is not positive

An arbitrary Stokes matrix has no reason for `S+S^T` to be positive.  Nondegeneracy gives only a
reciprocal spectrum and permits off-circle pairs.

**Positive residue:** the exact source theorem required is a Hodge--Riemann/Maxwell-stress law on
the reduced completed Stokes cohomology.  It must be proved from the prime--Gamma intersection
pairing, not imposed on a matrix chosen after seeing Xi.

### Gamma resurgence alone cannot see the Xi divisor

The Gamma Stokes constants and their `2*pi*i` lattice are classical and archimedean.  They do not
contain the prime Euler source or the nontrivial zero divisor.

**Positive residue:** the Seifert operator must be a welded prime--Gamma operator.  The Gamma
sector supplies the real polarization; the prime sector supplies the infinite incidence whose
regularized determinant can equal Xi.

### A finite integral Coxeter matrix is too small

A finite integral Seifert matrix has algebraic Coxeter eigenvalues.  Requiring every transformed
Xi zero to be one of them would add an unsupported algebraicity assertion and cannot encode the
infinite divisor.

**Positive residue:** finite matrices are local/window models only.  The global object must be a
closed infinite Coxeter operator with a regularized determinant; finite-window positivity must be
uniform and survive the cofinal limit.

### Reciprocal determinant symmetry is insufficient

A palindromic characteristic determinant follows from (2) without positivity and merely repeats
the functional equation.  Reciprocal polynomials commonly have roots off the unit circle.

**Positive residue:** retain the positive symmetrized form, not only the determinant symmetry.
The proof-bearing datum is `A`-unitarity of the operator before scalar determinant evaluation.

### Zero-indexed packets are circular

Choosing a one-dimensional unitary operator with eigenvalue `w_rho` after assuming `|w_rho|=1`
repackages RH.  Lean's equivalence exposes this exactly.

**Positive residue:** equation (1) must be an identity of source-built holomorphic/regularized
determinants on a domain, with a separately proved nonvanishing prefactor.  Zeros may appear only
after the identity is established.

### The tensegrity analogy is not the positivity theorem

Maxwell--Calladine stress and Katz rigidity motivate `S+S^T`, but dimension matching or rigidity
alone does not give a positive stress matrix.

**Positive residue:** a genuine source stress must be a Gram/intersection form whose positivity is
checked on every finite window and whose nullspace is exactly the Stokes gauge range.

### Resurgence nonclosure forces an infinite object

The corpus warns that a hypertranscendental completed object need not have a finite controller of
all Stokes data.  Treating finitely many alien derivatives as the whole category would contradict
that boundary.

**Positive residue:** nonclosure does not kill the route; it identifies its correct home as a
locally finite or nuclear Stokes category with a regularized Coxeter determinant.  The proof must
use closedness and trace-class/relative-determinant control, not finite generation.

### Critical-line zeros remain allowed

Positivity places the Coxeter spectrum on the unit circle; it does not annihilate it.  Therefore
the route localizes zeros without incorrectly forcing Xi to be zero-free.

## Candidate source constructions

1. **Theta-thimble construction.**  Use the weight-one theta inversion sectors as thimbles; prime
   Euler insertions give the infinite incidence, while the Gaussian intersection pairing supplies
   the positive symmetrization.
2. **Seam-suspension construction.**  Refine `SeamSuspensionTrace` from a scalar flat supertrace to
   a real perfect Stokes complex.  Its chain-level intersection matrix is `S`, and Hodge
   compression supplies the reduced positive form.
3. **Sonin/CCM construction.**  Use the two-polarization Sonin inverse-semigroup windows as finite
   Stokes sectors.  The proven Calkin partial isometries supply the gluing maps; the missing theorem
   is a cofinal positive Seifert form and determinant comparison.
4. **Prime-support boundary-jet construction.**  `PrimeSupportBoundaryJets.lean` proves that the
   marked Koszul selector is the zeroth boundary value of `M_n(t)=n(1-t)^(n-1)` and that its `r`th
   normal derivative selects support size `r+1` with signed factorial weight.  Use the complete jet
   tower as a support-stratified Stokes basis.  After the canonical sign twist its diagonal pairing
   is positive factorial; the arithmetic incidence supplies the off-diagonal Seifert entries.  A
   Gamma-damped diagonal-dominance or Hodge--Riemann theorem for this source-built pairing would
   discharge positivity of `S+S^T` without discarding mixed-prime sectors.  The separate route card
   `prime-support-boundary-jet-stability-rh.md` pursues the stable-determinant version of the same
   source floor.

The theta-thimble version has the cleanest chance of a source-positive form.  The seam-suspension
version has the shortest determinant-comparison path.  A successful construction may combine
them: theta positivity for `A`, seam supertrace for `(1)`.

## Status

- `[PROVED LEAN]` exact Coxeter preservation of the symmetrized Seifert form;
- `[PROVED LEAN]` norm-preserving spectral values lie on the unit circle;
- `[PROVED LEAN]` unit-circle Arakelov coordinate is equivalent to the critical line;
- `[PROVED LEAN]` the zero-indexed unitary-packet predicate is equivalent to RH;
- `[OPEN CORE]` source-defined completed prime--Gamma Stokes category and Seifert operator;
- `[OPEN CORE]` positivity on reduced closed Stokes cohomology;
- `[OPEN CORE]` nuclear/relative determinant and exact Arakelov--Xi comparison;
- `[CLOSED SHORTCUT]` finite algebraic Coxeter matrices;
- `[CLOSED SHORTCUT]` reciprocal characteristic polynomial without positivity;
- `[CLOSED SHORTCUT]` Gamma-only resurgence or zero-indexed unitary packets.
