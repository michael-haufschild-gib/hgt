# Fermionic FE projector and Lefschetz determinant to RH

- **ID:** `fermionic-fe-projector-lefschetz-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]`, `[RH ROUTE]`, `[LARGE OUTLANDISH DETOUR]`
- **Consumer:** `../../../3-formalized/not_new_scientific_knowledge/reflection-fermion-boundary-rh-criterion.md`
- **Source bricks:** `SeamSuspensionTrace.lean`, `IntegralOrbitTateExtension.lean`,
  `CompletedSEMContourBoundary.lean`

## Claim

Construct a source-defined seam complex `C_W` on every reflection-stable finite window, with
functional-equation involution `J_W`, whose degree-zero integral residue cohomology is the complete
Xi divisor in that window.  Prove that its anti-invariant summand is contractible:

```text
P_- = (1-J_W)/2 = d H_- + H_- d                         (over Q),
```

together with an integral determinant-line refinement showing that `1+J_W` is injective on the
residue lattice.  A free reflected zero pair contributes the anti-invariant vector
`e_rho-e_Jrho`; a critical-line fixed zero does not.  Therefore source acyclicity of the
anti-invariant cohomology forces every Xi zero to be fixed and proves RH.

The determinant formulation is equivalent on a finite window:

```text
det(1+J_W | H_res(C_W)) != 0
  iff the window contains no free reflection orbit.
```

This is a fermionic partition function at the special holonomy `-1`, or equivalently the equality
of the identity and FE Lefschetz marks.  The definition is static; no deformation or spectral flow
is used.

## Two-ended chain

```text
completed prime--Gamma / symmetric-EM source
  -> three-sector seam suspension complex C_W
       [existing flat supertrace reconstructs xi'/xi]
  -> integral residue cohomology H_res(C_W)
       [OPEN CORE A: multiplicity-exact source comparison]
  -> FE chain involution J_W
       [functional-equation action is available]
  -> source Bezout/Green homotopy on the anti-invariant complex C_W^-
       [OPEN CORE B: dH_- + H_-d = 1 on C_W^-]
  -> H_res(C_W)^- = 0
  -> 1+J_W injective on the integral residue lattice
  -> no free reflected Xi orbit in W
       [PROVED LEAN: reflectionFermionBoundary_injective_iff_fixed]
  -> exhaust reflection-stable windows
  -> RH
       [PROVED LEAN: riemannHypothesis_iff_reflectionFermionBoundary_injective].
```

## Why this is not the quadratic-circle route

No multiplicity is squared and no irrational character is introduced.  The invariant is the
kernel of a canonical operator already attached to the FE action.  It detects a free orbit by its
anti-invariant direction, not by assigning a positive scalar to that orbit.  Cross-orbit terms are
absent because kernel and direct-sum decompositions are linear.

## Existing bricks and exact use

- `SeamSuspensionTrace.logDeriv_completed_split` supplies the flat prime--Gamma trace whose poles
  have the Xi multiplicities.
- `SeamSuspensionTrace.gradedMatrixTrace_hodgeCompression` supplies the grading-correct algebraic
  compression once a source Hodge/Green homotopy and the finite parity operator are constructed.
  The legacy `flat_eq_cohomology_trace` only consumes a separately supplied ordinary commutator
  and is not the valid consumer of `dH+Hd=1-P`.
- `IntegralOrbitTateExtension.integralUnitExtension_tate_separates_fixed_free` proves that the
  integral residue lattice already distinguishes a fixed orbit from a free swap orbit.
- `CompletedSEMContourBoundary.completedSEMContourIndexZ_eq_xiOrder` supplies the source-defined
  integral local multiplicity.
- `ReflectionFermionBoundary` supplies the exact finite/infinite consumer algebra and the RH
  equivalence.
- `FEOddReducedQuotientBlindness` proves that the nonzero transverse coordinate `2s-1` lies in the
  closed span of the paired Euler tangents even after deleting finitely many primes.  Hence an
  ordinary reduced/Hausdorff quotient of the FE-odd compact-carrier space is zero on precisely the
  direction one would need it to detect.

## Firewalls and positive residues

### Functional-equation commutation is insufficient

`J_W d=d J_W` only decomposes the complex.  A free swap block satisfies the same identity and has
nonzero anti-invariant cohomology.  The new theorem must be a source-produced contraction of the
minus complex, not equivariance alone.

**Positive residue:** the missing statement has the precise form of a Bezout/Green identity on
`C_W^-`; it is not an unspecified positivity or zero-location premise.

### Equivariant Kummer roots do not help

`EquivariantRootDissolution.lean` proves that on symmetric regions with the positive Xi anchor,
equivariant root existence is just ordinary divisor-order divisibility.  Replacing `C_W^-`
acyclicity by an equivariant root repeats the dyadic ladder.

**Positive residue:** the anti-invariant cohomology functor must be applied to the source seam
complex before taking Kummer roots.

### Ordinary trace and square-root holonomy are blind

The completed contour trace reads total multiplicity.  The mirror square-root holonomy reads only
the on-line count modulo two, so free pairs disappear.  Neither proves equality of the identity
and FE marks.

**Positive residue:** keep both marks.  Their difference is the rank of the anti-invariant residue
module and equals twice the free-orbit multiplicity.

### Tate separation is not annihilation

The integral Tate theorem identifies fixed versus free local residue type, but it does not show
that the free type is absent.  A global reciprocity statement that merely sums Tate charges modulo
two is too weak.

**Positive residue:** use the Tate calculation as the integral lattice model for the determinant
of `1+J_W`, while the source homotopy must kill the entire minus complex, not only its parity.

### Target divisor complexes are circular

Defining `C_W` as the free module on Xi zeros gives the right answer by construction.  The complex,
involution, and homotopy must be built from the completed Euler--Gamma/SEM source.  Zeros may occur
only in the comparison theorem identifying source cohomology.

### The reduced FE-odd quotient is unconditionally blind

The compact-carrier completeness theorem puts the nonzero coordinate `2s-1` in the closed span of
the cofinite paired Euler family.  Therefore every continuous detector of the reduced quotient
kills it, without using RH.  A Banach cokernel or reduced cohomology based only on that closed span
cannot be the desired residue object.

**Positive residue:** retain the unreduced class modulo the algebraic paired-Euler range, or retain
the weighted all-prime coefficient tail of its approximants.  Private boundary poles now prove
that `2s-1` is outside every finite paired-Euler span while the Lean closure theorem puts it in the
closed cofinite span.  This replaces an unspecified derived limit by the canonical nonzero class
`[2s-1]` in the algebraic-range/closed-range quotient.

## Competing source constructions

1. `[CONJECTURE]` Refine the three-sector seam suspension into an integral perfect complex and
   construct `H_-` from a prime--Gamma Bezout identity.
2. `[CONJECTURE]` Build the finite-window Fredholm determinant line of the source reflection and
   prove its value at fermionic holonomy `-1` is a nonzero Euler--Gamma product.
3. `[CONJECTURE]` Use the all-prime Sonin inverse-semigroup normal form to contract only the
   anti-invariant boundary word, leaving the invariant cohomology untouched.

The first construction is strongest because it would explain the trace compression already in the
corpus.  The second may establish nonvanishing without a full chain homotopy.  The third is the most
indirect and must prove that Calkin contraction lifts to the integral residue lattice.

## Status

- `[PROVED]` every free involution orbit supplies an explicit nonzero kernel vector of `1+J`;
- `[PROVED]` injectivity of the Xi fermionic FE boundary is equivalent to RH;
- `[PROVED]` the corpus has source-defined local integral multiplicity and a fixed/free integral
  Tate distinction;
- `[PROVED]` the seam supertrace has the correct Xi logarithmic derivative and a formal Hodge
  compression mechanism;
- `[PROVED]` an ordinary Hausdorff quotient by the closed cofinite paired-Euler range kills the
  nonzero FE-transverse coordinate unconditionally;
- `[PROVED PAPER]` `2s-1` is outside the algebraic paired-Euler range, so its nonzero completion-
  defect class is canonical;
- `[OPEN CORE]` identify that class with a multiplicity-exact vector-valued source residue without
  passing through a scalar nonclosable graph;
- `[OPEN CORE]` construct a multiplicity-exact integral seam cohomology and source-defined
  anti-invariant contracting homotopy or determinant nonvanishing;
- `[OPEN CORE]` prove finite-window compatibility and exhaustion.
