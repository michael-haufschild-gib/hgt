# General matrix principal-symbol differential horizon

- **ID:** `matrix-principal-symbol-differential-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM / DIFFERENTIAL ALGEBRA / FILTERED PRINCIPAL SYMBOLS
- **Scientific status:** `[LEAN-FORMALIZED] [AXIOM-AUDITED] [NOVELTY PROVISIONAL]`
- **Paper lane:** *Before There Was Time: Hypertranscendence and the Holographic Determinant Horizon*

## Theorem

Let `K -> L` be a field extension with a differential structure on `L`. Let `x_i` be a finite
differentially algebraically independent source family and `y_i` a finite target family. Assume
that, at every jet order `n`, the full target-jet packet is obtained from the source-jet packet by a
strictly lower block-triangular law whose diagonal block is a square matrix `S_n` over `K`.

Then

```text
{y_i} is differentially algebraically independent over K
  iff
det S_n != 0 for every n.
```

For a law space `g` with symbols `S_n(A)`, the exact differential-algebraic dependence spectrum is

```text
{A | {y_i(A)} is differentially algebraically dependent over K}
  = union_n {A | det S_n(A)=0}.
```

If consecutive symbols satisfy the flat square law

```text
S_(n+1)(A) S_n(B) = S_(n+1)(B) S_n(A),
```

the exact spectrum is either all of `g`, or one first-layer determinantal locus

```text
{A | det S_0(A)=0}.
```

## Proof

At finite depth, the target packet is a block-lower-triangular linear transformation of an
algebraically independent source packet. It is algebraically independent exactly when the global
coefficient matrix has full row rank. The determinant of that matrix is the product of the
diagonal-block determinants, giving the finite criterion. Finite-type algebraic independence then
gives the complete countable criterion.

Differential independence is ordinary algebraic independence of the full jet family, so swapping
the component/order indices transports the packet theorem without loss. Flatness gives the
cross-determinant identity; one everywhere-regular direction identifies every layer singular set
with the first.

## Lean theorem surface

The unconditional proof is split across:

- `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolHypertranscendenceHorizon.lean`;
- `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolLowerLaw.lean`;
- `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolDifferentialHorizon.lean`;
- `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolDerivationLawHorizon.lean`;
- `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolCoefficientFlatness.lean`;
- `formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolDeterminantHorizon.lean`.

Principal declarations:

- `algebraicIndependent_matrixLinearForms_blockTriangular_iff`;
- `matrixPrincipalPacket_algebraicIndependent_iff`;
- `matrixPrincipalPacketRealization_of_lowerLaw`;
- `matrixPrincipalLowerLaw_differentialIndependent_iff`;
- `matrixPrincipalLowerLaw_hypertranscendentalOver_iff`;
- `matrixDifferentialDependentSet_eq_characteristicSet`;
- `matrixDifferentialDependentSet_eq_firstSingularSet_of_flat`;
- `matrixPrincipalLowerLaw_flat_differentialSpectrum_dichotomy`;
- `derivationPrincipalLowerLaw_independent_iff`;
- `derivationLawDependentSet_eq_characteristicSet`;
- `derivationLawDependentSet_eq_firstSingularSet_of_coefficientFlat`;
- `derivationPrincipalLowerLaw_coefficientFlat_spectrum_dichotomy`.

The varying-derivation declarations do not disguise the law parameter as a parameterized function:
each point of law space selects its own `Derivation`, and independence is defined from that
derivation's complete iterate tower. `MatrixCoefficientPrincipalSymbolFlat` records the row-order
composition convention produced by actual iterated derivations; transposition identifies it with
the geometric-arrow flat square without changing determinant loci.

Targeted builds pass. Formal lint passes. The terminal axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Novelty and significance gate

Block-triangular determinant transfer, determinantal varieties, characteristic varieties, and
flat/discrete-Lax transport are established parent theories. The candidate new content is their
combination into an exact theorem about the **ordinary differential-algebraic dependence spectrum
as the derivation law itself varies**. Primary-source and exact-phrase searches found adjacent
results in parametrized differential Galois theory, Spencer integrability, matrix pencils, and
solution algebras, but no matching spectrum theorem. This is an absence-of-hit verdict, not a
priority claim.

The theorem is broad and exact, but a major significance claim still requires a concrete natural
function or field-observable system satisfying the strict-lower law. Without that realization the
result is a new structural theory, not yet a field-changing application.

## Physical interpretation `[CONJECTURE]`

Before a time direction is selected, points of `g` are candidate laws. The determinantal locus is
the boundary where a complete observable family loses hypertranscendence. Flatness makes all
infinitely many layer boundaries holographic: the full differential-algebraic phase diagram is
encoded by one finite matrix pencil. No known QFT or cosmology is asserted to realize the
hypotheses.

## RH impact

Any finite-rank flat completed-`L`-function law model satisfying the lower principal law can have
only one determinantal differential-algebraic wall. This rules out independent scale-by-scale
critical walls inside that model class, but supplies no direct RH proof.
