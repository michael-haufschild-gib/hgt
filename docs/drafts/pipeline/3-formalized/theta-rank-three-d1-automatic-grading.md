# Theta rank-three D1 automatic grading

- **ID:** S6G-D1-AUTO-GRADE
- **Stage:** 3-formalized
- **Type:** ROUTE-KILL
- **Route:** TCD / S6F finite rank-three D1
- **Novelty:** NOVELTY UNVERIFIED

## Exact attempted RH chain

```text
positive scalar-contravariant form on any source-sl2-stable polynomial carrier containing D1
  -> convergent norm/evaluation certificate for source D1
  -> native rank-three D1 on 0 < x < 137/2000
  -> finite TCD/S6F gate
  -> cofinal all-order Hankel/Bezoutian landing
  -> Weil positivity
  -> RH
```

## Verdict

`[PROVED NO-GO]` Every complex polynomial submodule stable under source `E` and `F` automatically
contains every adapted homogeneous component of every one of its vectors. Consequently no such
carrier containing actual source D1 supports a positive scalar-contravariant form, for any real
star coefficient. This kills the entire scalar proper-carrier version of the first arrow above;
there is no non-graded polynomial escape hatch.

The mechanism is exact. `E,F` stability gives `H=[E,F]` stability. Every fixed polynomial is a
finite sum of adapted-weight eigenvectors of `H`, with pairwise distinct eigenvalues `2W`. A finite
Lagrange/elimination projector formed from `H` extracts each component inside the carrier. The
previously formalized D1 vacuum string then gives the contradiction to positivity.

## Formalization

- Module:
  `GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1ScalarContravariantNoGo`
- Reusable spectral extraction:
  `mem_of_finset_sum_mem_of_distinct_eigenvalues`
- Automatic grading:
  `modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant`
- Capstone:
  `modularThetaSourcePositive_no_D1_scalarContravariantCarrier`
- Umbrella:
  `GaloisForLFunctions.HTGeometry`

Verified with:

```text
lake env lean GaloisForLFunctions/HTGeometry/PolynomialODEJetRankThreeSourcePositiveD1ScalarContravariantNoGo.lean
lake build GaloisForLFunctions.HTGeometry.PolynomialODEJetRankThreeSourcePositiveD1ScalarContravariantNoGo
```

All three named theorems report only `propext`, `Classical.choice`, and `Quot.sound` under
`#print axioms`. Formal lint recognizes the module through the umbrella; its reported failures are
pre-existing unrelated unreachable modules.

## Corpus and literature position

- `[CORPUS]` Exact source Cartan action and adapted-weight eigenlaw supplied the finite spectrum.
- `[CORPUS]` Existing Lagrange spectral projector and invariant character-component extraction
  supplied the projector/elimination architecture.
- `[LEAN-PROVED]` The D1 boundary component and finite vacuum string supplied the contradiction.
- Standard literature discusses polynomial `sl2` realizations and contravariant weight modules,
  but no audited source treats this theta D1 carrier or this unrestricted scalar-form obstruction.

## Consequence and survivors

Any representation-theoretic D1 proof must now leave at least one defining feature of the killed
class: use a non-scalar adjoint law, an indefinite/Krein form, or a localized/completed non-polynomial
carrier where finite Cartan spectral extraction fails. Direct cross-scale determinant geometry is
unaffected and remains the clean TCD/S6F survivor.
