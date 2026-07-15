# Full nonlinearity--valuation Hilbert tomography and complete differential relations

- **ID:** `nonlinearity-valuation-hilbert-tomography-completeness`
- **Stage:** 3-formalized
- **Type:** GENERAL HT THEOREM / COMPLETE RELATION LAW
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY UNVERIFIED]`
- **Parent:** `prime-valuation-veronese-master-law.md`
- **Statement:** For a finite-range prime coefficient source in finitely many variables, the
  degree-`m` recurrent homogeneous coordinate space is exactly the `p^m` valuation-tail quotient;
  its dimension is the Hilbert function, the full shifted monomial carrier has no differential
  relations beyond the prolonged Hilbert-coordinate reductions, and the complete sequence of
  homogeneous kernels determines the normalized recurrent point geometry.

## Exact theorem surface

Let `x : Nat.Primes -> (sigma -> C)` have finite range, with `sigma` finite. For every homogeneous
degree `m`, recurrent evaluation is the linear map

```text
E_m : Sym^m(C^sigma) -> C^(R_x),
```

where `R_x` is the set of values of `x` whose prime fibres are infinite. Define

```text
H_x(m) = dim_C range(E_m).
```

The following assertions are proved without mathematical hypotheses hidden behind placeholders.

1. **Complete layer kernel.** A homogeneous polynomial has finite prime support after evaluation
   on `x` exactly when it vanishes on `R_x`. Hence the valuation-tail quotient in degree `m` is
   linearly equivalent to `range(E_m)` and has dimension `H_x(m)`.

2. **Full finite-point Hilbert law.** If one coordinate `X_0` is one on `R_x`, then `H_x(m)` is
   nondecreasing, is bounded by `card(R_x)`, and

   ```text
   H_x(m) = card(R_x)  whenever  card(R_x) - 1 <= m.
   ```

   The proof constructs homogeneous delta polynomials of degree `card(R_x)-1` and raises their
   degree by powers of `X_0` without changing their recurrent values.

3. **Full Hilbert basis and monomial layer.** In each degree, the entire recurrent evaluation
   range has a basis indexed by `Fin H_x(m)`. Every homogeneous polynomial, and in particular
   every degree-`m` monomial, has an exact coordinate expansion in that basis on `R_x`.

4. **Finite-window differential rank.** For valuation degrees `m=1,...,d`, finite shift sets
   `A_m` whose real parts are pairwise distinct, and a nonempty combined Hilbert-pivot palette,
   the Hilbert pivots form a differential-independent family over the finite-prime rational
   coefficient field. Its exact cardinality is

   ```text
   sum_(m=1)^d card(A_m) H_x(m).
   ```

5. **Complete relation ideal.** Take all degree-`m` monomial carriers in every selected valuation
   degree and all selected shifts. Their prolonged affine Hilbert-coordinate reductions, including
   the finite-prime base corrections, generate the entire differential relation ideal. There are
   no additional nonlinear relations and no relations mixing distinct valuation degrees.

6. **Injective homogeneous tomography.** For two finite-range sources normalized by the same
   coordinate `X_0=1`, equality of their homogeneous recurrent vanishing submodules in every
   degree is equivalent to equality of their recurrent point sets.

The choices of basis vectors need not have a closed formula. All statements are invariant at the
level of the complete homogeneous kernels, Hilbert numbers, generated field, and relation ideal.

## Formal declaration ledger

| Paper claim | Declaration |
|---|---|
| finite-range observable kernel | `finiteRange_observable_support_finite_iff` |
| homogeneous tail kernel | `homogeneousTailRelationSubmodule_eq_recurringVanishing` |
| quotient realization | `homogeneousTailQuotientEquivRecurringRange` |
| all-degree Hilbert equality | `valuationTailHilbertFunction_eq_recurrent` |
| sharp homogeneous interpolation | `exists_homogeneous_eval_eq_of_card_sub_one_le` |
| Hilbert monotonicity | `recurrentHomogeneousHilbertFunction_mono` |
| Hilbert upper bound | `recurrentHomogeneousHilbertFunction_le_ncard` |
| Hilbert stabilization | `recurrentHomogeneousHilbertFunction_eq_ncard_of_card_sub_one_le` |
| valuation-tail stabilization | `valuationTailHilbertFunction_eq_ncard_of_card_sub_one_le` |
| full Hilbert pivot independence | `fullRecurrentHilbertPivot_linearIndependent` |
| full Hilbert spanning | `fullRecurrentHilbertPivot_spans` |
| complete monomial presentation | `fullRecurrentHilbertValuationPresentation` |
| exact quotient rank | `fullRecurrentHilbert_finrank_tailQuotient` |
| exact finite-window rank sum | `fullRecurrentHilbert_pivotPalette_card` |
| complete differential relation ideal | `fullRecurrentHilbert_complete_relationIdeal` |
| differential basis and rank | `fullRecurrentHilbert_differentialBasis_and_rank` |
| injective homogeneous tomography | `recurringValueSet_eq_iff_homogeneousVanishingSubmodules_eq` |

The declarations are contained in:

- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationVeroneseKernel.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationVeroneseHilbert.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationVeroneseDifferentialBasis.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationVeroneseRelationIdeal.lean`;
- `formal/GaloisForLFunctions/HTGeometry/PrimeValuationVeroneseMaster.lean`.

## Paper boundary

The prospective paper may state only the six items above and their immediate logical
consequences. The following are not part of its theorem surface:

- transfer from the formal arithmetic-function carrier to analytic Dirichlet germs;
- polarization or Euler-ghost realization of every homogeneous layer;
- a canonical closed formula for the selected Hilbert basis;
- inverse-limit or Stone reconstruction of an infinite-coordinate source;
- Hilbert-slope, entropy, or topological-entropy laws;
- externality of an infinite Euler completion from every finite differential field;
- any consequence for the Riemann hypothesis or exclusion of an RH proof route.

These statements require separate formal declarations before they may enter the paper as
theorems. They may appear only as explicitly identified motivation or open problems, without
assertive mathematical wording.

## Verification

The two touched capstone modules pass direct checks. A single exact cached build of
`GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseMaster` succeeded; no full build was run.
The principal declarations depend only on the standard logical axioms used by the library:
`propext`, `Classical.choice`, and `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration occurs in the touched
Hilbert or master modules.

## Gates

- [x] layer kernel and quotient proved
- [x] full Hilbert function, monotonicity, and sharp stabilization proved
- [x] full degree-monomial presentation constructed
- [x] exact finite-window differential rank proved
- [x] complete relation ideal proved
- [x] homogeneous tomography injectivity proved
- [x] direct checks and exact cached capstone build passed
- [x] principal declarations have only standard library axioms
- [ ] specialist novelty and priority audit completed
- [ ] standalone paper restricted to this exact theorem surface
