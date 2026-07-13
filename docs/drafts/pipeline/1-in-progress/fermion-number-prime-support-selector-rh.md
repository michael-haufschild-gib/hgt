# Fermion-number prime-support selector and infinite boundary anomaly

- **ID:** `fermion-number-prime-support-selector-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [PROVED FINITE SOURCE END] [CONJECTURE]`
- **Scientific status:** finite selector is not new scientific knowledge; the infinite completed
  source theorem is unclassified
- **Lean:** `formal/GaloisForLFunctions/KoszulCohomology.lean`,
  `formal/GaloisForLFunctions/PrimeWordSupportSelector.lean`
- **Inputs:** `prime-loop-connectivity-mixed-word-obstruction.md`,
  `prime-koszul-superdeterminant-cancellation.md`, `FredholmDeterminantEuler.lean`,
  `SoninCoupledPrimeResidual.lean`, `SeamSuspensionTrace.lean`

## Claim

There is a canonical finite fermionic incidence functional which deletes every mixed-prime closed
word while retaining every pure prime repetition with coefficient one.  Applied to the logarithm
of a finite colored-word determinant, it reproduces the finite Euler product exactly.  The only
place a nontrivial global selector can remain is the infinite-prime completion defect of the full
marked complex, before the scalar fermionic trace factors through the disconnected prime-axis
quotient.

The proposed RH chain is

```text
connected finite prime-word transfer system
  -> exterior Fock space on the active word support
  -> fermion-number supertrace deletes support size other than one
  -> exact finite Euler logarithm and Euler determinant
  -> source-defined cofinal marked-complex completion with Gamma boundary
       [OPEN CORE A: closed completion defect independent of prime exhaustion]
  -> completed relative determinant equals Xi
       [OPEN CORE B: prime--Gamma comparison before reading the Xi divisor]
  -> reflected positive cohomology or self-adjoint quadratic realization
       [OPEN CORE C: positivity must live before scalar axis quotient]
  -> quadratic spectral reality
  -> RH.
```

## Finite selector theorem

For a finite active support `S`, put `r=|S|` and let

```text
F_S = exterior algebra(C^S),
N = exterior-degree number operator.
```

Then

```text
-Str(N | F_S)
  = sum_(j=0)^r (-1)^(j-1) j choose(r,j)
  = r(1-1)^(r-1)
  = 1,  r=1,
    0,  r=0 or r>=2.                                  (1)
```

This is the derivative at `-1` of `(1+x)^r`.  In the equivalent marked-Koszul form, choose one
marked direction and alternate over its complement:

```text
r * sum_(k=0)^(r-1) (-1)^k choose(r-1,k) = 1_[r=1].   (2)
```

Lean formalizes `(2)` as `koszulSupportMarkedExponent_eq`, with the pure and mixed consequences
`koszulSupportMarkedExponent_one` and `koszulSupportMarkedExponent_eq_zero`.

Let `w=(p_1,...,p_m)` be a closed colored word and apply `(1)` to its distinct-prime support.
For the Euler amplitude `a(w,s)=product_i p_i^(-s)`, the selected logarithmic word sum is

```text
sum_(m>=1) 1/m sum_w a(w,s) 1_[|supp(w)|=1]
  = sum_p sum_(m>=1) p^(-ms)/m
  = -sum_p log(1-p^(-s)).                              (3)
```

Exponentiating `(3)` gives the finite Euler product.  Mixed words are cancelled by a canonical
fermionic insertion rather than by declaring the transfer graph disconnected.

## Hard no-go test

The scalar functional in `(1)` is cyclic because support is invariant under cyclic permutation.
It annihilates every word using two or more prime colors.  Those mixed words form a two-sided
ideal, and the scalar functional therefore factors through the quotient in which products of
distinct prime colors vanish.  That quotient is the direct sum of the one-prime axes.

Hence the finite scalar determinant has exactly the desired Euler value but is structurally blind
to connected prime--prime coupling.  The fermionic selector solves the mixed-word arithmetic and
simultaneously proves that no scalar finite-level supertrace can supply the RH orientation.

This closure is now formal rather than heuristic.  The mixed-word predicate is preserved under
arbitrary left and right concatenation (`IsMixedPrimeWord.sandwich`), and
`primeWordSupportSelector_sandwich_eq_zero` annihilates every such contextualized word.  The
converse theorem `primeWordSupportSelector_eq_one_iff` proves that no scalar nonzero sector other
than a single-prime axis remains.

## Positive statement from the no-go

The full marked complex can carry more information than its scalar character.  A live construction
must retain one of the following before taking supertrace:

1. a non-Hausdorff algebraic-range/closed-range class at the cofinal prime boundary;
2. a determinant-line holonomy or torsion class of the marked differential;
3. a reflected positive cohomology class created by the Gamma boundary;
4. an exhaustion anomaly measuring failure of scalar axis-factorization to commute with closure.

At every finite level the class may be trivial while the cofinal completion is nontrivial.  This is
not an unspecified derived limit: the marking and the finite character are fixed by `(1)`, so the
only admissible defect is the failure of the marked-complex closure to commute with the
fermion-number trace.  It must be independent of prime ordering and regularization.

## Concrete coupled-Sonin carrier

The corpus already contains a non-block-diagonal bosonic carrier on which this construction can be
tested.  `SoninCoupledPrimeResidual.lean` stacks every weighted prime-power residual over the same
Sonin input space.  Its positive Gram operator retains all cross-prime overlaps, and its second
trace moment splits exactly as

```text
diagonal prime-power energy + nonnegative mixed invariant I_2.
```

This is stronger than the block-diagonal Sonin model and supplies the connected raw word geometry
needed here.  It also exposes the sign obstruction sharply.  The ordinary positive Gram squares
the Euler coefficients and keeps mixed energies; the fermion-number trace deletes the mixed
energies and restores the pure Euler logarithm, but its scalar supertrace is no longer a positive
functional.

The resulting concrete open construction is a supersymmetric coupled-Sonin complex whose
differential pairs every mixed prime overlap while leaving the pure prime repetitions and the
Gamma boundary as unpaired cohomology.  Positivity must hold on that cohomology, not on the flat
supertrace.  If the pairing is merely declared from the support decomposition, it factors through
the axis quotient and is dead; it must be generated by the existing coupled Sonin incidence and
commute with the reflected Gamma seam.

## Two-ended audit

- `[PROVED]` finite prime Euler factors are explicit Fredholm determinants;
- `[PROVED]` connected positive word systems create unwanted mixed primitive factors;
- `[PROVED]` the absolute Koszul superdeterminant also cancels the pure factors;
- `[PROVED]` fermion-number marking gives the exact singleton-support selector;
- `[PROVED NO-GO]` the scalar selector factors through the disconnected prime-axis quotient;
- `[OPEN CORE]` construct the cofinal marked-complex completion defect from the Euler--Gamma/theta
  source and prove it is exhaustion-independent;
- `[OPEN CORE]` identify its relative determinant with Xi without inserting the Xi divisor;
- `[OPEN CORE]` prove the defect cohomology has a positive reflected quadratic realization;
- `[PROVED CONSUMER]` a genuine source-defined self-adjoint realization of the quadratic Xi
  spectral parameter implies RH.

## Kill conditions

Retire the chain if the completion is a Hilbert direct sum of the one-prime quotients, if its
defect is chosen after evaluating Xi, if different cofinal prime orders give different classes, if
the Gamma sector is merely multiplied on after scalarization, or if positivity is equivalent to
the Xi Cauchy-kernel sign without an additional source theorem.

## Gates

- [x] finite support selector proved on paper and in Lean
- [x] scalar quotient-blindness isolated with a positive successor
- [ ] closed cofinal marked complex and canonical Gamma boundary constructed
- [ ] completion defect and determinant comparison proved
- [ ] positive reflected realization proved
- [ ] terminal RH theorem composed and formalized
