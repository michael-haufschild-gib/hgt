# Route R depth-one positive-completion no-go

- **ID:** `route-r-depth-one-positive-completion-no-go`
- **Status:** formally proved
- **Route:** Route R primitive-current singular continuation
- **RH status:** does not prove RH; removes positive direct-sum completion from open core

## New theorem

Let `K_1` be central diagonal of depth-one order-growing von
Mangoldt--Gamma two-boundary kernel. First source atom, `n=2`, has exact norm square

```text
1 / (128 log(2) (log(2)^2 - 1/4)^2).
```

Certified logarithm bounds imply

```text
1/5 < first_atom <= Re K_1(0,0).
```

Canonical completed zeroth prime--archimedean moment satisfies existing unconditional bound

```text
normalizedPrimeArchMoment(0) < 29/625 < 1/5.
```

Therefore

```text
normalizedPrimeArchMoment(0) < Re K_1(0,0).
```

More strongly, for every complex correction `C` with nonnegative real central diagonal,

```text
K_1(0,0) + C != normalizedPrimeArchMoment(0).
```

If equality is imposed without a sign hypothesis, correction must satisfy sharp certified budget

```text
Re C < -96/625.
```

## Why this moves frontier

Order-growing source Gram was live positive candidate for completed value identity. Exact first
coordinate now falsifies every orthogonal positive completion, including addition of independent
positive Gamma and polar clocks. Failure occurs before asymptotics, local-uniform analyticity, or
higher mixed jets: one actual Euler atom already exceeds complete target mass.

This is not generic Gram algebra and not target-fed restatement. It compares literal source atom
against independently derived complete prime--archimedean source moment and yields strict
incompatibility.

## Surviving hard object

Completed source kernel must contain one of:

1. forced negative Schur complement;
2. genuinely off-diagonal Euler--Gamma/polar cross term;
3. singular indefinite coupling before positive codiagonal formation.

Positive direct sum, orthogonal channel addition, and any nonnegative central-diagonal correction
are excluded. Route R annihilator must now be constructed in signed/off-diagonal pre-codiagonal
geometry while remaining conservative on completed Green provenance.

## Lean certificate

File:

```text
formal/GaloisForLFunctions/RHTower/
VonMangoldtGammaJetPositiveCompletionNoGo.lean
```

Principal declarations:

- `depthOneOrderGrowingFeature_two_normSq_eq`
- `one_fifth_lt_depthOneOrderGrowingFeature_two_normSq`
- `depthOneOrderGrowingKernel_zero_zero_eq_normSq_tsum`
- `normalizedPrimeArchMoment_zero_lt_depthOneOrderGrowingKernel_zero_zero_re`
- `depthOneOrderGrowingKernel_no_nonnegativeDiagonalCompletion`
- `depthOneOrderGrowingKernel_completion_forces_negativeBudget`

Verification:

- direct `lake env lean` passes;
- no `sorry`, `admit`, axiom, opaque, unsafe, or numerical experiment;
- proof uses exact source formula, certified analytic bounds for `log 2`, and existing
  unconditional moment bound.
