# The projected arithmetic minimum balance is not a complete exclusion law

- **Stage:** 5-failed, the specified sufficient-condition conjecture only
- **Source:** [frozen F, subsequent H and I, and paper proofs](../1-in-progress/arithmetic-minimum-phase-completeness.md)

## Rejected claim

The conjecture claimed that the exact real arithmetic balance of the normalized deletion remainder would recognize zeta zeros or exclude off-line points. On the actual source that balance is precisely `Re(zeta(s)/(s(s+1)))=0`.

## Proved obstruction

For every zeta zero in the open strip, every neighborhood contains a nonzero point satisfying this projected balance. Any strip zero also forces an off-line nonzero point satisfying it. These are Lean theorems on the actual source, not replacement-function examples. They use no numerical input and no simplicity assumption. The statements are quantified over actual strip zeros; this module does not separately prove existence of a strip zero.

The proof combines analytic openness, the coefficient-side negative zeta value on the real strip, and the intermediate value theorem on a vertical line. Exact locations are not supplied. The numerical report separately gives off-line examples and observed finite-grid minimum labels.

## Positive survivor

The complete complex identity is

`sum_(p>=1) mu(p)W_p/[p u(u+1)] = -1/[2u(1-u)] - conjugate(zeta(s)/(s(s+1)))`,

where `u=conjugate(s)`. Both components are retained, and the full discrepancy vanishes exactly at zeta zeros. At a zero the imaginary sum is `Im(s)(2 Re(s)-1)/(2 |u(1-u)|^2)`.

The projected equality itself is enough for the exact negative profile mean, existence of negative entries, and minimum attainment whenever the exponent lies below the decay threshold. Also, power tilting orders any two attained minima without using the zero equation. These positive statements, including the two existence obstructions, are formalized in `ArithmeticMinimumPhaseCompleteness`; [certificate](../3-formalized/arithmetic-minimum-phase-completeness.md).

## Scope boundary

This retires the projected balance as a sufficient condition. It does not retire arithmetic zero classification or rule out an additional real or complex arithmetic constraint. The exact imaginary formula is a record of the missing location information, not a proof that its sum vanishes. The global minimum labels of the nonzero witnesses are not prescribed by these existence theorems.
