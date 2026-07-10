# FE-semilinear upper shears are automatically split

- **ID:** fe-semilinear-upper-shear-exhaustion
- **Stage:** 2-fully-proven
- **Type:** THEOREM / FAMILY EXHAUSTION / ROUTE NO-GO, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parent:** `sheared-seam-gauge-trivialization.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/FESemilinearShearExhaustion.lean`
- **Statement:** `[PROVED]` For every polynomial `f`, the upper-unit torsion shear
  `[[X^m,f],[0,1]]` is FE-semilinearly equivariant exactly when `f(-X)=-f(X)`.  That same condition
  makes the elementary row gauge `[[1,f],[0,1]]` FE-semilinear, and this gauge splits the
  presentation.  Hence every FE-compatible member of the entire upper-unit-shear family is
  FE-semilinearly row-equivalent to `diag(X^m,1)`.

## Proof

Let

`A_f=[[X^m,f],[0,1]]`, `A_0=diag(X^m,1)`,

`U_f=[[1,f],[0,1]]`, and `U_f^(-1)=[[1,-f],[0,1]]`.

Then `U_f U_f^(-1)=U_f^(-1)U_f=I` and

`A_f=U_f A_0`.                                                   (1)

Target FE parity is `R=diag(-1,1)`, source parity is
`R_s=diag(-(-1)^m,1)`, and FE acts on coefficients by `X -> -X`.  The upper-right entry of

`R A_f(-X)=A_f(X) R_s`                                           (2)

is

`-f(-X)=f(X)`,                                                    (3)

so (2) holds exactly when `f` is odd.

The FE-automorphism equation for the splitting gauge is

`R U_f(-X)=U_f(X) R`.                                            (4)

Its upper-right entry is again (3).  Therefore whenever `A_f` is FE-semilinear, the explicit gauge
that splits it is FE-semilinear too.  This proves the family exhaustion.

## Consequence

The constant shear `f=1` failed because it is even.  Replacing it by an odd polynomial repairs FE
equivariance but simultaneously repairs the splitting gauge.  No polynomial in a unit second lane
can produce the required equivariant extension class.

The obstruction is module-theoretic: the lower-right unit leaves no second torsion quotient to
extend.  A genuinely non-split candidate must put positive torsion order on both lanes.

## Gates

- **NOVEL:** This is not merely the explicit constant-shear correction.  It classifies the full
  polynomial upper-shear family and proves that FE compatibility and FE-compatible splitting are
  the same parity equation.
- **SIGNIFICANT:** It exhausts the current Fitting presentation family and forces the move from a
  torsion-plus-unit chart to a two-torsion extension.
- **FLOW TEST:** Fixed polynomial matrices only; no carrier or limiting parameter.

- [x] paper proof complete.
- [x] Lean formalization and capstone axiom checks complete.
- [ ] publication integration with the two-torsion replacement.
