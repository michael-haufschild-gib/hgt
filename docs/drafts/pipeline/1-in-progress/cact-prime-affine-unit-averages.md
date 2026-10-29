# Actual prime averages of affine Ramanujan modes

## Question

Can the finite unit-average diagonalization be realized by the literal von Mangoldt source on growing multiplicative windows?

## Mechanism

For every real function on `ZMod q`, partition the actual weighted prime sum into residue classes. Existing residue-class Mertens constants give a finite part for each unit class; non-unit classes converge. Subtract the readings at `AN` and `BN` before taking the limit. The constants cancel, leaving the unit mean times `log(B/A)`.

Apply this to `r ↦ c_q(rn+h)`. The finite affine unit law identifies its mean as `c_q(n)c_q(h)/phi(q)`. This supplies actual arithmetic scalar limits for successor corrections, without assuming a prime model or a new equidistribution input.

## Drafts and status

`PrimeResidueWindowsConvergeToTheirUnitMean.lean` and `ActualPrimeWindowsDiagonalizeAffineRamanujanModes.lean` are unchecked drafts. The latter includes the exact affine coefficient limit and its normalized-mode version. Their imports authorize needed oleans for the residue-window and finite-unit-average modules. Continuous compact-weight transfer remains to be written. No new theorem is claimed until the individual Lean checks pass.

## Scope

The intended limits keep conductor and affine parameters fixed. They do not supply a growing-conductor norm estimate, spectral exhaustion, or a sign bound for the full overlapping Weil form. The surrounding corpus already supplies the residue-class Mertens input and a fixed-profile first-overlap positivity theorem; neither is a new contribution here.
