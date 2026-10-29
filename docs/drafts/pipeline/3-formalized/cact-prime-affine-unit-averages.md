# Actual prime averages of affine Ramanujan modes

Status: formalized, individually checked, and wired.

## Actual source theorem

For every real pattern `F` on `ZMod q`, with `q>0`, the literal reading
`sum_(1<=k<=Y) F(k mod q)*Lambda(k)/k - kappa_F*log(Y)` has a finite limit,
where `kappa_F` is the unit mean. No sign or multiplicativity restriction is
placed on the pattern. Convergent non-unit prime-power classes are retained.

For fixed positive integers `A<=B`, subtracting endpoints `AN` and `BN`
cancels the finite part and proves

```
lim_(N->infinity) sum_(AN<k<=BN) Lambda(k)/k * c_q(kn+h)
  = (log(B)-log(A))*c_q(n)*c_q(h)/phi(q).
```

The normalized-mode version is proved as well. Conductor `q`, natural affine
parameters `n,h`, and endpoints `A,B` are fixed throughout the limit.

## Mechanism and corpus inputs

Partition the actual weighted prime reading into residue classes. Existing
residue-class Mertens constants supply the unit terms, and the existing
non-unit convergence theorem supplies the remaining classes. Apply the
result to `r -> c_q(rn+h)`. The finite affine unit identity identifies its
mean exactly. These scalar source limits require no prime model or new
assumed equidistribution input.

## Lean closure

- `PrimeResidueWindowsConvergeToTheirUnitMean.lean`: needed check3765 and final check52715 passed clean.
- `ActualPrimeWindowsDiagonalizeAffineRamanujanModes.lean`: final check30789 passed clean.
- Its finite unit-average dependency: needed check86562 and final check85125 passed clean.

Every printed capstone dependency list contains only `propext`,
`Classical.choice`, and `Quot.sound`. All three modules are wired into the
programme umbrella. No full or umbrella build was run.

## Boundary

The limits give no growing-conductor norm estimate, spectral exhaustion, or
sign bound for the full overlapping Weil form. Continuous compact-weight
transfer was only proposed; it remains an explicit deferred conjectural
extension in the existing successor backlog. No completed paper proof of
that extension is claimed. The surrounding corpus's residue-class Mertens
input and fixed-profile first-overlap positivity are not new results here.
