# Theta-prefix reading of horizontal collision charge

- **ID:** hef-theta-collision-reading
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q2/charge.
- **Statement:** Read the actual Xi collision charge on each height window from finite integer
  theta prefixes, with a quantitative error tending to zero.

## Candidate kernel

For the zero current `μ=Σρ mρ δρ`, the pair kernel
`exp(−(Im z−Im w)²/ε²) − exp(−|z−w|²/ε²)` is nonnegative.
On a finite divisor it tends to the indicator of distinct points sharing an ordinate.
The pair sum therefore tends to the exact horizontal collision charge.
Its error is bounded by the squared total multiplicity times a Gaussian in the
minimum nonzero ordinate or point separation. Multiplicities remain intact.

Replace both currents by the finite theta curvature density. Compact C² testing
has a proved quantitative source error (`PolynomialThetaReadingError`), so a uniform
bound for derivatives of the two-variable kernel would control the product-current
error. Use shrinking smooth height collars to realize the exact window convention.

## Existing inputs and obligations

- `xiHorizontalCollisionCharge_eq_sum_pairs`: the exact ordered-pair charge.
- `tendsto_xiSourceThinSliceMass`: an existing full-source pair-current limit.
- `exists_polynomialThetaLocalReading_error_bound`: finite theta prefix error for
  shrinking local tests, without a zero-free contour premise.
- Open: uniform product-current error, height-collar treatment, and one explicit
  prefix/width schedule with all constants defined.

This construction reads the charge. It does not supply the bound below its first
nonzero quantum required by Q2's orientation equality.
