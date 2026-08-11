# Mass-shifted affine kernel Lorentz signature

## Claim

For every `w > 1/2` and physical source point `x ≥ 1`, restriction of the adaptive mixed Gamma kernel to real affine amplitudes `A(X)=b+cX` is a nondegenerate binary quadratic form of signature `(1,1)`. Its determinant is an explicit negative multiple of the positive discriminant polynomial already isolated in the linear-amplitude pointwise no-go. In particular, even monic positive-root amplitudes `X-r` meet the pointwise negative cone.

## Why this matters

This identifies the universal obstruction behind all failed fixed-sign kernel arguments. Admission cannot merely impose monicity, positive roots, or degree one; it must select a safe cone sector before reflection aggregation. The result directly sharpens the open admission-sensitive arithmetic source law in `docs/reports/mass-shifted-spectral-trace-route.md` §9.3.

## Proof obligations

1. Derive the exact affine-amplitude kernel formula from corpus primitives.
2. Compute the symmetric Gram determinant and prove it strictly negative on `w>1/2`, `x≥1`.
3. Exhibit the exact monic positive-root minimizer and prove its kernel value negative.
4. Audit which actual first-face null-polynomial laws constrain the admitted root.
5. Formalize all unconditional findings and wire the module into `RHTower.lean`.

## Hostile tests

- No inference from arbitrary affine amplitudes to admitted null flags.
- No replacement of source-first bilinear formation by a fixed linear reporter.
- No numerical or asymptotic evidence.
- Pointwise negativity alone does not decide the integrated prime-versus-continuum domination gate.

## Status

Formalized unconditionally in
`XiShiftedAdaptiveMixedGammaKernelPointwiseNoGo.lean`.

Exact formal survivors:

- affine kernel law with Gram determinant
  `-12 w⁴ D(z) < 0`;
- literal signature witness: positive coordinate axis and negative monic direction;
- exact positive-root monic minimizer
  `r_*=B₃(z)/(4w²B₂(z))`;
- strict negative kernel value
  `-x^{-(1/2+w)}D(z)/(192w⁹B₂(z))`.

Admission audit exposed a stronger positive successor: actual canonical first-face ratio is
confined to a safe subcone on `w<1`. That successor is tracked separately in
`mass-shifted-degree-one-admitted-kernel-positivity.md`.
