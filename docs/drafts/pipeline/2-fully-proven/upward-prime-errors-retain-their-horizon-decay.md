# Upward prime errors retain their horizon decay

- **ID:** upward-prime-horizon-decay
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean pending)
- **Statement:** For each positive conductor, the actual upward source has normalized squared residual `≤C_m(c^5/log N+c^10(log N/N)^2)` when `c≥1`, `log N≥1`, and `N≥4(exp(1)+3)^2 c²`.

## Paper proof

The exact upward-row identity has three differences: logarithmic kernel replacement, the two prime-index cutoff changes, and the signed reciprocal affine-shell remainder.

1. The proved pointwise kernel error is `≤D_m c²(B+1)³ A(N+B)/N`. For `B≤N` and `log N≥1`, the exact Mertens row bound gives `A(N+B)≤J log N`. Squaring and summing `1/n` preserves normalized error `O_m(c^4(B+1)^6(log N/N)^2)`.
2. Put `b=B+1`. The literal boundary row is bounded globally by `D_m b²/√n`. When `N/n≥4b`, its square is at most `2D_m²b^4/N`: use the proved `8b/√⌊N/n⌋` Mangoldt-window bound and `n⌊N/n⌋>N/2`. Summation gives `2D_m²b^4`. The remaining harmonic rows cost at most `D_m²b^4(1+log(8b))≤8D_m²b^5`. Thus the unnormalized boundary square budget is `O_m(b^5)`.
3. The two reflected affine shifts have the Lean-proved budget `O_m(c^5)` from [affine-shell-errors-have-a-uniform-harmonic-budget.md](../3-formalized/affine-shell-errors-have-a-uniform-harmonic-budget.md). Their average retains this bound.

The actual strip has `B+1≤(exp(1)+2)c`. Apply `(a+b+d)²≤3(a²+b²+d²)` and retain both horizon decay rates. No source orientation, prime power, or boundary is removed.

## Remaining route gap

This strengthens the actual source estimate. Its conductor constants still need uniform control on a family that captures negative eigenvectors; the complete signed residual and physical separated-bump synthesis remain necessary.
