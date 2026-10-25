# Paid perturbations preserve every normalized cofactor tangent

- **ID:** biarithmetic-paid-perturbations-preserve-escape-grams
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Parent:** [Golden digital module](../1-in-progress/biarithmetic-golden-digital-module.md)
- **Statement:** Adding a paid source to a nonzero scalar multiple of an escaping source preserves every normalized cofactor Gram tangent, with the same horizon subsequences. The conclusion concerns the entire tangent family, not just a chosen compactness extraction.

## Exact finite bounds

Let `v,w` be centered rows vanishing at zero, with `||w||_T<=B` at every horizon. Write
`u=t*v+w`, `t!=0`, and `d_T=||v||_T`. The reverse triangle inequality gives

`| ||u||_T - |t| d_T | <= B`.

Pronic dilation contracts by `1/sqrt(j)`. Bilinearity and Cauchy–Schwarz therefore give,
for every positive cofactor pair `j,k`,

`|<D_j u,D_k u>_T-t^2<D_j v,D_k v>_T|
 <= (2|t| B d_T+B^2)/sqrt(j*k)`.

These bounds retain the exact signed covariance. They use no convergence or number-theoretic
cancellation assumption.

## Passage to escape

If `d_T` tends to infinity, the first bound gives `||u||_T/d_T -> |t|`, hence
`E_u(T)/E_v(T) -> t^2` and `E_u(T) -> infinity`. Divide the second bound by `E_v(T)` to
obtain a zero limit. Since `|<D_j v,D_k v>_T/E_v(T)|<=1/sqrt(j*k)`, the identity

`K_u-K_v = [G_u-t^2 G_v]/E_u + [t^2 E_v/E_u-1] K_v`

proves `K_u(T;j,k)-K_v(T;j,k) -> 0`. Consequently every common Gram subsequence and every
limiting kernel is shared by the two rows. Equal kernels give the same canonical Hilbert
completion and dilation action. For sources with absolutely convergent means, the centered
prefix is exactly linear, so this applies to any paid source perturbation.

The separate ideal-stability theorem gives equality of repairing ideals as well. In the golden
application, the secondary tower and unit source are critical Wiener and hence paid, while the
primary tower's escape is proved by the digit-energy argument. Thus no unproved source estimate
is inserted as a premise of the eventual golden classification.

## Scope and verification

This is elementary Hilbert norm stability, used to compare all actual horizon tangents. It
does not prove escape of an arbitrary source and does not identify distinct phase kernels.

- [x] Exact finite inequalities and dependency-closed paper limit argument.
- [ ] Lean finite bounds and all-subsequence comparison.
- [ ] Application to the exact golden source.
- [ ] Direct source checks, axiom audits, and wiring.
