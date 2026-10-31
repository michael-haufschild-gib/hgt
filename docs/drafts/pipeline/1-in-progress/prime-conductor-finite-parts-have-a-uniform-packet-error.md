# Prime conductor finite parts have a uniform packet error

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Q1/O1](three-frontier-questions-full-solutions.md);
  [undilated component](../3-formalized/undilated-prime-heads-have-a-uniform-torsion-finite-part.md).

For `Q,N≥2`, put `M=sum_(m≤Q)a_m²`, `v_m,N=u_m/sqrt(n log N)`,
`T=sum_(m,l≤Q)a_m a_l I(m,l)/sqrt(phi(m)phi(l))`, and
`L=sum_(m≤Q)a_m²[log m+tau(m)]`. Conjecture one absolute `C>0` with

`|<sum a_m v_m,N,P_N sum a_m v_m,N>−log N·M+T+L|`
`≤C[(1+log Q)²/log N+Q⁴/(N^(1/4)log N)]M`.

The harmonic Gram finite part would then cancel the same torsion term in
`<sum a_m v_m,N,[(log N)I−P_N]sum a_m v_m,N>`, leaving
`sum a_m²[gamma+log m+tau(m)]` with the same error after enlarging `C`.

## Proposed mechanism

Let `D_k` be exact conductor dilation and `E_k=D_k−I`. The centered
prime correction is `2/log N sum_(k≤N)Lambda(k)<a,G_(N/k)E_k a>/k`.
Insert `G_Y=H_Y I−T+R_Y`.

The period head and its entrywise absolute majorant have norm `O(1+log Q)`.
The missing logarithmic-moment lemma is

`sum_k Lambda(k)log(k)|E_k(m,l)|/k`
`≤(1+log l)sum_k Lambda(k)|E_k(m,l)|/k`.

For `k=p^j`, a nonzero mixed transition removes `min(j,v_p(l))`
prime factors. Before saturation, `log k=log(l/m)`. After saturation,
the geometric tail adds mean logarithmic excess `log p/(p−1)≤1`.
On the diagonal its mean logarithmic weight is
`p log p/(p−1)≤log l+1`. This would bound the harmonic-scalar correction
and the torsion times period-head term by `O((1+log Q)²)M`.

For the remainder, split at `floor(sqrt N)`. Use
`||R_(N/k)||≤Q²k/N` and `||E_k||≤sqrt k+1` below the split.
Above it, only prime powers with `p≤Q` contribute; their geometric tails,
together with the logarithmic Gram plateau, give `O(Q⁴/N^(1/4))M`.
The omitted period-head tail fits the same error.

The logarithmic-moment lemma, bilinear Gram bounds, finite-horizon transfer,
and final Lean theorem remain unproved. This concerns the literal prime
compression; the Gamma, pole, and successor-shell comparison remains open.
