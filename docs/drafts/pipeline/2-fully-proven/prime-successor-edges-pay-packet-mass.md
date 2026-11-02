# Prime successor edges pay nonconstant packet mass

- **ID:** prime-successor-edges-pay-packet-mass
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Σ1c; `shell-degree-bounds-and-complete-packet-rigidity.md`.
- **Statement:** For each nonnegative nonzero `C²` profile supported in `[0,1]`, some fixed overlap threshold ensures
  `½ affineDirichlet ≥ (1/64)[primePoleScale(⌊N/(16Q²)⌋)−primePoleScale(Q)] nonconstantPacketMass`
  for all `Q≥2`, all horizons and all conductor packets.

## Proof [PROVED HERE]
For every prime `Q<p≤N/(16Q²)`, retain edges `(n,pn+1)` with
`A=N/(2p)`, `K=N/(4p)`, `A<n≤A+K` (integer quotients).
Then `pn>N/2`, `pn+1≤N`, and `n≥2`, so the exact-ratio subtraction vanishes.
The scaled logarithmic lag has absolute value at most `2/c`.
Continuity of the profile autocorrelation supplies a common normalized lower bound `1/2`
once `c` exceeds a profile-dependent constant. The actual matrix weight is then
at least `log p/(2N)`, since `√p√n√(pn+1)≤pn+1≤N`.

The cutoff implies `N≥16Q²p`, hence `K≥4Q²` and `A≥8Q²`.
The division inequalities give `2pn>N` and `4pn≤3N`; thus `n≥2` and `pn+1≤N`.
Also `N<4p(K+1)≤8pK`, so `K≥N/(8p)`.
Since `Q(Q−1)≤K/2`, the proved coprime-successor window gap gives at least
`(K−Q(Q−1)) nonconstantPacketMass ≥ N/(16p) nonconstantPacketMass`.
Primality and `p>Q` imply `gcd(p,Q!)=1`, as required by the window gap.
Different `(p,n)` give different ordered edges: equality fixes `n`, then positive `n` cancels.
Summing these nonnegative edge contributions
in the literal affine Dirichlet energy yields the factor `1/64` after multiplication by `1/2`.
This supplies the missing comparison with the complete form's actual successor energy;
the shell, pole and archimedean payments remain separate obligations.

If `N/(16Q²)<Q`, the displayed prime-scale difference is nonpositive and the
claim follows from nonnegativity of the affine energy. Otherwise the retained
prime sum equals that difference exactly.

## Formalization
Integer window bounds, literal matrix comparison and the finite edge injection are being
formalized in `ArithmeticCouplingTheory`; the successor-gap input is already kernel-checked.
