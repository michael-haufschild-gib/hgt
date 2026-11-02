# Prime successor edges pay nonconstant packet mass

- **ID:** prime-successor-edges-pay-packet-mass
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Σ1c; `shell-degree-bounds-and-complete-packet-rigidity.md`.
- **Statement:** For each nonnegative nonzero `C²` profile supported in `[0,1]`, some fixed overlap threshold ensures
  `½ affineDirichlet ≥ (1/64)[primePoleScale(⌊N/(16Q²)⌋)−primePoleScale(Q)] nonconstantPacketMass`
  for all `Q≥2`, all horizons and all conductor packets.

## Mechanism
For every prime `Q<p≤N/(16Q²)`, retain edges `(n,pn+1)` with
`A=N/(2p)`, `K=N/(4p)`, `A<n≤A+K` (integer quotients).
Then `pn>N/2`, `pn+1≤N`, and `n≥2`, so the exact-ratio subtraction vanishes.
The scaled logarithmic lag has absolute value at most `2/c`.
Continuity of the profile autocorrelation supplies a common normalized lower bound `1/2`
once `c` exceeds a profile-dependent constant. The actual matrix weight is then
at least `log p/(2N)`, since `√p√n√(pn+1)≤pn+1≤N`.

The proved coprime-successor window gap gives at least
`(K−Q(Q−1)) nonconstantPacketMass ≥ N/(16p) nonconstantPacketMass`.
Different `(p,n)` give different ordered edges. Summing these nonnegative edge contributions
in the literal affine Dirichlet energy yields the factor `1/64` after multiplication by `1/2`.
This supplies the missing comparison with the complete form's actual successor energy;
the shell, pole and archimedean payments remain separate obligations.

## Obligations
- Verify integer window bounds and injectivity.
- Prove the actual non-ratio matrix lower bound from the profile autocorrelation.
- Combine with the existing successor gap, then audit the exact capstone in Lean.
