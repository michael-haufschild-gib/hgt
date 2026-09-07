# Coupled head and prime-two packet directions

Bounded RunPod-only diagnostic; no numerical output is a Lean premise.

For each integer K from 2 through 512, group the actual signed dilation
channels by odd versus even index. These are the head and {2} coordinates
after every other child prime has been processed. Independently check the
{2} coordinate against exact prime-two reflection of the two adjacent
smaller odd-channel heads, retaining the clipped endpoint weight.

The first strict numerical positive circuit uses K=2,3,13. Its three positive
cross-product weights sum those source vectors to zero, with a nondegenerate
span. The maximum directional gap over the full sample is below pi. This
finite diagnostic does not prove any of those strict inequalities in Lean,
a growing coupled batch, complete source coverage, or RH.

Artifacts: [screen.py](screen.py), [profiles.csv](profiles.csv),
[summary.json](summary.json). The [research card](../../../1-in-progress/ccm-fu-coupled-prime-packet-balance.md)
records the independent analytic construction selected from this evidence.

Executed via `ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519`, using
`timeout 120s python3 screen.py` in the foreground. Eight forked workers,
32 available cores, shared read-only arrays, one BLAS/OpenMP thread per
worker. Actual run time 0.0185 seconds; NumPy 1.24.4. A containing-half-plane
check skips the triple search when no strict circuit is possible. All
511 profiles are retained; maximum absolute reflection discrepancy is
9.55e-18. No background computation or timeout occurred.

All three downloaded SHA-256 hashes matched the remote originals:

- script: `f5eeb18abb07d3e4b99c391f5b00f07397df8935d0a8484fac33416778ad95c8`
- profiles: `a8c93dfaec636b6f993f1e676e1e9ea744b699273cd66b0644afca4ffee8393d`
- summary: `21500e83735483b79bae39a2abcfd560650d1dc0220107525a0f116ee7077d9e`

The three owned remote files and execution directory were removed after
verification. Local script and results are retained for reproducibility.
