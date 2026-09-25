# Numerical enclosure lead

`enclosure_probe.py` studies `S^k(27ace−S(b+c+d)c)`, where `S=a+b+c+d+e`, on `|a|+|b|+|c|+|d|+|e|=1`. Source and `enclosure-results.json` were downloaded from the authorized Runpod host, directory `/root/chronological-chord-capacity`.

Method: all 16 sign chambers modulo global reversal, both output signs, depths k=0,…,6; 512 Dirichlet candidates and all 31 nonempty equal-mass supports per chamber, followed by eight analytic-gradient SLSQP starts. Ran 224 tasks on 24 workers with one BLAS/OpenMP thread each (NumPy 1.24.4, SciPy 1.10.1). Fifty of 1,792 local runs reported non-success; all returned probes were projected back to the unit simplex before evaluation. This is not an exhaustive/global optimization certificate.

| Depth | Largest response found |
|---|---:|
| 0 | 1.0438763935978541 |
| 1,…,6 | 1.0 |

Depth-zero probe, rounded: `(0.3035875144, 0, −0.3657335926, 0, −0.3306788931)`, with displacement about `−0.3928249712`. Its middle and endpoint signs differ from the earlier symmetric rational witness. Algebraic reasoning suggests the reduced profile `27z(1−z)^2/4 + 28z^3/27`, whose stationary equation is `841z²−972z+243=0`; identifying this as the global signed optimum remains unproved.

Every positive-depth numerical maximizer above can be replaced by the exact pure-central-jump probe, which has response magnitude one. The depth-one lead has now been proved by an independent symbolic argument: OneEnclosure.lean proves |S(27D−R)|≤V⁴, and EnclosureCone.lean proves that the minimal depth is exactly one. Both targeted leaf builds passed. The argument also covers AD−BR with 0≤A≤27B. The degree-zero optimizer remains an unproved global-optimum lead. No numerical value, optimizer output, or certificate enters Lean.
