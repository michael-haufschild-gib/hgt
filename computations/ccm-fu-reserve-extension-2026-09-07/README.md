# Direct reserve-extension induction diagnostic

Numerical research guidance only. No value from this directory enters Lean.
The frozen question and the attempted complete proof are in
[reserve-extension induction](../../../1-in-progress/ccm-fu-reserve-extension-induction.md).

For the actual source let `Phi(P)=Q_P+2sqrt(G_P D_P)` and `B=Q_empty`.
Does every proper state with `Phi(P)<=B` have a next prime whose successor
also satisfies that certificate, or completes the order? This tests local
inductive closure, which is stronger than existence of some complete path
inside the certificate set. Separately, the first script tests homogeneous
descent `min_q Phi(P+q)<=Phi(P)`.

## Results

- [screen.py](screen.py) reads the existing 8860 source states through32.
  All 7350 certified proper states extend. Homogeneous descent fails in
  975 states; the first is M=7, P={2}, where Phi is about0.01874618 and the
  best successor's Phi is about0.03181899, both below B about0.048776.
  Full records are in [summary.json](summary.json).
- [extension.py](extension.py) checks all 1746944 subset states at every
  integer cutoff33..64. All 999880 certified proper states extend. It
  reuses the saved defect/unit-clock table, obtains coefficients by exact
  clipped dilation, and uses signed subset sums for every oriented fibre.
  Original diagonals match the saved greedy summary within the original
  tolerance. Direct prime merging independently checks every initial,
  first-prime and terminal state; the script also checks every failure and
  outgoing successor if one occurs. There are no reported failures.
  Per-cutoff counts and audit errors are in
  [extension-summary.json](extension-summary.json).

Both tests retain `1e-12*max(1,B)`. The extended arithmetic uses NumPy
long-double operations on the existing source table; this does not remove
the original table's numerical uncertainty. These are finite numerical
passes. The universal source inequality and RH remain unproved.

## Execution and provenance

RunPod host: `ssh root@157.157.221.29 -p 27094 -i ~/.ssh/id_ed25519`.
Owned directory: `/root/ccm_fu_reserve_extension_20260907_01a077d3`.
Each script ran in the foreground with `timeout 60s python3 <script>` and
eight workers on a 16-core host. BLAS/OpenMP threads in the extended test
were limited to one per worker. Python3.8.10 was used. Recorded elapsed
times were about0.047 seconds and0.968 seconds respectively. No timeout or
background computation occurred.

Input hashes are embedded in both JSON outputs. Downloaded output and
local script hashes matched all four remote originals:

| File | SHA-256 |
| --- | --- |
| screen.py | 7b27c4f975c2c8265b84ede5e65a6d6bb61288ef9f3c1602acd6a194cfd85aec |
| summary.json | 46e814512b7eea375fda0888594e9eddda76243ee5eb6a672659507fef4431c2 |
| extension.py | 86767199fb5e643e1448a49723d4169ad03dbc0cd62e62e6e2c5b866495dff21 |
| extension-summary.json | d0cbea66a075503139872a122a4306dc5cf05b7c335d48d7b47b54a5ffe42248 |

The owned remote scripts, inputs, outputs and directory were removed after
hash verification. No owned numerical process remains.
