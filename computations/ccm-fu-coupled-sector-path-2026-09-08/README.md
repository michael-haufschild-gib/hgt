# Coupled-sector steepest-path diagnostic

Numerical evidence only. Placement in `computations` does not make these
finite sign assertions paper proofs or Lean theorems. RH remains open.
The [frozen protocol and proof-attempt analysis](../../../5-failed/ccm-fu-coupled-sector-steepest-path.md)
give the exact candidate claims and their limits.

Starting core: `{3,5,7,11,13}`. Retain prime two. At each step choose the
least transverse-energy gain among all remaining primes `q≥15`, `q²≤M`;
break ties by prime size and continue through the complete sector.
Here `T=Q−F_empty²−F_{2}²` uses the actual divisor source.

| M | Steps | Strict traps | Initial T | Sum of positive gains / initial T |
|---:|---:|---:|---:|---:|
| 512 | 2 | 0 | 127.8142981 | 0 |
| 2048 | 8 | 6 | 2175.2811182 | 0.2285359840 |
| 8192 | 18 | 13 | 35951.4672446 | 0.7790932067 |
| 32768 | 36 | 32 | 573684.4280752 | 1.1289135566 |

`paths.json` preserves every candidate gain, selection, processed core,
receiving coordinate and explicit before/after transverse energy.
The proposed nonpositive-step rule fails. The proposed cumulative budget
of one initial T also fails in this screen. These observations do not
exclude another order or a constant bound on signed peak energy.

## Independent audit

The first trap has `M=2048`, `P={3,5,7,11,13,41,43}`. The independently
reconstructed original time sum at 80 decimal digits gives:

| Candidate q | Transverse gain |
|---:|---:|
| 17 | 306.035203209642417609 |
| 19 | 260.848280343433588340 |
| 23 | 149.935796987482186732 |
| 29 | 76.573766806252673998 |
| 31 | 71.702535777768087314 |
| 37 | 13.205127232065452358 |

All candidates were independently enumerated and factored. All six
explicit fibre mergers agree with the paired-cost formula within
`3e−78`; their gains agree with the screen within `9e−12`. Prime 37
remains the strict minimizing choice. Before insertion, T is
2080.152316180005149463..., the empty coordinate is
1.832315084480156480..., and the prime-two coordinate is
−7.632481977949304244... .

This is high-precision floating-point agreement, not rigorous interval
arithmetic or a Lean counterexample. The cumulative failure at 32768
has the primary screen's binary64 merger checks, not this independent
high-precision audit.

## Execution and provenance

Executed only on the supplied RunPod SSH host. Primary: four cutoff
workers, 0.219238 seconds. Audit: four coefficient workers, 0.418039
seconds. Numerical-library threads were one. Each job had an internal
90-second deadline and external 100-second timeout plus five-second
kill grace. No enlargement, repeat scan, or numerical Lean certificate.

`source_screen.py` is the unchanged previously reviewed quotient-block
source routine; importing its `source` function does not execute its
older screen. `path_screen.py` runs the new frozen path question.
`audit.py` uses separately factored squarefree support and the original
time-sum source, rather than the quotient-block evaluator.

Both jobs exited successfully. Local and remote SHA-256 hashes matched
for all five files before removal. No process had the owned remote
directory as its working directory. The directory
`/root/ccm-sector-path-2hz0FR`, including Python import cache, was removed.

| File | SHA-256 |
|---|---|
| `source_screen.py` | `77bcc9058e05d01f20fdbe49536ab800b5a046512324cb2e5e2605cde2313427` |
| `path_screen.py` | `85cab391031e2ba0939655a86f6c1b65a339810115d0fa25a82be76d96183776` |
| `paths.json` | `9df62fcc9be4974eba104710f5b3d9abebf7819a1663baf451b23911ec856e40` |
| `audit.py` | `5c6183212bca23c6e472323c83668a30fdcd58e28efc513428977a84a5ac7561` |
| `audit.json` | `a3480c581d65aa4d5bf30a05969100c6dba332f263826c0a53a4ca9bda4784d4` |
