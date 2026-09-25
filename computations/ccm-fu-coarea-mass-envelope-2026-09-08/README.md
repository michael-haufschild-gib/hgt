# Complete-prime coarea mass-envelope diagnostic

Status: numerical evidence, not a Lean certificate or proof of RH.
Frozen protocol and mathematical interpretation:
[candidate and positive survivor](../../../5-failed/ccm-fu-coarea-mass-envelope.md).

For the complete literal source, retain signed fibre mass F and original
absolute fibre mass A. At every step score every remaining prime by
`B=max(A) Σ F²/A`, and select the minimum, breaking ties by smaller prime.
Continue through all primes. Zero-mass cells contribute zero. Exact
pair-variance scoring is checked against directly merged states.

| M | Prime steps | Strict positive steps | Peak B/B₀ | Peak raw Q/Q₀ |
|---:|---:|---:|---:|---:|
| 512 | 97 | 48 | 2.253066 | 1.262507 |
| 1024 | 172 | 99 | 4.061134 | 2.314992 |
| 2048 | 309 | 174 | 6.679569 | 3.892479 |
| 8192 | 1028 | 623 | 21.898473 | 15.800353 |

The monotone greedy candidate fails at all four cutoffs. These finite
ratios do not prove asymptotic unboundedness or refute another prime
order with a uniform quadratic ceiling.

## Independent audit

An 80-digit calculation reconstructed each coefficient from the original
time sum, rather than the screen's quotient-block source. It checked all
next-prime choices through the first trap at M=512, including the three
earlier greedy choices and their strict selection margins. The resulting
prefix is `2,479,509`. Every remaining prime increases B. The minimum is
prime 503, whose increase is

    0.7176745122862473498199952067917143373741...

The next-best choice is separated by approximately 0.8763005. The
80-digit pair-variance identity agrees with direct state reconstruction
to better than `1e-65`. This is high-precision floating arithmetic, not
interval arithmetic or a formal sign certificate.

The head slope `K-A_empty-2F_empty` equals approximately 63.50466829
after prime two and remains unchanged after 479 and 509. The head mass
then approaches the largest background cell mass. Inserting 503 crosses
that boundary. This motivates the exact late-prime slope law on the
linked card; its proof uses source identities, not these numerical values.

## Execution and artifacts

All mathematical computations ran on the user-specified RunPod at
`root@157.157.221.29:27094`, with four worker processes and BLAS/OMP
threads limited to one per worker. The screen took 6.666 seconds and
the independent audit 0.481 seconds. Each had a 90-second internal
deadline and a 100-second outer limit. Owned remote directory and jobs
were removed after downloading results.

- `screen.py`: frozen selection and complete trajectory.
- `source_screen.py`: unchanged source implementation reused from the prior experiment.
- `summary.json`: every trajectory and all candidates at each first trap.
- `audit.py`: independent original-time-sum audit and raw-energy peak extraction.
- `audit.json`: full audited prefix, every trap successor, and screen peak metrics.

Script and input SHA-256 values are stored in the JSON outputs. No local
mathematical computation was used.
