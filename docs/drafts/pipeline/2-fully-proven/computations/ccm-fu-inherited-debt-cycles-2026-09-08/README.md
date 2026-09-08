# Inherited prime-two debt: zero-mean source cycles

The frozen question and protocol are in the
[bridge card](../../1-in-progress/ccm-fu-inherited-debt-source-cycles.md).
Numerical evidence guides a separate analytic proof; it is not a Lean premise.

The finite linear program on all saved profiles K=2..512 has a positive
optimum, with support **2,11,15**. Independently reconstructed 80-digit
profiles give normalized circuit weights approximately
`(0.6323889274362208, 0.1833890798347072, 0.1842219927290720)` and quadratic
margin `0.00004566444109842622953296173072306365118`.
Both retained-coordinate balance residuals are at most `8.24e-84` in that
reconstruction; no near-degeneracy flag is raised. Exact balances and signs
still require symbolic proofs. The finite optimum is a solver result,
not a certified all-source extremum.

This distinguishes two requirements: a positive circuit can return the
retained field to its starting point while its quadratic covariance either
increases or decreases the external cost of inserting 2. The source at
2,11,15 has the debt-removing sign. Uniform capacity, clipping, overlap,
changing cores and exhaustive prime processing remain proof obligations.

The script ran once on the supplied RunPod with a 50-second internal and
60-second external deadline. NumPy 1.24.4 and HiGHS solved the finite LP;
three independent source audits ran in a process pool with configured cap
eight. Numerical libraries used one-thread environment settings. SciPy
reported `OptimizeWarning: Unknown solver options: threads`; this option
was not recognized by its wrapper. Total recorded script runtime was
0.01611385 seconds. No source channels were regenerated for the primary LP
and no cutoff range was extended.

The downloaded output retains every optimizer weight, equality residual,
dual coefficient, solver status, selected source reconstruction, circuit
weight and sign check. Remote hashes matched the downloaded files. The
owned remote directory `/tmp/ccm-debt-cycle-yiinlT` and all three files were
removed after download; no matching computation process remained.

SHA256:

- [screen.py](screen.py): `eadcfd7df9a7928fe774d5fca32933da85ea62845f9867447e4255e41f491f83`
- [summary.json](summary.json): `6f53cef1ffb410cf2cd070c88fb8c879a5bac991ad221a3d2dfc5eb04626a063`
- Reused [profiles.csv](../ccm-fu-coupled-prime-packets-2026-09-07/profiles.csv): `a8c93dfaec636b6f993f1e676e1e9ea744b699273cd66b0644afca4ffee8393d`
