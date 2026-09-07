# Complete binary gcd compensation: discriminating diagnostic

**Result:** The proposed packet sign fails numerically. Among every 2,550
binary gcd packets at every saved cutoff 1 through 100, 59 are positive.
No cutoff, packet or failure was omitted. The first failing cutoff was
independently reconstructed from the defining arithmetic source at 80 decimal
digits. This is numerical evidence against a sufficient proof candidate,
not a Lean premise, a formal counterexample, or a refutation of RH.

The frozen question and all quantifiers are in
[the source-attack card](../../../1-in-progress/ccm-fu-binary-gcd-compensation.md).
For each odd r, the tested packet is `J_r(M)=G_r(M)+G_(2r)(M)`, with no fitted
weight. Squarefree Möbius support makes these packets cover the complete
off-diagonal. The test checked their sum against the saved total at every
cutoff. The tolerance was fixed at `1e-12*max(1,abs(total_off_diagonal))`.

## Source-level failure and surviving compensation

At M=11, r=1, the independent reconstruction gives

| Quantity | Value, rounded for display |
|---|---:|
| G_1 | 0.062515966695204023 |
| G_2 | -0.058677200689993545 |
| J_1 | **0.003838766005210478** |
| J_3=G_3 | -0.051598680421799809 |
| J_5=G_5 | -0.006833600136025165 |
| Complete off-diagonal | **-0.054593514552614496** |

Thus even the complete smallest-prime packet does not have its own
nonpositive sign. Distinct odd gcd classes supply the compensation.
The exact source at this witness still satisfies the original diagonal
ceiling. Its strict negative complete cross sum is already formal in
`sum_mobiusDivisorGcdCross_eleven_lt_neg_oneHundredth`; that existing theorem
was not rebuilt or axiom-audited again.

The paired odd cofactors give an exact paper explanation. Put
`V_d=C_d(11)+C_(2d)(11)` for d=1,3,5,7, with channels beyond eleven zero.
These four odd indices are pairwise coprime. Therefore

`J_1=2*sum_(d<e) V_d*V_e+2*C_1*C_2`,

`sum_r G_r=2*sum_(d<e) V_d*V_e+2*(C_1*C_2+C_3*C_6+C_5*C_10)`.

The complete first-pair reserve includes the latter two negative terms;
the primitive binary packet does not. This identifies the actual source
terms that must be compared jointly. The displayed paper decomposition and
the positive binary-packet sign have not been newly formalized. The broader
source route is not retired, and no replacement weights or larger packet
family were tested.

## Reproduction and provenance

- Input: every row of [the saved component table](../ccm-fu-gcd-cross-sign-2026-09-06/components.csv).
- [Exact script](screen.py); [all packets, failures and independent audit](summary.json).
- Execution: prescribed RunPod SSH host, Python 3.8.10, eight cutoff workers,
  one-thread BLAS environment and 60-second foreground deadline.
- Measured runtime, including independent reconstruction: 0.0343 seconds.
- No source channels were regenerated for the initial test. Only the first
  failing cutoff was reconstructed, using defining logarithmic-factorial,
  divisor, Möbius and Abel sums rather than the saved unit-clock table.
- Input and script hashes match the recorded hashes. Downloaded result hash
  matches the remote result. [SHA256SUMS](SHA256SUMS) records all three.
- Remote task files and directory were removed after download verification.
  The foreground job and its worker pool exited normally.

The pipeline computation directory holds evidence, not a mathematical proof
of the tested sign. No new Lean code, axioms, audits or builds were run for
this diagnostic.
