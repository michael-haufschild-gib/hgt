# Gcd parity charge and the location of cancellation capacity

Numerical diagnostic only. No interval certificate, Lean premise, or
unconditional RH proof is supplied by this directory.

## Frozen question

For actual gcd crosses G_r and diagonal D, let L=sum G=S^2-D and
J=sum mu(r)|G_r|. Prime-adjacent nonzero groups have opposite Möbius
parities. Removing equal mass from opposite-sign neighbors therefore
preserves J. The two invariant classes have net masses (L+J)/2 and
(L-J)/2; any one-prime flow leaves positive mass at least
U_colour=max((L+J)/2,0)+max((L-J)/2,0).

The proposed prime-flow remainder U<=D requires S^2+|J|<=3D. This
diagnostic tests that new obstruction and compares U_colour with the
already-computed prime-flow remainder. It does not extend the max-flow
screen or infer uniform success from finite data.

[Research card, derivation and proof gap](../../../1-in-progress/ccm-fu-one-prime-gcd-compensation.md).
`frozen-protocol.md` records the protocol uploaded before execution.

## Result

All 165 saved cutoffs were processed: M=101,...,256 and powers of two
512,...,131072. Both class balances are negative at every tested cutoff,
so U_colour=0. The greatest (S^2+|J|)/D is approximately 0.9544291021
at M=223. The frozen necessary bound has no observed failure.

The independent 80-digit audit at M=223 gives:

| Quantity | Value, approximately |
|---|---:|
| D | 59.9946697975656108684 |
| S^2 | 4.4211971878550281696 |
| J | 52.8394616364315009240 |
| Positive-parity-sign class balance | -1.3670054866395408874 |
| Negative-parity-sign class balance | -54.2064671230710418114 |
| U_colour | 0 |
| Previously audited one-prime U | 15.0720088277191103002 |

Negative mass is sufficient within each class, but the prime graph
prevents access to enough of it from the deficient set {6,10}. Its
positive residual is therefore caused by restricted neighborhoods.
Parity balance and source non-isolation alone do not control that loss.
The global class signs themselves remain unproved at general cutoffs.

## Execution and checks

- All mathematical computation ran on the supplied RunPod.
- Reused all saved C/G/Möbius arrays and the 161 existing flow outputs.
  No new source screen or max-flow solve.
- Four-worker long-double screen, one BLAS thread, 60-second deadline;
  elapsed 0.04899 seconds.
- At every cutoff: squarefree support, full signed reconstruction,
  direct class sums versus (L±J)/2, and lower-bound comparison with
  every available existing prime-flow residual.
- Predetermined audit selection chose M=223. The copied independent
  source-audit implementation reconstructs the literal log-factorial,
  divisor sums, original time-sum channels and every channel pair at
  80 digits. Four workers, 90-second deadline; elapsed 0.04075 seconds.
- Charge audit factors each group label directly and evaluates the new
  invariant from the audited groups; elapsed 0.00215 seconds. Screen
  ratio discrepancy below 8.7e-19. These are precision comparisons,
  not rigorous interval enclosures.
- All 499 remote source/result/input file hashes verified locally.
  Owned remote directory and local transfer archives removed after
  verifying no owned experiment process remained. No Lean process ran.

`summary.json` retains all cutoffs, L/J/class masses, necessary ratios,
existing flow remainders, local gaps and input hashes. `audit.json`
contains the independently reconstructed source. `charge_audit.json`
contains the 80-digit invariant. Original inputs, existing flow records,
scripts and pre-execution protocol are retained. `SHA256SUMS` covers all
499 remote files; this README was added locally afterward.
