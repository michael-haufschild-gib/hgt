# CCM-FU: complete binary gcd compensation

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], direct signed-source proof candidate.
- **Goal:** Complete signed Abel bound, CCM-FU boundary chain, RH.
- **Parent:** [complete reserve-extension attack](ccm-fu-reserve-extension-induction.md).

Write `G_r(M)` for the exact ordered off-diagonal contribution of channel
pairs with gcd r. The corpus proves
`sum_r G_r(M)=S(M)^2-Q_empty(M)`, while individual components can be positive.
The complete coprime-column cancellation theorem suggests retaining a whole
prime-incidence packet before taking a sign or absolute value. Its floor
weights cannot simply be replaced by the divisor Abel weights: that would
discard the actual source dependence.

This attempt tests the concrete binary packet

`J_r(M)=G_r(M)+G_(2r)(M)`, for positive odd r.

The frozen sufficient claim is `J_r(M)<=0` at every cutoff and every positive
odd r. Every nonzero gcd component has squarefree gcd, because a repeated
prime in the gcd makes both Möbius coefficients zero. Thus grouping by odd
part gives the complete off-diagonal as `sum_(r odd) J_r(M)`. If the proposed
sign is true, it gives SD1 directly, followed by the already proved quadratic
diagonal ceiling and the full CCM-FU RH receiver. This candidate does not
assume a safe prime-elimination order or omit the terminal source square.

The choice of 2 fixes the smallest-prime incidence pair, without fitted
weights. The known positive primitive component at cutoff eleven does not
decide the sign of its complete binary packet. No claim that this packet
sign follows from unsigned positivity is made.

## Frozen discriminating test

Use every saved gcd component at every cutoff 1 through 100 in
`2-fully-proven/computations/ccm-fu-gcd-cross-sign-2026-09-06/components.csv`.
Do not regenerate those channels or extend the cutoff range. Check every
odd r<=M, interpreting G_(2r)=0 outside the cutoff. Use tolerance
`1e-12*max(1,abs(total_off_diagonal))`, retain every failure and every packet,
and check that their complete sum reconstructs the saved off-diagonal.

Independently reconstruct the first failing cutoff from the defining
logarithmic factorial, divisor sum, Möbius coefficients and Abel weights at
80 decimal digits. Retain every component and channel there. A failed
packet refutes this sufficient proof candidate at the numerical-evidence
level; it does not refute SD1, the complete reserve-extension claim, or RH.
A pass leaves the universal arithmetic packet sign to prove.

Execute only on RunPod, with at most eight cutoff workers and a 60-second
foreground deadline. Download the exact script, input hash, output and
interpretation. No numerical value becomes a Lean premise. Do not change
packet weights, add more primes or enlarge the screen after seeing its result.

## Current outcome and positive survivor

The [completed diagnostic](../2-fully-proven/computations/ccm-fu-binary-gcd-compensation-2026-09-07/README.md)
finds 59 positive packets among all 2,550. At the first, M=11 and r=1,
independent 80-digit source reconstruction gives
`J_1=0.0038387660052104776300...>0`, while the complete cross sum is
`-0.0545935145526144963903...<0`. The proposed universal packet sign is
therefore rejected at the numerical-evidence level. No formal negative
theorem or route retirement is claimed.

The positive survivor is the complete source compensation: at this witness,
the negative gcd-three and gcd-five terms pay the residual positive binary
packet. The full strict diagonal ceiling is already formal as
`sum_mobiusDivisorGcdCross_eleven_lt_neg_oneHundredth`. It was not re-audited.

A second algebraic pass identifies the exact omitted reserve. With the four
paired odd cofactors `V_d=C_d+C_(2d)`, d=1,3,5,7, write
`H=2*sum_(d<e) V_d*V_e`. Pairwise coprimality of these four indices gives
`J_1=H+2*C_1*C_2`, whereas the complete cross sum is
`H+2*(C_1*C_2+C_3*C_6+C_5*C_10)`. These paper identities retain the actual
source. They show why the complete first-prime reserve cannot be assigned
only to its primitive gcd packet. The new packet positivity and this exact
paired decomposition are not Lean certificates; the already formal complete
source ceiling is the audited surviving positive statement.

This attempt does not establish a sharper full signed bound. Its next
arithmetic obligation is a joint comparison using all released pair terms,
rather than another claim that each fixed gcd packet has a separate sign.
