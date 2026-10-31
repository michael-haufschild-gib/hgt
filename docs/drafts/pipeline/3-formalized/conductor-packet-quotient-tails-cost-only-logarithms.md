# Conductor packet quotient tails cost only logarithms

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md);
  [Gram plateau](harmonic-gram-remainders-have-a-logarithmic-plateau.md).

Put `F(n)=sum_(m≤Q)a_m u_m(n)`, `M=sum a_m²`, and
`L_Q=6log Q+log4+5`. For `Q≥2`, `N≥1`, and real `T≥1`,

`sum_(n≤N, N/n<T) F(n)²/n ≤[1+log(2T)+2L_Q]M`.

The Gram expansions at `N` and `floor(N/T)` have the same torsion term,
which cancels on subtraction. Their remainders cost at most `2L_Q M`.
The remaining harmonic interval has mass at most `1+log(2T)`.

Consequently, if `|r(n)|≤B` on the full horizon and `|r(n)|≤A` where
`N/n≥T`, then

`sum_(n≤N)r(n)²F(n)²/n`
`≤{A²[log N+17(1+log Q)]+B²[1+log(2T)+16(1+log Q)]}M`.

The actual Mertens remainder is bounded and tends to zero. Consequently,
for every `epsilon>0`, eventually in `N`,
uniformly over `Q≥2` and every packet,

`sum_(n≤N)[A(floor(N/n))−log(N/n)+gamma]² F(n)²/(n log N)`
`≤[epsilon+2048(1+log Q)/log N]M`.

This controls the scalar part of the full prime-row residual in
norm on every subpower conductor range. The conductor-changing correction
and the complete Weil residual still need their own norm estimates.

## Lean

`SuccessorShellArithmetic.Conductor.HarmonicPacketQuotientTails` proves
`harmonicConductorPacket_le_log`, `harmonicConductorPacket_interval_le`,
`harmonicConductorPacket_quotient_tail_le`, `sum_sq_packet_le_quotient_tail`,
and `eventually_primeRowScalarError_packet_sq_le`.
Direct production audit passed. All five dependency closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
