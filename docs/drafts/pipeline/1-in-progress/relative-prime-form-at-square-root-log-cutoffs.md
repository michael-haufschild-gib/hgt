# Relative prime forms at square-root logarithmic cutoffs

- **ID:** critical-rigidity-relative-prime-form
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Question:** Does retaining adjunction energy enlarge the actual prime-form approximation regime from a cubic logarithmic residual cost to a quadratic one?

## Candidate mechanism

For normalized packets with the conductor-one coefficient removed, `M≤L/log 2`. The relative residual estimate would therefore give

`||R_a||²/log N ≤ C (1+log Q)² L/log N`.

Together with a uniform harmonic packet upper frame, Cauchy–Schwarz would bound the mixed residual against the packet by

`C (1+log Q)/sqrt(log N) · L`.

The diagonal adjunction pairing uses a harmonic Gram matrix, not the identity. Its error must also be bounded in `L`, with every conductor and horizon explicit. A two-sided harmonic frame estimate and polarization suggest a cost at most `C(1+log Q)²/log N · L`.

This would give relative approximation of the literal renormalized prime quadratic form whenever `(1+log Q)²=o(log N)`, and positivity below a sufficiently small square-root logarithmic cutoff. The full prime residual must retain the prescribed Euler constant and the actual finite prime matrix throughout the transfer.

## Scope and unresolved steps

- Check the exact residual/matrix sign and renormalization.
- Prove the uniform two-sided harmonic Gram error needed for weighted adjunction pairing.
- Establish the quantitative relative form statement with no new analytic input.
- Compare its growing-conductor range against existing corpus theorems.

## Existing receivers and sharper source projection

`CompletedArithmeticForms.PrimePacketCoercivity.exists_primePacket_energy_ge_log` requires `(1+log R)²/sqrt(log N)≤1`, besides its horizon conditions. Its public polarized Gram theorem has discrepancy `9(1+log Q)/log N` times the two coefficient norms. A new relative approximation must be compared with this actual theorem, not merely with an isolated residual estimate.

The coefficient-one projection can be replaced by the actual harmonic pole projection. If `v_m` are normalized horizon modes and `u=Σa_m v_m`, define `b_m=a_m` for `m≠1` and

`b_1=a_1−<u,v_1>/||v_1||²`.

Then `Σb_m v_m` is exactly pole-neutral, and adjunction energy is unchanged. The constant conductor is annihilated by the complete prime-dilation generator, so that generator is unchanged as well. The polarized Gram estimate should bound `Σb_m²` by a constant times adjunction energy whenever `9(1+log Q)/log N≤1/2`. This would retain the actual finite-horizon hyperplane in the relative residual theorem. These source and quantitative transfers still require Lean proofs.

This is a prime-form candidate. It does not establish positivity of the complete Weil form, control Gamma or shell coupling, or imply an RH improvement.
