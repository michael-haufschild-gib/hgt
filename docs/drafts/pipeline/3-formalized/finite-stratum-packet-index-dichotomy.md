# The finite stratum is the packet-index dichotomy

- **ID:** A110
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The supremum of the negative indices of the comb defect on finite real
  compactly supported smooth packet families equals the number of distinct zeta zeros right
  of the critical line. Consequently, `FiniteOffLine → RH` iff this index is zero or infinite.

## Proof

Split each complex test into its real and imaginary parts. Its Gram matrix is a compression
of the Gram matrix of the resulting real family, so its negative index cannot increase.
Thus real packets attain the full Pontryagin index, which counts distinct right-hand zeros.
The real-packet upper bound gives equality. Finiteness of the right-hand zero set is equivalent
to `FiniteOffLine`, and emptiness is equivalent to RH. Splitting into finite and infinite sets
now gives both directions of the dichotomy.

## Lean

Module: `ArithmeticCastelnuovoSeveri/TheFiniteStratumIsThePacketIndexDichotomy.lean`.

- `exists_real_packets_negIndex_ge`
- `realPacketNegIndex_eq_rightZeros`
- `finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite`

Direct `lake --old env lean` check passed. Transitive axioms: `propext`, `Classical.choice`,
`Quot.sound`. Wired into `ArithmeticCastelnuovoSeveri.lean`; umbrella not compiled.
