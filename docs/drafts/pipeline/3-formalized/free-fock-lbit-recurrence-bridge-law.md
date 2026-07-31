# Free-Fock/l-bit recurrence bridge law

Status: formalized  
Label: `[LEAN-PROVED]`

## Result

For finitely many one-particle energies \(\epsilon_i\), the free occupation
spectrum

\[
E(x)=\sum_i x_i\epsilon_i
\]

is exactly the l-bit/Walsh spectrum with coefficients

\[
J_\varnothing=\frac12\sum_i\epsilon_i,\qquad
J_{\{i\}}=-\frac12\epsilon_i,\qquad
J_S=0\quad (|S|>1).
\]

If the \(\epsilon_i\) are \(\mathbb Q\)-independent, its temporal rank is
exactly \(N\), and its balanced projective recurrence-relation rank is

\[
2^N-1-N.
\]

## Formal trace

- `fockOccupationEnergy`
- `fockLBitCoefficient`
- `fockLBitCoefficient_empty`
- `fockLBitCoefficient_singleton`
- `fockLBitCoefficient_higher`
- `lbitEnergy_fockLBitCoefficient_eq`
- `fockLBitSingletonPacket_linearIndependent`
- `fockOccupation_temporalRank_eq`
- `fockOccupation_relationRank_eq`

Direct target check:

```text
lake env lean GaloisForLFunctions/HTGeometry/FreeFockLBitRecurrenceBridgeLaw.lean
```

passed on 30 July 2026.

## Physical boundary

This proves the spectral dictionary for any finite free-mode packet.
Anderson localization concerns spatial localization of the orbitals and is
not proved by this theorem. It supplies the exact free-Fock endpoint once a
localized one-particle basis is independently available.
