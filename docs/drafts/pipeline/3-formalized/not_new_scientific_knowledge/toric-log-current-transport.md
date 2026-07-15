# Laurent monomials act linearly on toric logarithmic currents

- **ID:** toric-log-current-transport
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), BRIDGE
- **Source:** toric log-Calabi--Yau tail theorem
- **Statement:** In any characteristic-zero differential field, the logarithmic current of an
  arbitrary finite Laurent monomial is the integral linear combination of the coordinate
  logarithmic currents specified by its character-lattice exponent row.

## Goal

Formalize the exact source-pure transport identity by which a torus isogeny acts on the flat
log-cotangent frame of a toric boundary pair.

## Gates

- [x] 0 -> 1 in-progress: Laurent-monomial statement isolated
- [x] 1 -> 2 fully-proven: field-algebra proof complete, including negative exponents
- [x] 2 -> 3 formalized: scratch check, targeted build, and axiom audit pass
- [ ] 3 -> 4 publication-ready: supporting certificate for the full toric stable-tail theorem

## Lean certificate

File: `formal/GaloisForLFunctions/HTGeometry/ToricLogTail.lean`

Declarations:

- `toricLogCurrent`
- `toricLogCurrent_mul`
- `toricLogCurrent_zpow`
- `toricLogCurrent_laurentMonomial`

Targeted verification:

`lake build GaloisForLFunctions.HTGeometry.ToricLogTail`

All three theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical use

If a torus isogeny has character-lattice matrix `A=(a_ij)`, each pulled-back character is a
Laurent monomial and `toricLogCurrent_laurentMonomial` gives

`alpha*u_i=sum_j a_ij u_j`.

This is the formal transport core of the paper theorem identifying a pure expanding toric tail
with the differential field of the flat logarithmic boundary frame.  The stable-field equality
and toric compactification geometry remain paper-level and are not postulated as Lean axioms.

## RH impact audit

The identity supplies a precise test for a hypothetical toroidal RH factor: its logarithmic
currents must carry an integral character-lattice action.  It does not produce such a factor for
the completed-zeta source and has no direct implication for zeros or positivity.

## Log

- 2026-07-15 -- arbitrary Laurent-monomial transport formalized; targeted build and axiom audit
  passed.
