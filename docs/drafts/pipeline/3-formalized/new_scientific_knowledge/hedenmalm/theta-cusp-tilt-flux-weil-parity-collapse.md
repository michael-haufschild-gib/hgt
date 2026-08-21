# Theta tilt flux is the two-channel Weil parity-energy deficit

Status: Lean-formalized, unconditional three-route synthesis. `[CORPUS-NEW SYNTHESIS]`. Does not
prove RH.

## Exact identity

For a safe packet `Re(w_j) > a > 1/2`, rescale coefficients by

```text
d_j = c_j * xiCent(w_j).
```

Let `A_d` and `B_d` be the canonical even and odd rational-resolvent channel packets on the
multiplicity-exact centered Xi divisor. Split each packet by critical-line reflection into its
reflection-even and reflection-odd parts, and write `E(F)` and `O(F)` for their squared divisor
evaluation energies. Lean proves

```text
eulerSafeDeficit(a,d,w)
  = π * (Weil(A_d,A_d) + Weil(B_d,B_d)),

Re(eulerSafeDeficit(a,d,w))
  = π * (E(A_d) + E(B_d) - O(A_d) - O(B_d)),

d/da|_{a=0} tiltCorrelation(thetaCuspTiltSource,c,w)
  = E(A_d) + E(B_d) - O(A_d) - O(B_d).
```

No zero-location assumption enters these identities. The Weil form is correctly treated as a
Krein polarization: calling its two summands “Gram kernels” does not make them positive.

## Higher universal principle

Three formerly separate frontier obstructions are one law in different coordinates:

```text
theta neutral tilt production
  = Euler-safe observability after de-Poissonization
  = reflection-even channel energy - reflection-odd channel energy.
```

Safe half-plane positivity constructs the positive `J`-metric. The missing RH implication is not
positivity of that ambient metric; it is contractivity of reflection-odd projection on the linked
two-channel packet span. Lean proves the exact endpoint

```text
RH ↔ ∀ linked packets,
  O(A_d) + O(B_d) ≤ E(A_d) + E(B_d).
```

This explains why scalar source shape, one-node currents, generic Carathéodory kernels, and an
unqualified “Weil Gram” interpretation stall: they see the ambient positive metric but not the
linked-channel reflection incidence.

Lean now also proves the sharp rank-one boundary unconditionally:

```text
Re(w) > 1/2
  ⇒ Re criticalLogDerivKernel(w,w) ≥ 0
  ⇒ O(A_c) + O(B_c) ≤ E(A_c) + E(B_c)
     for the canonical one-node linked packet.
```

The first implication transports the scalar theta-source current through the nonzero factor
`|xiCent(w)|²`; the second uses the exact Euler/parity weld. Therefore diagonal energy cannot be
the RH obstruction. Any negative packet must involve at least two modes and nontrivial
off-diagonal interference.

## Positive survivor and next conjecture

The source-facing survivor is now a concrete contraction problem. Construct, from literal
theta/Euler incidence, an operator on the canonical linked channel-packet closure whose output is
the pair of reflection-odd divisor evaluations, whose input is the pair of reflection-even
evaluations, and whose norm is at most one. Equivalently, produce a source-level sum-of-squares or
Schur complement proving the displayed energy domination without importing a zero-location
statement.

Any next route must preserve all three structures simultaneously:

- coefficient linkage between `A_d` and `B_d`;
- critical-line reflection pairing on the actual divisor;
- literal theta/Euler source realization of the coefficients.

Dropping any one returns to an obstruction already formalized in the corpus.

## Lean source

`formal/GaloisForLFunctions/RHTower/ThetaCuspTiltFluxWeilParityWeld.lean`

Closed declarations:

```text
xiWeilEvenEnergy
xiWeilOddEnergy
xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
xiWeilSquareSummable_channelPacketA
xiWeilSquareSummable_channelPacketB
eulerSafeDeficit_eq_pi_mul_twoChannelWeil
eulerSafeDeficit_re_eq_pi_mul_twoChannelParityDeficit
tiltCorrelation_thetaCuspTiltSource_deriv_eq_twoChannelParityDeficit
riemannHypothesis_iff_twoChannelParityEnergy_domination
criticalLogDerivKernel_self_re_nonneg_of_half_lt
oneMode_twoChannelParityEnergy_domination
```

Verification:

- direct source check passed with `lake env lean`;
- exact target build passed with
  `lake build GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityWeld`;
- no umbrella/full build was run;
- all nine theorem `#print axioms` reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`;
- module is wired into `RHTower.lean`.

## Log

- 2026-08-21 — TTF, Euler-safe observability, and two-channel Weil/Krein routes welded into one
  exact parity-energy deficit; final obstruction recast as source-specific odd-projection
  contractivity.
- 2026-08-21 — Proved unconditional diagonal critical-kernel positivity and one-mode linked
  parity contraction; localized every possible obstruction to genuine cross-mode interference.
