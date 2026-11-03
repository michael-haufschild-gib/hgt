# Complete Weil energy as a limit of actual core Krein squares

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/WindowWeilCorePackets.lean`.
- **Statement:** Existing CWS zero coordinates, realized in the actual PM core basis, identify the complete signed form and its correct reflection.

## Finite and limiting identities

Let `s♯=1/2−conjugate(s)`, `b_s=mayerPeriodBasis s`, and let `P(S)=S∪S♯` for a finite set of upper Mayer resonances. For a real window test `H`, define

`v_S(H)=Σ_(s∈P(S)) X_H(2s)b_s`,
`X_H(2s)=windowZeroMap(H)(2s)=√m_(2s) Φ_H(s,1)`.

These are finite sums of actual boundary-subtracted scattering cores. Their existing PM Krein form satisfies

`[v_S(H),v_S(H)]_PM = Σ_(s∈P(S)) Wsummand(H,H,2s)`.

As finite `S` exhaust all upper resonances,

`2 Re [v_S(H),v_S(H)]_PM → Q(H)`.

No new Hilbert completion or metric is introduced. This identifies the complete signed Weil form through the actual PM core space, without a positivity assumption.

## Reflection and Hecke

On the existing core coordinates,

`repr(v_S(σ_AH))(s)=exp(−A(2s−1/2)) conjugate(repr(Θ_PM v_S(H))(s))`.

For the expanded-window pull `F₂H(u)=√2H(u+log2)`,

`repr(v_S(F₂H))(s)=2·2^(−2s) repr(v_S(H))(s)`.

The latter multiplier comes from the [actual completed-period Hecke equation](f2-hecke-window-mellin-correspondence.md). It is coefficient transport, not an assertion that raw four-branch Hecke acts diagonally on the boundary-subtracted cores; the [nonzero core correction](f2-hecke-scattering-boundary-correction.md) remains intact.

## Proof

The map `s↦2s` injects upper resonances into the actual zeta carrier and respects Riemann–Mayer reflection. Basis coordinates of the finite sum vanish outside `P(S)`. The PM reflection pairs each coordinate with its reflected coordinate; equality of multiplicities and the square-root identity give the Weil summand exactly.

The zeta carrier is the disjoint union of upper zeros and their conjugates: there are no real nontrivial zeros. Real-test Weil summands are conjugated by this bijection. Thus the complete real sum is twice the real part of the upper sum. Existing absolute summability and cofinality of `S↦P(S)` give the asserted limit.

Reflection and Hecke identities follow from the audited Mellin identities at `a=1`, including multiplicity and the exact finite-set reflection closure.

## Lean audit

- `windowZeroMap_upperMayerZero`
- `mayerKreinForm_windowWeilCorePacket`
- `repr_windowWeilCorePacket_reflection`
- `repr_windowWeilCorePacket_hecke`
- `weilQuad_eq_twice_upperMayer_sum`
- `tendsto_mayerKreinForm_windowWeilCorePacket`

Final individual check passed without warnings. All five printed endpoint audits use only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.

## Open sign

Neither finite Krein squares nor their limit are proved nonnegative. The remaining task is an arithmetic lower bound or positive source realization compatible with this exact signed correspondence.
