# Zero-Fed Uvarov Repair Tautology

- **ID:** zero-fed-uvarov-repair-tautology
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `rh-landscape-proof-gate.md`, `no-boundary-selection-of-zeta.md`,
  `finite-rank-one-selector-no-free-lunch.md`, and
  `docs/consolidated/revision01/big-picture.md`
- **Statement:** A rank-one Uvarov repair proves no source selection when the
  unrepaired form is defined by subtracting the same rank-one atom from the
  zero-fed repaired form. In that case the repair positivity is exactly the
  positivity of the original zero-fed form.

## Goal

Separate two statements that the boundary-Weyl language can blur:

1. a useful coordinate identity: `H^0_d = H^-_d + a_* v_* v_*^*`;
2. the missing theorem: source data force `H^0_d >= 0` for all `d`.

Only the second can carry RH content. The first is a change of coordinates unless
`H^-_d` is constructed before the zero-fed form `H^0_d`.

## Theorem

Let `V_d` be a finite-dimensional complex vector space, let `v_* in V_d` be
nonzero, let `a_*>0`, and let `H^0_d` be a Hermitian form. Define

`H^-_d = H^0_d - a_* v_* v_*^*`.

Then

`H^-_d + a_* v_* v_*^* >= 0`

is equivalent to

`H^0_d >= 0`.

If, moreover, `H^-_d` is invertible with inertia `(d,1)` and
`m_d = v_*^* (H^-_d)^{-1} v_* < 0`, then the finite Weyl scalar

`S_d = -1/a_* - m_d`

satisfies

`S_d > 0  <=>  H^0_d > 0`.

At `S_d=0`, `H^0_d` has a one-dimensional kernel; for `S_d<0`, the repaired form
still has one negative square.

## Proof

The first claim is the definition of `H^-_d`.

For the scalar statement, apply the rank-one Schur-complement theorem from
`finite-rank-one-selector-no-free-lunch.md` to

`H(t)=H^-_d+t v_*v_*^*`

at `t=a_*`. Since `H(a_*)=H^0_d`, the Schur scalar sign is exactly the positivity
side of `H^0_d`. This proves the theorem.

## Consequence for the RH Route

In the reciprocal seam chart, if one starts with the zero-divisor tower

`H^0_d = [T_{i+j+1}]`,

then defines

`H^-_d = H^0_d - a_* v_*v_*^*`

by removing the first Gamma-boundary atom, the statement that adding that atom
repairs `H^-_d` back to a positive form is just the statement `H^0_d >= 0`.
By the source-aware `Q_0` theorem, the all-degree version is RH.

Thus a Uvarov / Christoffel / Krein-Langer formulation is a faithful chart only
after the unrepaired object has been source-built independently. It becomes
non-mirror only if the proof constructs `H^-_d`, `v_*`, and `a_*` from
Euler/Gamma/functional-equation data without first forming `H^0_d` from zeros,
then proves the Schur sign from that source construction.

The useful source test is therefore:

`source-built H^-_d + Gamma atom => positive side`

not

`zero-fed H^0_d - Gamma atom + Gamma atom => H^0_d`.

## Source Boundary

The theorem is finite-dimensional linear algebra plus the previous rank-one
Schur-complement guardrail. It claims no new positivity for `xi`. Its purpose is
to prevent the first-trivial-zero Uvarov coordinate from being mistaken for the
landscape/self-selection theorem.

## Gates

- [x] 0 -> 1 in-progress: zero-fed Uvarov circularity isolated.
- [x] 1 -> 2 fully-proven: tautology and Schur scalar equivalence written.
- [x] 2 -> 3 formalized: `HTGeometry/ZeroFedUvarovRepairTautology.lean`
  proves the exact finite Hermitian rank-one identity, the PSD equivalence,
  positive Schur-scalar iff positive-definiteness, and the wall/negative-side
  inertia conclusions.

## Log

- 2026-06-24 -- Codex: created under the landscape-proof audit. Entropy draw was
  `extreme-cases`: the extreme case is the coordinate built from `H^0_d` itself.
  In that case the Gamma repair theorem collapses to `H^0_d >= 0`, hence to the
  existing all-order RH chart.

## 2026-06-24 finite-rank quotient audit

`finite-rank-counterterm-kernel-visibility.md` gives the general finite-rank version of the zero-fed repair warning. A rank-one or finite-rank repair proves source information only on the kernel of its boundary map. The quotient part can be a zero-fed cancellation unless the boundary map and quotient form are constructed from source data before the reciprocal divisor is used.

## 2026-06-24 non-atomic finite-rank quotient check

`non-atomic-finite-rank-counterterms-rh-strength.md` isolates the zero-feeding risk in finite-rank repairs. If the quotient boundary data are non-atomic on the reciprocal support, the repair cannot hide any off-line atom. If the quotient does see atom-isolators, the proof must explain how those atom evaluations were source-built before the divisor was used.

## 2026-08-15 Lean formalization

Formalized in
`formal/GaloisForLFunctions/HTGeometry/ZeroFedUvarovRepairTautology.lean`.
`zeroFedUvarovRepairTautology` proves the complete stated finite-dimensional
certificate without added hypotheses or axioms: the remove-and-restore identity,
PSD equivalence, the Schur-scalar/positive-definiteness equivalence, and the
zero/negative scalar inertia alternatives. The formal statement interprets
`inertia (d,1)` as positive index `d`, negative index `1`, and null index `0`;
this repairs the card's ambiguous dimension notation. The rank-one energy is
the real scalar whose complex coercion is the card's Hermitian resolvent
quadratic expression (`rankOneEnergy_coe`).

Validated with `lake env lean
GaloisForLFunctions/HTGeometry/ZeroFedUvarovRepairTautology.lean` and targeted
`lake build GaloisForLFunctions.HTGeometry.ZeroFedUvarovRepairTautology`.
`#print axioms` for the package theorem and its core identity reports only
`propext`, `Classical.choice`, and `Quot.sound`.
