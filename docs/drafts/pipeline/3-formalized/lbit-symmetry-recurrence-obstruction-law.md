# L-bit symmetry recurrence obstruction

- **ID:** `lbit-symmetry-recurrence-obstruction-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Date:** 2026-07-31
- **Formal source:** `formal/GaloisForLFunctions/HTGeometry/LBitSymmetryRecurrenceObstructionLaw.lean`

## Exact law

A finite l-bit Hamiltonian has maximal recurrence dimension exactly when its
complete nonempty-support coefficient packet is rationally linearly
independent:
\[
  \boxed{
  \tau(J)=2^{|I|}-1
  \iff
  (J_S)_{\varnothing\ne S\subseteq I}
  \text{ is linearly independent over }\mathbb Q.}
\]

Consequently, one equality \(J_S=J_T\) between distinct nonempty supports
forces
\[
  \tau(J)<2^{|I|}-1.
\]
If a nontrivial site permutation preserves every coefficient, any moved
nonempty support, in particular a moved singleton, supplies such a
collision.

Thus exact permutation symmetry obstructs maximal recurrence rank in the
commuting l-bit class. The full-rank infinite quasi-local construction must
be inhomogeneous; its disorder is structural rather than cosmetic.

## Formal declarations

- `lbitTemporalRank_le_maximal`;
- `lbitTemporalRank_eq_maximal_iff_linearIndependent`;
- `lbitTemporalRank_lt_maximal_of_coefficient_collision`;
- `lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSupport`;
- `lbitTemporalRank_lt_maximal_of_permutation_symmetry`;
- `lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSite`.

## Scope

The result proves strict loss from one exact coefficient collision. It does
not give a sharp rank formula for every translation-invariant model or
assert that all forms of physical symmetry prevent large recurrence rank.

## Verification

Direct target compilation passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/LBitSymmetryRecurrenceObstructionLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/LBitSymmetryRecurrenceObstructionLaw.olean
```

Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Final `lake build` audit is reserved for publication audit.
