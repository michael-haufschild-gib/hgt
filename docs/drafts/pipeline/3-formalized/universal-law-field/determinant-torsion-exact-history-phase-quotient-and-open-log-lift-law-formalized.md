# Determinant torsion, exact history, phase quotient, open log lift — Lean certification

- **ID:** ULF-TORS-1
- **Paper card:**
  `determinant-torsion-exact-history-phase-quotient-and-open-log-lift-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

### The based complex and its determinant history

`torsionDifferential u : k →ₗ[k] k` is the differential `d_u(e₁) = u e₀` of `C(u)`.
`torsionDifferential_eq_smul` identifies it with `u • id`, so `det_torsionDifferential` proves

`det d_u = u`:

the comparison scalar is not a label but the determinant of the differential.

### Theorem 2.1 — homology forgets a multiplicative history field

- `torsionDifferential_ker` and `torsionDifferential_range` — `C(u)` is acyclic in both degrees for
  every `u ≠ 0`;
- `homology_indistinguishable` — all nonzero comparison scalars give literally the same kernel and
  the same image, so the homological observer collapses the whole `kˣ`-family;
- `sumDifferential` is the differential of a finite orthogonal sum, `sumDifferential_apply` shows it
  acts blockwise, and `det_sumDifferential` proves `det = ∏ u_j`: the determinant history is
  multiplicative under direct sums;
- `BasedChainIso` is a chain isomorphism whose two components fix the declared basis vectors;
  `linearEquiv_eq_id_of_base` shows such a component is the identity, and
  `basedChainIso_nonempty_iff` proves `Nonempty (BasedChainIso u v) ↔ u = v`.  The determinant
  history is therefore a complete based invariant.

`exists_unbased_chainIso` certifies the card's fatal boundary 1: dropping the basing and allowing
independent automorphisms in the two degrees produces a chain isomorphism between *any* two nonzero
scalars, so the invariant disappears and the source marking is load-bearing.

### Corollary 2.2 — positive scalarization is a phase quotient

`positiveShadow u = normSq u`, positive for `u ≠ 0` (`positiveShadow_pos`), and constantly one on
unitary histories (`positiveShadow_exp`).  `positiveShadow_eq_iff_phase` proves that two histories
with `u ≠ 0` share a positive shadow *if and only if* they differ by a `U(1)` phase — the shadow is
exactly the quotient of `ℂˣ` by its phase action, no more and no less.

### Theorem 2.3 — closed exact observation, open lifted history

For `u_N(t) = exp(2πiNt)` (`loopHistory`, with `logLift` its chosen logarithm and `exp_logLift`
their relation):

- `loopHistory_ne_zero` — every member of the family is acyclic, so the homological observation is
  constantly zero;
- `positiveShadow_loopHistory` — the positive shadow is constantly one;
- `loopHistory_zero`, `loopHistory_one` — the determinant history is a closed loop;
- `logLift_endpoint`, `logLift_ne_of_ne_zero` — the logarithmic lift is open, with endpoint
  increment exactly `2πiN`, nonzero for `N ≠ 0`;
- `hasDerivAt_loopHistory`, `loopLogDerivative`, `winding_integral`, `winding_number_eq` — the
  logarithmic-derivative integrand is the constant `2πiN`, and `(2πi)⁻¹ ∫₀¹ u⁻¹ u̇ = N`.

`closed_observation_open_lift` bundles all seven conclusions in one unconditional theorem.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveDeterminantTorsion.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on the based-invariant criterion, the direct
sum determinant, the determinant identification, homological indistinguishability, the gauge
collapse, the phase-quotient criterion, and the closed/open capstone reports only `propext`,
`Classical.choice`, and `Quot.sound` (the based-invariant criterion needs only `propext` and
`Quot.sound`).  No project axiom, placeholder, hypothesis interface, or unresolved theorem premise
is used.

## Exact field consequence

Exactification erases the path by which a law became exact.  Zero homology, a positive scalar
return, and a closed determinant return are jointly compatible with a lifted law history that does
not close: the surviving datum is a determinant-line comparison against a declared source basis,
and its logarithmic winding is a genuine invariant of the history rather than of the endpoint.
