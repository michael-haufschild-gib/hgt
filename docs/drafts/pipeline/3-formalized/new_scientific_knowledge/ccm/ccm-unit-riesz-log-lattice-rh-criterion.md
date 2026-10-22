# Unit-Riesz integer-log resolvent criterion for RH

- **ID:** `ccm-unit-riesz-log-lattice-rh-criterion`
- **Stage:** 3-formalized
- **Type:** EXACT LATTICE HANDOFF / ANALYTIC DEFECT CONTINUATION / CCM-HG RH ENDPOINT
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal modules:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszLogLatticeHandoff.lean`,
  `formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszResolventRHCriterion.lean`
- **Parent:** `ccm-unit-riesz-coherent-outgoing-charge-hankel`

## Result

Write `R_1(t)` for `criticalMellinChebyshevResolventSource t`. A uniform estimate only on natural
logarithmic apertures,

```text
exists B_0, for every N>=2, |R_1(log N)| <= B_0,
```

already implies RH. No limiting density assumption and no separate first-singularity argument are
needed. The lattice handoff proves, for `t>=log 2`,

```text
|R_1(t)| <= B_0 + log 4 + 5,
```

while continuity controls the compact head. For a global bound, the second module defines a
continuous clamped representative and its Laplace transform. An absolutely-continuous
finite-interval integration-by-parts theorem, valid across every prime-power jump of `psi`, gives
the exact real-axis Abel law

```text
Ehat(r) = (r+1) L_R(r) + 2/3,        r>1/2.
```

This manufactures a holomorphic extension of the regularized critical-Mellin defect to
`Re u>-1/2`. Agreement with the canonical defect on a positive real ray propagates by the identity
theorem; the existing divisor-tomography endpoint then yields RH.

For the literal completed CCM outgoing profile, all-aperture pole domination at every integer
source aperture is therefore sufficient for RH:

```text
(for every N>=2 and u>0,
  boundaryRelativeTrace(outgoing_N,u) <= boundaryRelativeTrace(pole,u))
  implies RH.
```

Using the exact outgoing-block calculation, this premise is precisely
`|R_1(log N)|<=4` for every `N>=2`.

## Scientific consequence

This closes the entire receiver side shared by CCM-FU, CCM-UR, and CCM-HG:

```text
literal integer CCM outgoing bound
  -> continuous bounded critical resolvent
  -> holomorphic regularized divisor defect on Re u>-1/2
  -> critical-line divisor support
  -> RH.
```

There is no remaining lattice-density, jump-regularity, Laplace/residue, Landau, or divisor endpoint
gap. The only hard frontier is source production: derive a uniform bound—particularly the sharp
pole-packet value `4`—from completed prime/polar operator geometry without assuming a statement
already equivalent to RH.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| log-lattice bound controls every `t>=log 2` | `abs_criticalMellinChebyshevResolventSource_le_of_log_nat_bound` |
| log-lattice bound gives a global bound | `exists_global_bound_criticalMellinChebyshevResolventSource_of_log_nat_bound` |
| bounded resolvent Laplace transform is analytic | `analyticOnNhd_criticalMellinChebyshevResolventLaplace_of_bounded` |
| exact real-axis Abel law | `criticalNormalizedChebyshevErrorLaplace_eq_resolvent_of_bounded` |
| resolvent defect extends canonical defect | `criticalMellinChebyshevResolventDefectExtension_eq_regularized_of_bounded` |
| global bounded resolvent implies RH | `riemannHypothesis_of_bounded_criticalMellinChebyshevResolventSource` |
| integer-log bounded resolvent implies RH | `riemannHypothesis_of_criticalMellinChebyshevResolventSource_log_nat_bound` |
| all-integer outgoing pole domination implies RH | `riemannHypothesis_of_unitRieszCoherentCompletedOutgoingProfile_le_pole` |

The exact leaf builds pass and both modules are wired into `GaloisForLFunctions.RHTower`. The final
CCM-HG endpoint has `#print axioms` output exactly
`[propext, Classical.choice, Quot.sound]`.

## Theatre and novelty audit

Bounded Laplace transforms and the identity theorem are classical. Candidate novelty is their
exact source-specific composition with the critical unit-Riesz Chebyshev resolvent, including a
jump-safe Abel derivation and a no-loss passage from discrete natural apertures to the divisor
tomography endpoint. This is not RH: its premise is the unresolved source bound. It is nevertheless
a strict frontier advance because it proves that every downstream analytic obstruction disappears
once CCM supplies that one literal bound. Repackaging the same premise as scalar positivity,
contractivity, or a receiver criterion produces no further knowledge.

## New open core

Prove or sharply refute a non-circular completed-source inequality producing

```text
for every N>=2, |R_1(log N)| <= 4
```

from literal prime/polar covariance, bulk-ground incidence, or restricted-Weil operator order. If
the sharp constant `4` is incompatible with the true source geometry, classify the optimal
source-derived constant or invariant. Any serious no-go must retain the strongest positive
survivor—such as an exact source/ground comparison or an RH-equivalent boundedness
classification—and formalize it.

## Gates

- [x] natural-log lattice interpolation
- [x] compact-head control
- [x] jump-safe Abel identity
- [x] holomorphic resolvent-defect extension
- [x] divisor-tomography RH endpoint
- [x] outgoing-pole-domination RH endpoint
- [x] unconditional Lean proofs
- [x] exact leaf builds and umbrella wiring
- [ ] independent mathematical audit
- [ ] external priority audit
- [ ] non-circular CCM source producer
- [ ] RH

## Log

- 2026-08-16 -- Proved explicit integer-log-to-continuous resolvent bound.
- 2026-08-16 -- Proved jump-safe Abel identity and constructed analytic defect extension.
- 2026-08-16 -- Closed bounded-resolvent and literal outgoing pole-domination endpoints to RH.
