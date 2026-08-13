# Mass-shifted vacuum-free nondegenerate source action

- **ID:** `mass-shifted-vacuum-free-nondegenerate-source-action`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3
- **Claim:** unit-vacuum subtraction inside adaptive two-amplitude `P^sharp` source preserves odd
  null-defect landing, pays admission effectivity, and has sharp fixed-degree `y^-2` recession.

## Conjecture / proof-or-failure loop

1. **Convex adjacent-edge entropy.** Failed: derivative carries uncontrolled edge amplitude.
2. **Gauge-centered full arcsine charge.** Failed: newborn Jacobi edge is independent and can make
   charge arbitrarily negative.
3. **Full nondegenerate null-flag completion.** Partly succeeds: pays current effectivity and
   preserves singular odd landing. Fails as normalized budget because unit channel forces density
   at least one.
4. **Post-aggregation vacuum subtraction.** Rejected: not source-first.
5. **Pre-aggregation unit subtraction.** Survives. Removed polynomial `P_n^2` has zero moment at
   null face, so odd landing remains exact; positive-chamber history loses only constant one.
6. **Qualitative recession.** Strengthened: exact coordinate weights prove sharp `y^-2` law with
   positive explicit coefficient.

## Paper theorem

For positive adjacent moment chamber and `n>0`, write

```text
H°_n = sum_(j<n) alpha_j^2 + 2 sum_(j<n) beta_j + 2 a_n^2 + alpha_n^2,
R_n  = -2 a_n + (2n+1) alpha_n,
K_n  = (2n+1)^2 + 2.
```

Then `H°_n >= 0`, `R_n^2 <= K_n H°_n`, and literal vacuum-free source satisfies

```text
S°_n = 2 N_n H°_n,
2 N_n R_n^2 <= K_n S°_n.
```

At every lifted null flag with first odd Padé defect `delta`, `L(P_n^2)=0`; hence unit
renormalization preserves exact source landing `A^sharp_circ = 2 delta`, independently of adjacent
amplitude.

Reciprocal-mass coordinate transport gives

```text
y^2 * S°_n(y)/(2 N_n(y)) -> C_n,
C_1 = 1,
C_n = (4n^2+3n+2)/8  for n>=2.
```

Across positive chamber `[a,b]`, actual integral action is

```text
(log N_n(b)-log N_n(a))^2
  <= (b-a) K_n integral_[a,b] S°_n(y)/(2N_n(y)) dy.
```

## Lean certificates

Modules:

- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionAdjacentEdgeArithmeticAction.lean`
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity.lean`
- `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionVacuumFreeSourceRecession.lean`

Capstones:

- `xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource_liftedNull_eq_two_mul_firstOddDefect`;
- `literal_unitRenormalizedAdaptiveMixedSource_pays_admissionEffectivity`;
- `tendsto_square_mul_unitRenormalizedSourceMass_div_norm`;
- `tendsto_fourth_mul_literal_unitRenormalizedAdaptiveMixedSource_div_norm`;
- `log_norm_sub_log_norm_sq_le_unitRenormalizedSource_action`;
- `hasDerivAt_log_adjacentEdge_and_literal_nondegenerateSource_action`.

## Honest scope

This is missing producer and fixed-degree action, not RH proof. Exact leading coefficient grows
quadratically with degree. Remaining open core is degree-proper common budget preventing cofinal
frontier events from escaping through `n -> infinity`. Any summable degree weighting can absorb a
uniform event floor and therefore cannot close route without a compensating degree-growth law.

## Verification

- direct `lake env lean` checks: PASS;
- targeted module build: PASS;
- formal lint: new modules reachable and clean; repository gate fails on unrelated concurrent
  unreachable Maynard/Sieve, Deninger, and Suzuki modules;
- capstone axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computation.

## Novelty

Route-specific claim is `[NOVELTY UNVERIFIED]`. Classical Hankel/Toda/Jacobi literature supplies
coordinate transport and sum-rule analogues, but no audited result identifies this source-first
vacuum-free adaptive rational--Gamma/von-Mangoldt producer or preserved odd-to-even null landing.
