# Dyadic-prime Dirichlet high-line sign rigidity — Lean formalization

- **ID:** `dyadic-prime-dirichlet-high-line-sign-rigidity`
- **Stage:** `3-formalized`
- **Type:** `[BRIDGE] [NO-GO] [POSITIVE CLASSIFICATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `dyadic-prime-dirichlet-high-line-sign-rigidity.md`

## Generic module

`GaloisForLFunctions.HTGeometry.DirichletHalfPlaneSignRigidity` provides:

- `lseriesPowerTwistCoeff_abscissa_lt_top`;
- `tendsto_rpow_mul_im_lseriesPeeledPowerTwist`;
- `eventually_lseriesPeeledPowerTwist_im_pos` and `_im_neg`;
- `eventually_LSeriesSummable_sub_const`;
- `lseriesPeeledPowerTwist_im_eq_LSeries_sub`;
- `eventually_realLSeries_sub_im_pos` and `_im_neg`.
- `nat_cpow_quarterTurn_im_eq_one` and `_neg_quarterTurn_im_eq_neg_one`;
- `exists_opposite_imaginary_phase_of_ne_zero`;
- `realLSeriesRawImpedance_not_fixedSign_of_firstNonzero`.

The last two theorems formalize arbitrary-first-mode high-line sign rigidity for real ordinary
Dirichlet series, including construction of a phase for every nonzero first surviving real
coefficient.  No continuation or zero hypothesis occurs.

## Dyadic specialization

`GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPassiveNoGo` provides:

- `dyadicWeightedPrimeWindow_two` and `dyadicSharpPrimeSourceCoefficient_two`, proving the exact
  formulas `W(2) = log(2) / sqrt(2)` and
  `S(2) = 4 * (sqrt(2) - 1) - sqrt(2) * log(2)`;
- `dyadicSharpPrimeSourceComplexCoeff_two_pos`;
- `two_cpow_I_im_pos` and `two_cpow_neg_I_im_neg`;
- exact peeled/source overlap identities on `x-I` and `x+I`;
- eventual strict signs on both lines;
- `exists_high_dyadicSharpPrimeImpedance_im_pos` and `_im_neg` above arbitrary height;
- `dyadicSharpPrimeImpedance_not_upperHalfPlaneValued_above`;
- `dyadicSharpPrimeImpedance_not_lowerHalfPlaneValued_above`.

Both modules are imported by their umbrellas.

The closure is strengthened by
`GaloisForLFunctions.RHTower.CCMSharpPrimeWindowMobiusPassiveNoGo`, which excludes every
nondegenerate real Möbius postcomposition, and by
`GaloisForLFunctions.RHTower.CCMSharpPrimeWindowCompletedPassiveTransfer`, which identifies the
canonical completed survivor with the already-existing horizontal Xi-growth response.

## Audit

- `lake env lean GaloisForLFunctions/HTGeometry/DirichletHalfPlaneSignRigidity.lean`: pass.
- `lake env lean GaloisForLFunctions/RHTower/CCMSharpPrimeWindowPassiveNoGo.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPassiveNoGo`: pass.
- final direct check after generic phase selection: pass.
- final focused Route-I build after generic phase selection: pass.
- `lake env lean GaloisForLFunctions/RHTower/CCMSharpPrimeWindowMobiusPassiveNoGo.lean`: pass.
- `lake env lean GaloisForLFunctions/RHTower/CCMSharpPrimeWindowCompletedPassiveTransfer.lean`:
  pass.
- targeted builds for both added Route-I leaf modules: pass.
- formal lint without build initially passed; final repository-wide rerun reports only seven
  unrelated concurrently added RHTower modules missing umbrella reachability.  All Route-I modules
  are reachable and no Route-I lint error is reported.
- `#print axioms` for generic sign/phase theorems, coefficient positivity, high witnesses, and
  both no-go capstones: only `propext`, `Classical.choice`, and `Quot.sound`.
- no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration introduced.

## Route impact

This formalizes the terminal kill condition on Route I's raw passive-impedance producer.  Existing
sharp-window RH criteria and divisor tomography remain valid, but no passive scalar response can
equal the literal source on its initial overlap, and no real Möbius postcomposition repairs it.
The exact completed source candidate collides with retired Route C2.  This exhausts that
transformation branch but does not assign Route I's open arithmetic endpoint to a live route.
