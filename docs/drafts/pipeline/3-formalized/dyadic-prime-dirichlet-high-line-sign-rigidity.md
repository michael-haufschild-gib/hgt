# Dyadic-prime Dirichlet high-line sign rigidity — Lean formalization

- **ID:** `dyadic-prime-dirichlet-high-line-sign-rigidity`
- **Stage:** `3-formalized`
- **Type:** `[BRIDGE] [NO-GO] [POSITIVE CLASSIFICATION]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:**
  `../2-fully-proven/not_new_scientific_knowledge/dyadic-prime-dirichlet-high-line-sign-rigidity.md`

## Generic module

`GaloisForLFunctions.HTGeometry.DirichletHalfPlaneSignRigidity` provides:

- `lseriesPowerTwistCoeff_abscissa_lt_top`;
- `tendsto_rpow_mul_im_lseriesPeeledPowerTwist`;
- `eventually_lseriesPeeledPowerTwist_im_pos` and `_im_neg`;
- `eventually_LSeriesSummable_sub_const`;
- `lseriesPeeledPowerTwist_im_eq_LSeries_sub`;
- `eventually_realLSeries_sub_im_pos` and `_im_neg`.

The last two theorems formalize arbitrary-first-mode high-line sign rigidity for real ordinary
Dirichlet series.  No continuation or zero hypothesis occurs.

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

## Audit

- `lake env lean GaloisForLFunctions/HTGeometry/DirichletHalfPlaneSignRigidity.lean`: pass.
- `lake env lean GaloisForLFunctions/RHTower/CCMSharpPrimeWindowPassiveNoGo.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.CCMSharpPrimeWindowPassiveNoGo`: pass.
- formal lint without build: pass.
- `#print axioms` for generic sign theorems, coefficient positivity, high witnesses, and both
  no-go capstones: only `propext`, `Classical.choice`, and `Quot.sound`.
- no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration introduced.

## Route impact

This formalizes the terminal kill condition on Route I's passive-impedance producer.  Existing
sharp-window RH criteria and divisor tomography remain valid, but no passive scalar response can
equal the literal source on its initial overlap.  Route I is retired; a transformed passive source
would require a new card and an unconditional inverse handoff.
