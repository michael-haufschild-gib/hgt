# Observable rectangular power lower floor gives a horizontal Xi zero-free region

- **ID:** `ccm-observable-power-lower-zero-free-region`
- **Stage:** 3-formalized
- **Type:** THEOREM / QUANTITATIVE RH PREDECESSOR
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/ccm-rectangular-subpower-lower-floor-rh-law.md`

## Statement

Fix `L > 0`, `alpha >= 0`, and an admissible tail threshold `N`.  Suppose the actual rectangular
Weil values satisfy

```text
Re Q_Xi(chi_((log n)/2,L), chi_((log n)/2,L)) >= -C n^alpha
```

for every `n >= N`.  Then every Xi zero `rho` satisfies

```text
re rho <= 1/2 + alpha.                                    (1)
```

Equivalently, `Xi` is zero-free on `re rho > 1/2 + alpha`.

## Positive top-down chain

```text
observable one-sided O(n^alpha) lower loss
  -> bounded rectangular remainder absorption
  -> global positive-transverse carrier power floor
  -> power-corrected local Landau transfer
  -> transverse Xi supremum <= alpha
  -> Xi zero-free on re rho > 1/2 + alpha.                (2)
```

The exponent is retained throughout.  Applying `(1)` for every positive `alpha` gives the already
formalized subpower-lower implication to RH.

## Non-circularity boundary

The theorem does not prove the observable lower floor.  Its continuation and pole analysis use the
actual Xi divisor carrier, so they belong only after an independently derived source estimate.  A
prime--Gamma, Möbius, Sonin, theta, or prolate proof of the lower floor remains the open source
problem.

## Lean certificate

Modules:

- `formal/GaloisForLFunctions/RHTower/CCMRectangularPowerLowerZeroFree.lean`
- `formal/GaloisForLFunctions/RHTower/CCMRectangularObservablePowerLowerZeroFree.lean`

Principal declarations:

- `xiRightTransverseSup_le_of_xiRectangularRightPowerLower`
- `xiRightCenteredZero_re_le_of_xiRectangularRightPowerLower`
- `XiRectangularWeilTailPowerLower`
- `exists_xiRectangularRightPowerLower_of_xiRectangularWeilTailPowerLower`
- `re_I_mul_xiSpectralPoint_le_of_xiRectangularWeilTailPowerLower`
- `xi_zero_re_le_half_add_of_xiRectangularWeilTailPowerLower`
- `xi_ne_zero_of_half_add_alpha_lt_re_of_xiRectangularWeilTailPowerLower`

The exact module builds pass.  The two final zero-region declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] fixed-exponent carrier theorem formalized
- [x] bounded observable remainder absorbed
- [x] every multiplicity copy bounded in centered coordinates
- [x] every Xi zero bounded in literal coordinates
- [x] zero-free half-plane theorem exposed
- [x] exact builds and axiom checks pass
- [ ] derive one source-defined observable subpower lower floor
- [ ] RH
