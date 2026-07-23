# Kapustin horizontal-multiplicity universality law

Status: paper proof complete; exact `lake env lean` audit passed.

## Lean sources

- `riemannHypothesis_of_kapustin_symmetric_pointSpectrum`
- `xi_zero_re_eq_half_of_RH`
- `xiHorizontalMultiplicity_eq_order_of_RH`
- `xiHorizontalFibersMultiplicityOne_iff_rh_and_orderOne`

## Survivor

Any Hilbert-symmetric operator carrying every Kapustin Xi-divisor eigenvalue forces more than
critical-line location: for every Xi zero, its full exact-height strip-fiber multiplicity equals its
local analytic order. Consequently, under that spectral realization, global horizontal
multiplicity one is equivalent to simplicity of every Xi zero; operator symmetry has discharged
the RH half of the unrestricted characterization.

The strengthened certificate identifies that same integer in four charts: Hilbert spectral
realization, horizontal divisor mass, local loop winding, and every falling-factorial residue of
the normalized derivative tower of the peeled local Xi section.

This is a cross-interface law between the Hilbert--Pólya endpoint and the intrinsic horizontal
divisor census. Neither source states a multiplicity consequence of the Kapustin realization.

## Proof skeleton

Hilbert symmetry makes every carried Kapustin eigenvalue conjugation-fixed. The Kapustin coordinate
then places every Xi divisor point on the critical line, hence RH. At fixed ordinate, all strip zeros
therefore have real part `1/2`; equality of real and imaginary parts collapses the finite fiber to
the chosen zero. The defining fiber sum is its analytic order. Xi peeling produces a nonvanishing
local unit; the argument principle reads the order as winding, while the multiple-zero derivative
law reads its complete falling-factorial fingerprint.

## Novelty audit

Pending post-formalization literature search.
