# Length-dependent floors imply the abscissa law

- **ID:** length-dependent-floors-abscissa-law
- **Stage:** 3-formalized
- **Tasks:** A106
- **Lean:** `SurfaceOfSpecZ/ScaleLocality/LengthDependentFloorsGiveTheAbscissaLaw.lean`

## Statement

Put `F(u)=2 Re lagStructure(ζ,boxSpline 1 3,u)` and `Lₖ=(k+1)π/67`.
Suppose that for every natural `k` there is a real `Kₖ` such that arbitrarily
late intervals `[T,T+Lₖ]` satisfy `F(u)≥−Kₖ`. Then ζ satisfies the asymptotic
abscissa law. The same conclusion holds if the floor is imposed only at
prime logarithms in those intervals.

## Proof

Failure of the abscissa law gives a finite nonempty exceptional zero set.
Its maximum real part has positive depth `b` and a finite nonempty active
top spectrum of size `k`. Half-period deletion gives a negative excursion
of fixed size for `exp(−bu)F(u)` on every sufficiently late interval of
length `Lₖ`. This contradicts a fixed floor there.

For prime samples, choose a longer prescribed interval. Prime-gap transfer
extends its floor to a central real interval with error exponent
`α=max(0,b−1/3)<b`. The same normalized negative excursions contradict
every floor `−M exp(αu)`.

## Formalization

Namespace `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`:

- `exists_finite_top_of_not_abscissaLaw`
- `zeta_finite_top_breaks_exponential_floor`
- `asymptoticAbscissaLaw_of_lengthDependent_floors`
- `asymptoticAbscissaLaw_of_lengthDependent_prime_floors`

Direct Lean check passed. Imported by `SurfaceOfSpecZ.lean`.
