# PM separate negative mixed-current budget

- **Status:** failed candidate; positive survivor formalized and audited, 2026-10-04.
- **Route:** PM; the complete signed-energy route is still active.
- **Rejected claim:** the negative part of the literal canonical mixed prime-update current admits an independent subpower bound for all sufficiently small positive damping.
- **Source:** `../1-in-progress/pm-prime-square-coupled-source.md`.

## Obstruction

For every sufficiently small positive epsilon, the actual negative part
`Mminus(8P^2)` is at least `c*(2P)^(2-4*epsilon)/log(2P)^4` eventually.
Its quotient by `(8P^2)^kappa` tends to infinity for every real
`kappa<1-2*epsilon`. This contradicts a separate subpower bound. It does
not contradict RH: the complete mixed current retains its positive part.

## Positive survivor

The actual core and its prime dilate have opposite uniform signs on the
square slab. Their weighted product has negative magnitude at least
`c*P^(3-4*epsilon)/log(P)^3`; the integrated negative mass is at least
`c'*P^(1-4*epsilon)/log(P)^3` per prime. This identifies a concrete,
power-sized term which the complete compensation must retain.

Paper proof: exact rough inversion, square-inclusive semiprime bound,
signed prime-convolution limit, boundary-jet gap and the positive first
band. Integration and prime-shell counting give the escape theorem.
Lean status: all eleven exports in
`PMPowerDampedMobiusNegativePrimeCurrent.lean` pass targeted old leaf
build, final actual-file check and standard-three-axiom audit. Full audit:
`../3-formalized/pm-negative-mixed-prime-current.md`.

## Continued hard target

Retain `Mpositive-Mnegative-Q/2` as one signed object. Its uniform lower
bound, or an adequate complete subpower estimate, remains open. The next
paper target is exact finite-update energy balance and forced positive
compensation at the scale exposed above.
