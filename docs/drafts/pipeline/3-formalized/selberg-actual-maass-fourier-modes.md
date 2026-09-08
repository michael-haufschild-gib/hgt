# Actual Fourier-mode equations of congruence Maass eigenforms

- **ID:** SELBERG-ACTUAL-MAASS-FOURIER-MODES
- **Stage:** 3-formalized.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 19.
- **Scope:** Literal normalized Fourier coefficients of the existing principal-congruence Maass cusp eigenform definition.

## Exact result

For a Maass cusp eigenform of level `N+1`, put `w=N+1` and define

`a_n(y)=(1/w)*integral_0^w exp(-2*pi*i*n*x/w)*f(x+iy) dx`.

For every integer `n` and every `y>0`, this actual function has both height derivatives and satisfies

`-y^2*(a_n''(y)-(2*pi*n/w)^2*a_n(y))=lambda*a_n(y)`.

The zero-index coefficient is exactly the earlier unnormalized Maass mean divided by `w`. As height tends to infinity, all coefficients tend to zero uniformly in their integer index. At each fixed positive height there exists a finite nonnegative `M` such that

`(2*pi*n/w)^2*|a_n(y)|<=M`

for every integer `n`.

## Dependency-closed paper proof

Use the actual real C² chart of the source Maass eigenform. On a compact horizontal interval and a small closed positive-height interval, the vertical directional derivative is continuous and bounded. Multiplication by the continuous Fourier kernel retains this domination. Differentiation under the finite integral gives the coefficient of the vertical derivative; repeating this once gives its actual second height derivative.

The congruence translation already proves period `w`. Differentiating that actual periodic equality proves the same period for the first horizontal derivative. The inspected `DeningerFourierCoeffDeriv` integrates by parts against the literal Fourier kernel; its endpoint terms cancel by these periodic equalities. Two applications multiply the coefficient by `(2*pi*i*n/w)^2=-(2*pi*n/w)^2`.

Multiply the defining hyperbolic PDE by the Fourier kernel and integrate. Continuity on the compact horizontal interval supplies all required integrability. Pull out the height and eigenvalue constants, then substitute the two derivative identities. This proves the modal equation without selecting a Bessel solution or postulating a modal ansatz.

The source cusp filter bounds the norm of the eigenform uniformly in horizontal position at every sufficiently large height. The normalized Fourier coefficient norm is at most that same bound, independently of `n`; hence the asserted uniform decay. At fixed positive height, compactness bounds the norm of the actual horizontal second derivative by `M`. Its normalized Fourier coefficients have norm at most `M`. Taking norms in the twice-integrated identity gives the squared-frequency bound.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergMaassFourierModes`, namespace `SelbergMaassFourier`.

Capstones: `coefficient_second_hasDerivAt`, `coefficient_horizontal_second`, `maassCoefficient_modal_equation`, `maassCoefficient_zero`, `maassCoefficient_uniform_decay`, `maassCoefficient_decay`, `maassCoefficient_frequency_square_bound`.

Complete scratch and final direct source checks passed without warnings. Seven coordinate/directional helpers in `SelbergMaassFourierMean` were made public with unchanged proofs; that source passed direct checking and its needed olean was refreshed serially. The targeted final build passed, rebuilding the changed mean dependency and then this module (`/tmp/selberg_maass_fourier_modes_build.log`). Twelve capstone checks in `/tmp/selberg_maass_fourier_modes_axioms.lean`, including the two preserved mean theorems, report only `propext`, `Classical.choice`, and `Quot.sound`. The same audit successfully imports the existing exceptional-mean interface. The module is wired and indexed; whitespace checks passed. Latest repository-wide lint failed on seven unrelated unwired modules, detailed on the parent card; no task module is named. All task-owned Lean/Lake handles finished. No numerical experiment, additional axiom, automorphic lift, or Selberg conclusion is used.

## Next source question

The inverse-square coefficient estimate should imply that the actual trace belongs to the frequency-weighted boundary-form domain constructed in cycle 18. That is a separate next target. The current theorem does not prove Parseval for the tail energy or supply the missing quotient-core coupling.
