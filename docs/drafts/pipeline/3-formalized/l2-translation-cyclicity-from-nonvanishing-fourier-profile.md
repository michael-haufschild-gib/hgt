# L2 translation cyclicity from a nonvanishing Fourier profile

- **ID:** l2-translation-cyclicity-from-nonvanishing-fourier-profile
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II; topology of genuine Poisson boundaries.
- **Statement:** A complex L2 function on the real line whose Fourier transform is nonzero almost everywhere has dense complex span of its real translates.

## Proof

First consider the character orbit of an almost-everywhere nonzero L2 vector f.
Represent an annihilating continuous functional by inner product against g.
The function conjugate(g)f is integrable by Cauchy–Schwarz. Annihilation says
all its Fourier integrals vanish, so Fourier uniqueness makes it zero almost
everywhere. Nonvanishing of f forces g=0. Hilbert duality then gives density.
The unitary Fourier transform carries translations into character
multiplication and proves the asserted translation criterion.

No lower bound on the Fourier profile is required. The analytic criterion is
standard; the new intended application is density of actual Meyer Poisson
boundaries in origin L2, recorded on its separate card.

## Lean certificate

Module: `HTGeometry/L2TranslationCyclicity.lean`.

- `isCyclicFamily_fourierPhase_of_ae_ne_zero`
- `isCyclicFamily_translation_of_fourier_ae_ne_zero`

Actual-file `lake --old env lean` check passed. Both endpoint transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary prints removed; HTGeometry umbrella wired.
